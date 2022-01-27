// We'll just hack it all together in one file for now
extern crate nom;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::collections::HashMap;
use std::str::{from_utf8};
use nom::{IResult,Finish};
use nom::bytes::complete::{tag,is_not};
use nom::branch::{alt};
use nom::character::complete::{digit1,alpha1,multispace1, multispace0,alphanumeric1, none_of};
use nom::sequence::{tuple,pair};
use nom::combinator::{recognize,all_consuming};
use nom::multi::{many0,many1,separated_list1,separated_list0};

// We will model an architecture where code and data live in separate address spaces
// We don't need to have a global pointer because those actually get flattened into memory
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum VirtualVal<'a> {
    Data { val: u64 },
    CodePtr { val: &'a str }
}
impl <'a> fmt::Display for VirtualVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            VirtualVal::Data { val } => write!(f, "{}", val),
            VirtualVal::CodePtr { val } => write!(f, "{}", val)
        }
    }
}


#[derive(Debug,PartialEq)]
pub enum Reason {
    NotAPointer,
    NotANumber,
    NoSuchField,
    NoSuchMethod,
}
#[derive(Debug,PartialEq)]
pub enum IRExpr<'a> {
    IntLit { val: u32 },
    GlobalRef { name: &'a str },
    Var { id: &'a str },
    BlockRef { bname: &'a str },
}
// Adapted from nom recipes
pub fn identifier(input: &[u8]) -> IResult<&[u8], &str> {
    recognize(
      pair(
        alt((alpha1, tag("_"))),
        many0(alt((alphanumeric1, tag("_"))))
      )
    )(input).map(|(rest,m)| (rest,from_utf8(m).unwrap()))
  }
pub fn parse_op(i: &[u8]) -> IResult<&[u8], &str> {
    alt((
        tag("<<"),
        tag(">>"),
        tag("+"),
        tag("-"),
        tag("*"),
        tag("/"),
        tag("|"),
        tag("&"),
        tag("^")
    ))(i).map(|(rest,op)| (rest, from_utf8(op).unwrap()))
}
pub fn parse_register_name(i: &[u8]) -> IResult<&[u8], &str> {
    alphanumeric1(i).map(|(rest,id)| (rest, from_utf8(id).unwrap()))
}
pub fn parse_ir_expr(i: &[u8]) -> IResult<&[u8], IRExpr> {
    let (i,_) = multispace0(i)?;
    alt((
        |i| tuple((tag("@"),identifier))(i).map(|(rest,(_,id))| (rest,IRExpr::GlobalRef { name : id })),
        |i| tuple((tag("%"),parse_register_name))(i).map(|(rest,(_,id))| (rest,IRExpr::Var { id: id })),
        |i| identifier(i).map(|(rest,id)| (rest,IRExpr::BlockRef { bname: id })),
        |i| digit1(i).map(|(rest,n)| (rest,IRExpr::IntLit { val: from_utf8(n).unwrap().parse::<u32>().unwrap() }))
    ))(i)
}
#[cfg(test)]
mod TestParseIRExpr {
    use crate::*;
    #[test]
    fn check_ir_txpr() {
        let empty : &[u8] = b"";
        assert_eq!(parse_ir_expr("%v3".as_bytes()), Ok((empty, IRExpr::Var { id : "v3" })));
        assert_eq!(parse_ir_expr("%3".as_bytes()), Ok((empty, IRExpr::Var { id : "3" })));
        assert_eq!(parse_ir_expr("%asdf".as_bytes()), Ok((empty, IRExpr::Var { id : "asdf" })));
        assert_eq!(parse_ir_expr("@v3".as_bytes()), Ok((empty, IRExpr::GlobalRef { name : "v3" })));
        assert_eq!(parse_ir_expr("@asdf".as_bytes()), Ok((empty, IRExpr::GlobalRef { name : "asdf" })));
        assert_eq!(parse_ir_expr("v3".as_bytes()), Ok((empty, IRExpr::BlockRef { bname : "v3" })));
        assert_eq!(parse_ir_expr("asdf".as_bytes()), Ok((empty, IRExpr::BlockRef { bname : "asdf" })));
        assert_eq!(parse_ir_expr("3".as_bytes()), Ok((empty, IRExpr::IntLit { val : 3 })));
        assert_eq!(parse_ir_expr("2342342".as_bytes()), Ok((empty, IRExpr::IntLit { val : 2342342 })));
        assert_eq!(parse_ir_expr("23432241".as_bytes()), Ok((empty, IRExpr::IntLit { val : 23432241 })));
    }
}

#[derive(Debug,PartialEq)]
pub enum Prim<'a> {
    VarAssign { lhs: &'a str, rhs: IRExpr<'a> },
    Op { lhs: &'a str, arg1: IRExpr<'a>, op: &'a str, arg2: IRExpr<'a> },
    Call { lhs: &'a str, code: IRExpr<'a>, receiver: IRExpr<'a>, args: Vec<IRExpr<'a>> },
    Phi { lhs: &'a str, opts: Vec<(&'a str, IRExpr<'a>)> },
    Alloc { lhs: &'a str, slots: u32 },
    Print { out: IRExpr<'a> },
    GetElt { lhs: &'a str, base: IRExpr<'a>, offset: IRExpr<'a> },
    SetElt { base: IRExpr<'a>, offset: IRExpr<'a>, val: IRExpr<'a> },
    Load { lhs: &'a str, base: IRExpr<'a> },
    Store { base: IRExpr<'a>, val: IRExpr<'a> }
}
pub fn parse_reason(i: &[u8]) -> IResult<&[u8], Reason> {
    let (i,_) = multispace0(i)?;
    alt((
        |i| tag("NotAPointer")(i).map(|(rest,_)| (rest, Reason::NotAPointer)),
        |i| tag("NotANumber")(i).map(|(rest,_)| (rest, Reason::NotANumber)),
        |i| tag("NoSuchMethod")(i).map(|(rest,_)| (rest, Reason::NoSuchMethod)),
        |i| tag("NoSuchField")(i).map(|(rest,_)| (rest, Reason::NoSuchField))
    ))(i)
}
pub fn parse_arg_list(i: &[u8]) -> IResult<&[u8], Vec<IRExpr>> {
    alt((|i| tuple((tag(","),multispace0,separated_list0(tuple((multispace0,tag(","),multispace0)),parse_ir_expr),multispace0,tag(")")))(i).map(|(rest,(_,_,v,_,_))| (rest,v) ),
         |i| tag(")")(i).map(|(rest,_)| (rest, Vec::new()))
    ))(i)
}

#[cfg(test)]
mod test_parse_arg_List {
    use crate::*;
    #[test]
    fn check_args() {
        let empty : &[u8] = b"";
        assert_eq!(parse_arg_list(")".as_bytes()), Ok((empty, vec![])));
        assert_eq!(parse_arg_list(", 3)".as_bytes()), Ok((empty, vec![IRExpr::IntLit {val:3}])));
        assert_eq!(parse_arg_list(", %v3, 3)".as_bytes()), Ok((empty, vec![IRExpr::Var { id: "v3"}, IRExpr::IntLit {val:3}])));
        assert_eq!(parse_arg_list(", %3, 3)".as_bytes()), Ok((empty, vec![IRExpr::Var { id: "3"}, IRExpr::IntLit {val:3}])));
        assert_eq!(
            parse_arg_list(", %v3 , 3 )".as_bytes()).map(|(rest,r)| (from_utf8(rest).unwrap(),r)), 
            Ok(("", vec![IRExpr::Var { id: "v3"}, IRExpr::IntLit {val:3}])));
    }
}


pub fn parse_phi_arg_list(i: &[u8]) -> IResult<&[u8], Vec<(&str,IRExpr)>> {
    alt((|i| tuple((separated_list1(tuple((multispace0,tag(","),multispace0)),
                                    |x| tuple((identifier,tuple((multispace0,tag(","),multispace0)),parse_ir_expr))(x).map(|(rest,(i,_,e))| (rest,(i,e)))
                                ),multispace0,tag(")")))(i).map(|(rest,(v,_,_))| (rest,v) ),
         |i| tag(")")(i).map(|(rest,_)| (rest, Vec::new()))
    ))(i)
}
#[cfg(test)]
mod test_parse_phi_arg_list {
    use crate::*;
    #[test]
    fn check_phi_args() {
        let empty : &[u8] = b"";
        assert_eq!(parse_phi_arg_list(")".as_bytes()), Ok((empty, vec![])));
        assert_eq!(parse_phi_arg_list("blah, 3)".as_bytes()), Ok((empty, vec![("blah",IRExpr::IntLit {val:3})])));
        assert_eq!(parse_phi_arg_list("blah, 3, asdf, %v3)".as_bytes()), Ok((empty, vec![("blah",IRExpr::IntLit {val:3}), ("asdf",IRExpr::Var {id:"v3"})])));
        assert_eq!(parse_phi_arg_list("blah ,  3 )".as_bytes()), Ok((empty, vec![("blah",IRExpr::IntLit {val:3})])));
        assert_eq!(parse_phi_arg_list("blah ,  3  ,   asdf , %v3  )".as_bytes()), Ok((empty, vec![("blah",IRExpr::IntLit {val:3}), ("asdf",IRExpr::Var {id:"v3"})])));

        assert_eq!(parse_phi_arg_list("bb1,%q,bb3,5)".as_bytes()), 
                   Ok((empty, vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})])));
        assert_eq!(parse_phi_arg_list("bb1 , %q , bb3 , 5 )".as_bytes()), 
                   Ok((empty, vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})])));
    }
}

pub fn parse_full_arg_list(i: &[u8]) -> IResult<&[u8], Vec<IRExpr>> {
    tuple((multispace0,separated_list0(tuple((multispace0,tag(","),multispace0)),parse_ir_expr),multispace0,tag("}")))(i).map(|(rest,(_,v,_,_))| (rest,v) )
}
pub fn parse_ir_statement(i: &[u8]) -> IResult<&[u8], Prim> {
    // TODO: Very sensitive to ordering. Should reject input that results in parsing a blockname phi or alloc
    let (i,_) = multispace0(i)?;
    alt((
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("phi("),multispace0,parse_phi_arg_list))(i).map(|(rest,(_,l,_,_,_,_,_,a1))| (rest,Prim::Phi { lhs: l, opts: a1 })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("load("),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,l,_,_,_,_,_,a1,_,_))| (rest,Prim::Load { lhs: l, base: a1 })),
        |i| tuple((tag("store("),multispace0,parse_ir_expr,multispace0,tag(","),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,_,base,_,_,_,v,_,_))| (rest,Prim::Store { base: base , val: v })),
        |i| tuple((tag("setelt("),multispace0,parse_ir_expr,multispace0,tag(","),multispace0,parse_ir_expr,multispace0,tag(","),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,_,base,_,_,_,off,_,_,_,v,_,_))| (rest,Prim::SetElt { base: base, offset: off, val: v })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("getelt("),multispace0,parse_ir_expr,multispace0,tag(","),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,lhs,_,_,_,_,_,base,_,_,_,off,_,_))| (rest,Prim::GetElt { lhs: lhs, base: base, offset: off })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("load("),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,l,_,_,_,_,_,a1,_,_))| (rest,Prim::Load { lhs: l, base: a1 })),
        |i| tuple((tag("%"),
                   parse_register_name,
                   tuple((multispace1,tag("="),multispace1)),
                   tag("call("),
                   parse_ir_expr,
                   tuple((multispace0,tag(","),multispace0)),
                   parse_ir_expr,
                   multispace0,
                   parse_arg_list, // TODO: check handling of that first comma before the varargs part
            ))(i).map(|(rest,(_,l,_,_,cd,_,rcv,_,args))| (rest,Prim::Call { lhs: l, code: cd, receiver: rcv, args: args })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("alloc("),digit1,tag(")")))(i).map(
            |(rest,(_,l,_,_,_,_,d,_))| (rest,Prim::Alloc { lhs: l, slots: from_utf8(d).unwrap().parse::<u32>().unwrap() })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,parse_ir_expr,multispace1,parse_op,multispace1,parse_ir_expr))(i).map(|(rest,(_,l,_,_,_,a1,_,o,_,a2))| (rest,Prim::Op { lhs: l, arg1: a1, op: o, arg2: a2 })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,parse_ir_expr))(i).map(|(rest,(_,l,_,_,_,a1))| (rest,Prim::VarAssign { lhs: l, rhs: a1 })),
        // print
        |i| tuple((tag("print("),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,_,e,_,_))| (rest, Prim::Print { out: e}))
    ))(i)
}
pub fn parse_ir_statements(i: &[u8]) -> IResult<&[u8], Vec<Prim>> {
    // This needs to eat trailing whitespace as well, but tuple((multispace0,tag("\n"))) seems to stick the \n into the whitespace....
    separated_list0(tag("\n"),//tuple((multispace0,tag("\n"))), 
        parse_ir_statement
        //|x|tuple((parse_ir_statement, 
        //          alt((|y| multispace0(y).map(|(r,_)| (r,())), |y| tuple((multispace0, tag("#"), (is_not("\n")) ))(y).map(|(r,_)| (r,())) )) 
        //    ))(x).map(|(rest,(ss,_))| (rest,ss))
    )(i)
}
#[cfg(test)]
mod test_parse_ir_statement {
    use crate::*;
    #[test]
    fn check_statements() {
        let empty : &[u8] = b"";
        assert_eq!(parse_ir_statement("print(3)".as_bytes()), Ok((empty, Prim::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("print( 3 )".as_bytes()), Ok((empty, Prim::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("print(\t3 )".as_bytes()), Ok((empty, Prim::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("\t\tprint( 3 )".as_bytes()), Ok((empty, Prim::Print { out: IRExpr::IntLit { val : 3}})));

        assert_eq!(parse_ir_statement("%v = 3".as_bytes()), Ok((empty, Prim::VarAssign { lhs: "v", rhs: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("  %v  =   3".as_bytes()), Ok((empty, Prim::VarAssign { lhs: "v", rhs: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("%1 = 10".as_bytes()), Ok((empty, Prim::VarAssign { lhs: "1", rhs: IRExpr::IntLit { val : 10}})));

        assert_eq!(parse_ir_statement("%1 = call(%code, %recv, %arg1, %arg2)".as_bytes()),
            Ok((empty, Prim::Call { lhs: "1", code: IRExpr::Var { id: "code" }, receiver: IRExpr::Var { id: "recv"}, args: vec![
                IRExpr::Var { id: "arg1" },
                IRExpr::Var { id: "arg2" },
            ]}))
        );

        assert_eq!(parse_ir_statement("%1 = load(%4)".as_bytes()), Ok((empty, Prim::Load { lhs: "1", base: IRExpr::Var { id : "4"}})));
        assert_eq!(parse_ir_statement("%3 = load(%2)".as_bytes()), Ok((empty, Prim::Load { lhs: "3", base: IRExpr::Var { id : "2"}})));
        assert_eq!(parse_ir_statement("  %3  =  load( %2 )".as_bytes()), Ok((empty, Prim::Load { lhs: "3", base: IRExpr::Var { id : "2"}})));

        assert_eq!(parse_ir_statement("%v = phi(bb1,%q,bb3,5)".as_bytes()), 
                   Ok((empty, Prim::Phi { lhs: "v", opts: vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})]})));
        assert_eq!(parse_ir_statement("  %v  =   phi( bb1 , %q , bb3 , 5 )".as_bytes()), 
                   Ok((empty, Prim::Phi { lhs: "v", opts: vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})]})));

        assert_eq!(parse_ir_statement("%v = 3 + 4".as_bytes()), Ok((empty, Prim::Op { lhs: "v", arg1: IRExpr::IntLit { val : 3}, op: "+", arg2: IRExpr::IntLit { val:4}})));
        assert_eq!(parse_ir_statement("\t %v   =  %q   * 4".as_bytes()), Ok((empty, Prim::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}})));


        assert_eq!(parse_ir_statements("\t %v   =  %q   * 4\nprint( %v )".as_bytes()), 
            Ok((empty, vec![Prim::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}},
                            Prim::Print { out: IRExpr::Var { id: "v"}}
            ])));
        assert_eq!(parse_ir_statements("\t %v   =  %q   * 4     \nprint( %v )".as_bytes()), 
            Ok((empty, vec![Prim::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}},
                            Prim::Print { out: IRExpr::Var { id: "v"}}
            ])));
    }
}

#[derive(Debug,PartialEq)]
pub enum ControlXfer<'a> {
    Jump { block: &'a str },
    If { cond: IRExpr<'a>, tblock: &'a str, fblock: &'a str },
    Ret { val: IRExpr<'a> },
    Fail { reason: Reason }
}
pub fn parse_control(i: &[u8]) -> IResult<&[u8], ControlXfer> {
    let (i,_) = multispace0(i)?;
    alt((
        |i| tuple((tag("jump"),multispace1,identifier))(i).map(|(rest,(_,_,n))| (rest,ControlXfer::Jump { block: n})),
        |i| tuple((tag("if"),multispace1,parse_ir_expr,multispace1,tag("then"),multispace1,identifier,multispace1,tag("else"),multispace1,identifier))(i).map(|(rest,(_,_,b,_,_,_,t,_,_,_,f))| (rest,ControlXfer::If { cond: b, tblock: t, fblock: f})),
        |i| tuple((tag("ret"),multispace1,parse_ir_expr))(i).map(|(rest,(_,_,n))| (rest,ControlXfer::Ret { val: n})),
        |i| tuple((tag("fail"),multispace1,parse_reason))(i).map(|(rest,(_,_,r))| (rest, ControlXfer::Fail { reason: r}))
    ))(i)
}
#[cfg(test)]
mod TestParseControl {
    use crate::*;
    #[test]
    fn checkControl() {
        let empty : &[u8] = b"";
        assert_eq!(parse_control("\tjump loophead".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, ControlXfer::Jump { block: "loophead" })));
        assert_eq!(parse_control("\tret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, ControlXfer::Ret { val: IRExpr::IntLit { val: 0 } })));
    }
}

#[derive(Debug,PartialEq)]
pub struct BasicBlock<'a> {
    name: &'a str,
    formals: Vec<&'a str>,
    instrs: Vec<Prim<'a>>,
    next: ControlXfer<'a>
}

// They're not really supposed to have leading %s, but I shipped some demo code that did it, so let's accept it.
pub fn parse_block_arg(i: &[u8]) -> IResult<&[u8], &str> {
    alt((
        identifier,
        |x| tuple((tag("%"),identifier))(x).map(|(rst,(_,id))| (rst,(id)))
    ))(i)
}
pub fn parse_opt_block_arg_list(i: &[u8]) -> IResult<&[u8], Vec<&str>> {
    alt((
        |x| tag(":\n")(x).map(|(rest,_)| (rest, vec![])),
        |x| tuple((tag("("), multispace0, separated_list0(tuple((multispace0,tag(","),multispace0)),parse_block_arg), multispace0, tag("):\n")))(x).map(|(rest,(_,_,args,_,_))| (rest,args))
    ))(i)
}
pub fn parse_basic_block(i: &[u8]) -> IResult<&[u8], BasicBlock> {
    let (i,_) = multispace0(i)?;
    tuple((
        identifier, parse_opt_block_arg_list, parse_ir_statements, parse_control
    ))(i).map(|(rest,(name,formals,prims,ctrl))| (rest,BasicBlock { name: name, instrs: prims, next: ctrl, formals: formals}))
}
#[cfg(test)]
mod TestParseBB {
    use crate::*;
    #[test]
    fn checkBB() {
        let empty : &[u8] = b"";
        assert_eq!(parse_basic_block("main:\n\t%1 = 10\nret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, BasicBlock {
                        name: "main",
                        formals: vec![],
                instrs: vec![Prim::VarAssign { lhs: "1", rhs: IRExpr::IntLit { val : 10}}],
                next: ControlXfer::Ret { val: IRExpr::IntLit { val:0 } }
            })));
        assert_eq!(parse_basic_block("mB(this):\n\tret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, BasicBlock {
                        name: "mB",
                        formals: vec![],
                instrs: vec![],
                next: ControlXfer::Ret { val: IRExpr::IntLit { val:0 } }
            })));
    }
}

#[derive(Debug,PartialEq)]
pub enum GlobalStatic<'a> {
    Array { name: &'a str, vals: Vec<VirtualVal<'a>> }
}
pub fn parse_id_list(i: &[u8]) -> IResult<&[u8], Vec<&str>> {
    separated_list0(tuple((multispace0,tag(","),multispace0)), identifier)(i)
}

pub fn parse_array_elt(i: &[u8]) -> IResult<&[u8], VirtualVal> {
    alt((
        |i| identifier(i).map(|(rest,x)| (rest,VirtualVal::CodePtr { val: x })),
        |i| digit1(i).map(|(rest,x)| (rest,VirtualVal::Data { val: from_utf8(x).unwrap().parse::<u64>().unwrap() }))
    ))(i)
}
pub fn parse_array_body(i: &[u8]) -> IResult<&[u8], Vec<VirtualVal>> {
    tuple((multispace0,separated_list0(tuple((multispace0,tag(","),multispace0)),parse_array_elt),multispace0,tag("}")))(i).map(|(rest,(_,v,_,_))| (rest,v) )
}
pub fn parse_global(i: &[u8]) -> IResult<&[u8], GlobalStatic> {
    tuple((
        tuple((multispace0,tag("global"), multispace1, tag("array"), multispace0)),
        identifier,
        tuple((multispace0,tag(":"), multispace0, tag("{"))),
        parse_array_body,
        multispace0
    ))(i).map(|(rest,(_,name,_,vs,_))| (rest,GlobalStatic::Array {name: name, vals: vs}))
}
#[cfg(test)]
mod TestParseGlobal {
    use crate::*;
    #[test]
    fn check_global() {
        let empty : &[u8] = b"";
        assert_eq!(parse_global("global array vtblA: { mA }\n".as_bytes()),
            Ok((empty, GlobalStatic::Array { name: "vtblA", vals: vec![VirtualVal::CodePtr{val:"mA"}]})));
    }
}

#[derive(Debug,PartialEq)]
pub struct IRProgram<'a> {
    Globals: Vec<GlobalStatic<'a>>,
    Blocks: HashMap<&'a str, BasicBlock<'a>>
}


pub fn parse_program(i: &[u8]) -> IResult<&[u8], IRProgram> {
    let (rst,_) = tuple((multispace0,tag("data:\n")))(i)?;
    let mut globals = vec![];
    let mut last_global_parse = parse_global(rst);
    //print!("Initial global parse {:?}", last_global_parse);
    while let Ok((remaining,g)) = last_global_parse {
        //print!("Parsed {:?}", g);
        //print!("Global remaining = {}", from_utf8(remaining).unwrap());
        globals.push(g);
        last_global_parse = parse_global(remaining);
    }
    match last_global_parse.finish() {
        Err(nom::error::Error{ input: postglobals, code: _}) => {
            // TODO: figure out what happens with 
            let (rst2,_) = tuple((multispace0,tag("code:\n")))(postglobals)?;
            let mut last_block_parse = parse_basic_block(rst2);
            let mut blocks = vec![];
            while let Ok((remaining2,b)) = last_block_parse {
                //println!("Parsed basic block:\n{:?}", &b);
                //println!("remaining text: {:?}", from_utf8(remaining2).unwrap());
                blocks.push(b);
                last_block_parse = parse_basic_block(remaining2);
                //println!("last_block_parse={:?}", &last_block_parse);
            }
            //println!("last_block_parse={:?}", &last_block_parse);
            match last_block_parse.finish() {
                Err(nom::error::Error{ input: postcode, code: _}) => {
                    //println!("postcode={}", from_utf8(postcode).unwrap());
                    let tail = all_consuming::<_,_,nom::error::Error<&[u8]>,_>(multispace0)(postcode).finish();
                    match tail {
                        Ok(_) => {
                            let mut bs = HashMap::new();
                            while let Some(b) = blocks.pop() {
                                bs.insert(b.name, b);
                            }
                            Ok(("".as_bytes(), IRProgram { Globals: globals, Blocks: bs}))
                        },
                        Err(nom::error::Error { input: x, code: _}) => {
                            panic!("Leftover text after last parsed block: {}", from_utf8(x).unwrap())
                        }
                    }
                },
                _ => panic!("shouldn't hit this")
            }
            // TODO: "finish" to make sure we didn't just stop on a malformed block
        },
        _ => panic!("This should be impossible"),
    }
}




#[derive(Debug,PartialEq)]
pub enum RuntimeError<'a> {
    NYI,
    BadCallArity,
    CallingNonCode,
    WriteToImmutableData,
    NullPointer,
    UnalignedAccess,
    UnallocatedAddress,
    UninitializedVariable { name: &'a str },
    MissingMain,
    UndefinedVariable,
    UndefinedGlobal,
    CodeAddressArithmetic { bname: &'a str },
    AccessingCodeInMemory { bname: &'a str },
    InvalidBlock { bname: &'a str },
    PhiInFirstBlock,
    BadPhiPredecessor { instr: &'a Prim<'a>, actual_predecessor: &'a str }
}


// Memory is a map from u64 to u64. Lookup will fail for unaligned accesses for now
type Memory<'a> = HashMap<u64,VirtualVal<'a>>;
type Locals<'a> = HashMap<&'a str, VirtualVal<'a>>;
type Globals<'a> = HashMap<&'a str, u64>;
fn mem_lookup<'a>(m:&Memory<'a>, addr:u64) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    if addr == 0 {
        Err(RuntimeError::NullPointer)
    } else if addr % 8 == 0 {
        match m.get(&addr) {
            None => Err(RuntimeError::UnallocatedAddress),
            Some(&v) => Ok(v)
        }
    } else {
        Err(RuntimeError::UnalignedAccess)
    }
}
fn mem_store<'a>(m:&mut Memory<'a>, first_writable:u64, addr:u64, val:VirtualVal<'a>) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    if addr == 0 {
        Err(RuntimeError::NullPointer)
    } else if addr < first_writable {
        Err(RuntimeError::WriteToImmutableData)
    } else if addr % 8 == 0 {
        match m.get(&addr) {
            None => Err(RuntimeError::UnallocatedAddress),
            Some(_) => { Ok(m.insert(addr, val).unwrap()) }
        }
    } else {
        Err(RuntimeError::UnalignedAccess)
    }
}
fn read_var<'a>(l:&Locals<'a>, v:&'a str) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    match l.get(v) {
        Some(&x) => Ok(x),
        None => Err(RuntimeError::UninitializedVariable { name : v})
    }
}
fn set_var<'a>(l:&mut Locals<'a>, x:&'a str, val:VirtualVal<'a>) -> Result<(),RuntimeError<'a>> {
    l.insert(x, val);
    Ok(())
}


fn init_memory<'a>(prog: &'a IRProgram) -> (u64,Memory<'a>,Globals<'a>) {
    let mut next_free : u64 = 0x32;
    let mut m : Memory = HashMap::new();
    let mut globs : Globals = HashMap::new();

    for g in prog.Globals.iter() {
        let GlobalStatic::Array { name: n, vals: vs } = g;
        globs.insert(n, next_free);
        for v in vs.iter() {
            m.insert(next_free, v.clone());
            next_free = next_free + 1;
        }
    }

    (next_free,m,globs)
}

fn expr_val<'a>(l:&Locals<'a>, globs:&Globals<'a>, prog:&IRProgram<'a>, e:&IRExpr<'a>) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    // TODO need globals and program to detect invalid block and global references,
    // and to map global names to locations
    match e {
        IRExpr::IntLit { val: v } => Ok(VirtualVal::Data { val: u64::from(*v) }),
        IRExpr::Var { id: n } => read_var(l, n),
        IRExpr::BlockRef { bname: b } =>
            match prog.Blocks.get(b) {
                None => Err(RuntimeError::UndefinedGlobal),
                Some(_) => Ok(VirtualVal::CodePtr { val: b } )
            },
        IRExpr::GlobalRef { name: n } => { 
            match globs.get(n) {
                None => Err(RuntimeError::UndefinedGlobal),
                Some(v) => Ok(VirtualVal::Data { val: v.clone()} )
            }
        },
    }
}

// Run one basic block to completion. We abuse the Rust stack to encode the target code stack.
fn run_code<'a>(prog: &'a IRProgram<'a>, 
                mut cur_block: &'a BasicBlock<'a>, 
                mut locs: Locals<'a>, 
                globs: &mut Globals<'a>,
                next_alloc: &mut u64,
                mut_mem_start: u64,
                m: &mut Memory<'a>
            ) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    // on entry no previous block
    let mut prevblock : Option<&'a str> = None;
    let mut finalresult = None;
    while let None = finalresult {
        for i in cur_block.instrs.iter() {
            let step =
            match i {
                Prim::Print { out: e } => {
                    let v = expr_val(&locs, &globs, &prog, &e)?;
                    println!("{}",v);
                    Ok(())
                },
                Prim::Alloc { lhs: v, slots: n } => {
                    // reserve n addresses at 8-byte offsets from next alloc
                    *next_alloc = *next_alloc + 8; // Skip 8 bytes to catch some memory errors
                    let result = *next_alloc;
                    let mut allocd = 0;
                    while allocd < *n {
                        mem_store(m, mut_mem_start, *next_alloc, VirtualVal::Data { val: 0 })?;
                        *next_alloc = *next_alloc + 8;
                    }
                    set_var(&mut locs, v, VirtualVal::Data { val: result })
                },
                Prim::VarAssign { lhs: var, rhs: e } => {
                    let v = expr_val(&locs, &globs, &prog, &e)?;
                    set_var(&mut locs, var, v)
                },
                Prim::Phi { lhs: dest, opts } => {
                    if prevblock.is_none() {
                        return Err(RuntimeError::PhiInFirstBlock);
                    }
                    let pred = prevblock.unwrap();
                    let mut done = false;
                    for (bname,src) in opts {
                        if pred.eq(*bname) {
                            let v = expr_val(&locs, &globs, &prog, &src)?;
                            set_var(&mut locs, &dest, v)?;
                            done = true;
                            break;
                        }
                    }
                    if done {
                        Ok(())
                    } else {
                        Err(RuntimeError::BadPhiPredecessor { instr: i, actual_predecessor: pred })
                    }
                },
                Prim::Call { lhs: dest, code, receiver: rec, args } => {
                    let mut calleevars = HashMap::new();
                    let vcode = expr_val(&locs, &globs, &prog, &code)?;
                    let target_block_name = match vcode {
                        VirtualVal::CodePtr { val: b } => Ok(b),
                        VirtualVal::Data { .. } => Err(RuntimeError::CallingNonCode)
                    }?;
                    let target_block = match prog.Blocks.get(target_block_name) {
                        Some(b) => Ok(b),
                        None => Err(RuntimeError::InvalidBlock { bname: target_block_name })
                    }?;
                    let vrec = expr_val(&locs, &globs, &prog, &rec)?;
                    set_var(&mut calleevars, target_block.formals[0], vrec)?;
                    if args.len() + 1 != target_block.formals.len() {
                        return Err(RuntimeError::BadCallArity);
                    }
                    // args are in left-to-right order. Receiver is idx 0.
                    let mut argidx = 1;
                    for arg in args.iter() {
                        let varg = expr_val(&locs, &globs, &prog, &arg)?;
                        set_var(&mut calleevars, target_block.formals[argidx], varg)?;
                        argidx = argidx + 1;
                    }
                    let callresult = run_code(prog, target_block, calleevars, globs, next_alloc, mut_mem_start, m)?;
                    set_var(&mut locs, dest, callresult)
                },
                Prim::SetElt { base, offset: off, val: v } => {
                    let vbase = expr_val(&locs, &globs, &prog, &base)?;
                    let offv = expr_val(&locs, &globs, &prog, &off)?;
                    let v = expr_val(&locs, &globs, &prog, &v)?;
                    match vbase {
                        VirtualVal::CodePtr { val: b } => Err(RuntimeError::AccessingCodeInMemory { bname: b }),
                        VirtualVal::Data { val: n } => 
                            match offv {
                                // TODO: should be different error
                                VirtualVal::CodePtr { val: offb } => Err(RuntimeError::AccessingCodeInMemory { bname: offb }),
                                VirtualVal::Data { val: offset } => mem_store(m, mut_mem_start, n+(8*offset), v).map(|_| ())
                            }
                    }
                },
                Prim::GetElt { lhs: dest, base: e, offset: off } => {
                    let v = expr_val(&locs, &globs, &prog, &e)?;
                    let offv = expr_val(&locs, &globs, &prog, &off)?;
                    match v {
                        VirtualVal::CodePtr { val: b } => Err(RuntimeError::AccessingCodeInMemory { bname: b }),
                        VirtualVal::Data { val: n } => 
                            match offv {
                                // TODO: should be different error
                                VirtualVal::CodePtr { val: offb } => Err(RuntimeError::AccessingCodeInMemory { bname: offb }),
                                VirtualVal::Data { val: offset } => {
                                    let mval = mem_lookup(&m, n+(8*offset))?;
                                    set_var(&mut locs, dest, mval)
                                }
                            }
                    }
                },
                Prim::Load { lhs: dest, base: e } => {
                    let v = expr_val(&locs, &globs, &prog, &e)?;
                    match v {
                        VirtualVal::CodePtr { val: b } => Err(RuntimeError::AccessingCodeInMemory { bname: b }),
                        VirtualVal::Data { val: n } => {
                            let memval = mem_lookup(&m, n)?;
                            set_var(&mut locs, dest, memval)
                        }
                    }
                },
                Prim::Store { base: e, val: ve } => {
                    let bv = expr_val(&locs, &globs, &prog, &e)?;
                    let vv = expr_val(&locs, &globs, &prog, &ve)?;
                    match bv {
                        VirtualVal::CodePtr { val: b } => Err(RuntimeError::AccessingCodeInMemory { bname: b }),
                        VirtualVal::Data { val: n } => {
                            mem_store(m, mut_mem_start, n, vv).map(|_| ())
                        }
                    }
                },
                Prim::Op { lhs: v, arg1: e1, op: o, arg2: e2} => {
                    let v1 = expr_val(&locs, &globs, &prog, &e1)?;
                    let v2 = expr_val(&locs, &globs, &prog, &e2)?;
                    match (v1,v2) {
                        (VirtualVal::CodePtr{ val: b },_) => Err(RuntimeError::CodeAddressArithmetic { bname: b}),
                        (_,VirtualVal::CodePtr{ val: b }) => Err(RuntimeError::CodeAddressArithmetic { bname: b}),
                        (VirtualVal::Data { val: n1 }, VirtualVal::Data { val: n2 }) => 
                            // We've ruled out computing with code addresses, which we don't plan to allow
                            match *o {
                                "+" => set_var(&mut locs, v, VirtualVal::Data { val: n1+n2 }),
                                "<<" => set_var(&mut locs, v, VirtualVal::Data { val: n1<<n2 }),
                                ">>" => set_var(&mut locs, v, VirtualVal::Data { val: n1>>n2 }),
                                "-" => set_var(&mut locs, v, VirtualVal::Data { val: n1-n2 }),
                                "/" => set_var(&mut locs, v, VirtualVal::Data { val: n1/n2 }),
                                "*" => set_var(&mut locs, v, VirtualVal::Data { val: n1*n2 }),
                                "&" => set_var(&mut locs, v, VirtualVal::Data { val: n1&n2 }),
                                "|" => set_var(&mut locs, v, VirtualVal::Data { val: n1|n2 }),
                                "^" => set_var(&mut locs, v, VirtualVal::Data { val: n1^n2 }),
                                _ => Err(RuntimeError::NYI) 
                            }
                        
                    }
                },
            }?;
        }
        match &cur_block.next {
            ControlXfer::Fail {reason: r} => { panic!("Failure: {:?}", r )},
            ControlXfer::Ret { val: e } => {
                let result = expr_val(&locs, &globs, &prog, &e)?;
                finalresult = Some(result);
            },
            ControlXfer::Jump { block: b } => {
                let target_block = match prog.Blocks.get(b) {
                        Some(b) => Ok(b),
                        None => Err(RuntimeError::InvalidBlock { bname: b })
                }?;
                prevblock = Some(cur_block.name);
                cur_block = target_block;
            },
            ControlXfer::If { cond, tblock, fblock } => {
                let vcond = expr_val(&locs, &globs, &prog, &cond)?;
                // TODO: Reconsider if we really want global addresses to count as true instead of errors
                let target_block_name = match vcond {
                    VirtualVal::Data { val: 0 } => fblock,
                    _ => tblock
                };
                let target_block = match prog.Blocks.get(target_block_name) {
                        Some(b) => Ok(b),
                        None => Err(RuntimeError::InvalidBlock { bname: target_block_name })
                }?;
                prevblock = Some(cur_block.name);
                cur_block = target_block;
            }
        }
    }
    Ok(finalresult.unwrap())
}
fn run_prog<'a>(prog: &'a IRProgram) -> Result<VirtualVal<'a>,RuntimeError<'a>> {

    let main = prog.Blocks.get("main");
    if main.is_none() {
        return Err(RuntimeError::MissingMain);
    }
    let mut cur_block = main.unwrap();
    let (mut_mem_start, mut m, mut globs) = init_memory(prog);
    // mut_mem_start is the starting allocation point, but more importantly is also the dividing line between read-only and writable memory, so we can warn about invalid writes to RO mem
    let mut next_alloc = mut_mem_start;
    let mut cycles = 0;
    // Run main with an empty variable
    run_code(prog, cur_block, HashMap::new(), &mut globs, &mut next_alloc, mut_mem_start, &mut m)
}

fn check_warnings(prog: &IRProgram) {
    if !prog.Blocks.contains_key("main") {
        println!("WARNING: No main block found");
    }
    for (_,b) in prog.Blocks.iter() {
        let mut past_phis = false;
        for i in b.instrs.iter() {
            // Check that all phi targets exist
            match i {
                Prim::Phi { .. } => {
                    if past_phis {
                        println!("ERROR: phi instruction after non-phis in basic block {}: {:?}", b.name, i);
                    }
                },
                _ => (past_phis = true)
            }
        }
        match &b.next {
            ControlXfer::If { cond, tblock:t, fblock:f } => {
                if !prog.Blocks.contains_key(t) {
                    println!("ERROR: next block |{}| in block {} does not exist!", t, b.name);
                }
                if !prog.Blocks.contains_key(f) {
                    println!("ERROR: next block |{}| in block {} does not exist!", f, b.name);
                }
            }
            ControlXfer::Jump { block:l } => {
                if !prog.Blocks.contains_key(l) {
                    println!("ERROR: next block |{}| in block {} does not exist!", l, b.name);
                }
            }
            _ => ()
        }
    }
}

fn main() -> Result<(),Box<dyn std::error::Error>> {
    let cmd = std::env::args().nth(1).expect("need subcommand check|exec|compile");
    let txt = std::env::args().nth(2).expect("441 IR code to process");

    let libfile = Path::new(&txt);
    let display = libfile.display();

    let mut file = match File::open(&txt) {
        Err(why) => panic!("Couldn't open {}: {}", display, why),
        Ok(file) => file,
    };
    let mut bytes : Vec<u8> = vec![];
    file.read_to_end(&mut bytes)?; 
    let (leftover,prog) = parse_program(&bytes[..]).finish().map_err(|nom::error::Error { input, code }| from_utf8(input).unwrap())?;
    let cmd_str = cmd.as_str();
    if cmd_str == "check" {
        println!("Parsed: {:?}", prog);
        check_warnings(&prog);
    } else if cmd_str == "exec" {
        println!("Parsed: {:?}", prog);
        check_warnings(&prog);
        let fresult = run_prog(&prog);
        println!("Final result: {:?}", fresult);
    } else {
        panic!("Unsupported command (possibly not-yet-implemented): {}", cmd);
    }
    
    Ok(())
}

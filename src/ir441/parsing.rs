
extern crate nom;
use std::collections::{HashMap};

use crate::ir441::nodes::*;
use nom::{IResult,Finish};
use nom::bytes::complete::{tag,is_not};
use nom::branch::{alt};
use nom::character::complete::{digit1,alpha1,multispace1, multispace0,alphanumeric1};
use nom::sequence::{tuple,pair};
use nom::combinator::{recognize,all_consuming,opt};
use nom::multi::{many0,separated_list1,separated_list0};

use std::str::{from_utf8};


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
        tag("^"),
        tag("<"),
        tag(">"),
        tag("==")
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
        |i| digit1(i).map(|(rest,n)| (rest,IRExpr::IntLit { val: from_utf8(n).unwrap().parse::<u64>().unwrap() }))
    ))(i)
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

pub fn parse_phi_arg_list(i: &[u8]) -> IResult<&[u8], Vec<(&str,IRExpr)>> {
    alt((|i| tuple((separated_list1(tuple((multispace0,tag(","),multispace0)),
                                    |x| tuple((identifier,tuple((multispace0,tag(","),multispace0)),parse_ir_expr))(x).map(|(rest,(i,_,e))| (rest,(i,e)))
                                ),multispace0,tag(")")))(i).map(|(rest,(v,_,_))| (rest,v) ),
         |i| tag(")")(i).map(|(rest,_)| (rest, Vec::new()))
    ))(i)
}

pub fn parse_ir_statement(i: &[u8]) -> IResult<&[u8], IRStatement> {
    // TODO: Very sensitive to ordering. Should reject input that results in parsing a blockname phi or alloc
    let (i,_) = multispace0(i)?;
    // This is a dumb hack, but we'll just hard-code for up to 10 comments...
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    let (i,_) = opt(tuple((tag("#"), (is_not("\n")) ,tag("\n") )))(i)?;
    let (i,_) = multispace0(i)?;
    alt((
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("phi("),multispace0,parse_phi_arg_list))(i).map(|(rest,(_,l,_,_,_,_,_,a1))| (rest,IRStatement::Phi { lhs: l, opts: a1 })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("load("),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,l,_,_,_,_,_,a1,_,_))| (rest,IRStatement::Load { lhs: l, base: a1 })),
        |i| tuple((tag("store("),multispace0,parse_ir_expr,multispace0,tag(","),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,_,base,_,_,_,v,_,_))| (rest,IRStatement::Store { base: base , val: v })),
        |i| tuple((tag("setelt("),multispace0,parse_ir_expr,multispace0,tag(","),multispace0,parse_ir_expr,multispace0,tag(","),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,_,base,_,_,_,off,_,_,_,v,_,_))| (rest,IRStatement::SetElt { base: base, offset: off, val: v })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("getelt("),multispace0,parse_ir_expr,multispace0,tag(","),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,lhs,_,_,_,_,_,base,_,_,_,off,_,_))| (rest,IRStatement::GetElt { lhs: lhs, base: base, offset: off })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("load("),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,l,_,_,_,_,_,a1,_,_))| (rest,IRStatement::Load { lhs: l, base: a1 })),
        |i| tuple((tag("%"),
                   parse_register_name,
                   tuple((multispace1,tag("="),multispace1)),
                   tag("call("),
                   parse_ir_expr,
                   tuple((multispace0,tag(","),multispace0)),
                   parse_ir_expr,
                   multispace0,
                   parse_arg_list, // TODO: check handling of that first comma before the varargs part
            ))(i).map(|(rest,(_,l,_,_,cd,_,rcv,_,args))| (rest,IRStatement::Call { lhs: l, code: cd, receiver: rcv, args: args })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("alloc("),digit1,tag(")")))(i).map(
            |(rest,(_,l,_,_,_,_,d,_))| (rest,IRStatement::Alloc { lhs: l, slots: from_utf8(d).unwrap().parse::<u32>().unwrap() })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,parse_ir_expr,multispace1,parse_op,multispace1,parse_ir_expr))(i).map(|(rest,(_,l,_,_,_,a1,_,o,_,a2))| (rest,IRStatement::Op { lhs: l, arg1: a1, op: o, arg2: a2 })),
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,parse_ir_expr))(i).map(|(rest,(_,l,_,_,_,a1))| (rest,IRStatement::VarAssign { lhs: l, rhs: a1 })),
        // print
        |i| tuple((tag("print("),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,_,e,_,_))| (rest, IRStatement::Print { out: e}))
    ))(i)
}
pub fn parse_ir_statements(i: &[u8]) -> IResult<&[u8], Vec<IRStatement>> {
    // This needs to eat trailing whitespace as well, but tuple((multispace0,tag("\n"))) seems to stick the \n into the whitespace....
    separated_list0(tuple((opt(tag("\r")),tag("\n"))),//tuple((multispace0,tag("\n"))), 
        parse_ir_statement
        //|x|tuple((parse_ir_statement, 
        //          alt((|y| multispace0(y).map(|(r,_)| (r,())), |y| tuple((multispace0, tag("#"), (is_not("\n")) ))(y).map(|(r,_)| (r,())) )) 
        //    ))(x).map(|(rest,(ss,_))| (rest,ss))
    )(i)
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


// They're not really supposed to have leading %s, but I shipped some demo code that did it, so let's accept it.
pub fn parse_block_arg(i: &[u8]) -> IResult<&[u8], &str> {
    alt((
        identifier,
        |x| tuple((tag("%"),identifier))(x).map(|(rst,(_,id))| (rst,(id)))
    ))(i)
}
pub fn parse_opt_block_arg_list(i: &[u8]) -> IResult<&[u8], Vec<&str>> {
    alt((
        |x| tuple((tag(":"),opt(tag("\r")),tag("\n")))(x).map(|(rest,_)| (rest, vec![])),
        |x| tuple((tag("("), multispace0, separated_list0(tuple((multispace0,tag(","),multispace0)),parse_block_arg), multispace0, tag("):"), opt(tag("\r")), tag("\n")))(x).map(|(rest,(_,_,args,_,_,_,_))| (rest,args))
    ))(i)
}
pub fn parse_basic_block(i: &[u8]) -> IResult<&[u8], BasicBlock> {
    let (i,_) = multispace0(i)?;
    tuple((
        identifier, parse_opt_block_arg_list, parse_ir_statements, parse_control
    ))(i).map(|(rest,(name,formals,prims,ctrl))| (rest,BasicBlock { name: name, instrs: prims, next: ctrl, formals: formals}))
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
mod parsing_tests {
    use crate::ir441::parsing::*;
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
        assert_eq!(parse_ir_expr("18446744073709551614".as_bytes()), Ok((empty, IRExpr::IntLit { val : 18446744073709551614 })));
    }

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

    #[test]
    fn check_statements() {
        let empty : &[u8] = b"";
        assert_eq!(parse_ir_statement("print(3)".as_bytes()), Ok((empty, IRStatement::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("print( 3 )".as_bytes()), Ok((empty, IRStatement::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("print(\t3 )".as_bytes()), Ok((empty, IRStatement::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("\t\tprint( 3 )".as_bytes()), Ok((empty, IRStatement::Print { out: IRExpr::IntLit { val : 3}})));

        assert_eq!(parse_ir_statement("%v = 3".as_bytes()), Ok((empty, IRStatement::VarAssign { lhs: "v", rhs: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("  %v  =   3".as_bytes()), Ok((empty, IRStatement::VarAssign { lhs: "v", rhs: IRExpr::IntLit { val : 3}})));
        assert_eq!(parse_ir_statement("%1 = 10".as_bytes()), Ok((empty, IRStatement::VarAssign { lhs: "1", rhs: IRExpr::IntLit { val : 10}})));

        assert_eq!(parse_ir_statement("%1 = call(%code, %recv, %arg1, %arg2)".as_bytes()),
            Ok((empty, IRStatement::Call { lhs: "1", code: IRExpr::Var { id: "code" }, receiver: IRExpr::Var { id: "recv"}, args: vec![
                IRExpr::Var { id: "arg1" },
                IRExpr::Var { id: "arg2" },
            ]}))
        );

        assert_eq!(parse_ir_statement("%1 = load(%4)".as_bytes()), Ok((empty, IRStatement::Load { lhs: "1", base: IRExpr::Var { id : "4"}})));
        assert_eq!(parse_ir_statement("%3 = load(%2)".as_bytes()), Ok((empty, IRStatement::Load { lhs: "3", base: IRExpr::Var { id : "2"}})));
        assert_eq!(parse_ir_statement("  %3  =  load( %2 )".as_bytes()), Ok((empty, IRStatement::Load { lhs: "3", base: IRExpr::Var { id : "2"}})));

        assert_eq!(parse_ir_statement("%v = phi(bb1,%q,bb3,5)".as_bytes()), 
                   Ok((empty, IRStatement::Phi { lhs: "v", opts: vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})]})));
        assert_eq!(parse_ir_statement("  %v  =   phi( bb1 , %q , bb3 , 5 )".as_bytes()), 
                   Ok((empty, IRStatement::Phi { lhs: "v", opts: vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})]})));

        assert_eq!(parse_ir_statement("%v = 3 + 4".as_bytes()), Ok((empty, IRStatement::Op { lhs: "v", arg1: IRExpr::IntLit { val : 3}, op: "+", arg2: IRExpr::IntLit { val:4}})));
        assert_eq!(parse_ir_statement("\t %v   =  %q   * 4".as_bytes()), Ok((empty, IRStatement::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}})));


        assert_eq!(parse_ir_statements("\t %v   =  %q   * 4\nprint( %v )".as_bytes()), 
            Ok((empty, vec![IRStatement::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}},
                            IRStatement::Print { out: IRExpr::Var { id: "v"}}
            ])));
        //assert_eq!(parse_ir_statements("\t %v   =  %q   * 4     \nprint( %v )".as_bytes()), 
        //    Ok((empty, vec![IRStatement::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}},
        //                    IRStatement::Print { out: IRExpr::Var { id: "v"}}
        //    ])));
    }

    #[test]
    fn check_control() {
        let empty : &[u8] = b"";
        assert_eq!(parse_control("\tjump loophead".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, ControlXfer::Jump { block: "loophead" })));
        assert_eq!(parse_control("\tret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, ControlXfer::Ret { val: IRExpr::IntLit { val: 0 } })));
    }

    #[test]
    fn check_basicblock() {
        let empty : &[u8] = b"";
        assert_eq!(parse_basic_block("main:\n\t%1 = 10\nret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, BasicBlock {
                        name: "main",
                        formals: vec![],
                instrs: vec![IRStatement::VarAssign { lhs: "1", rhs: IRExpr::IntLit { val : 10}}],
                next: ControlXfer::Ret { val: IRExpr::IntLit { val:0 } }
            })));
        assert_eq!(parse_basic_block("mB(this):\n\tret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, BasicBlock {
                        name: "mB",
                        formals: vec!["this"],
                instrs: vec![],
                next: ControlXfer::Ret { val: IRExpr::IntLit { val:0 } }
            })));
        // Also, windows line endings
        assert_eq!(parse_basic_block("main:\r\n\t%1 = 10\r\nret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, BasicBlock {
                        name: "main",
                        formals: vec![],
                instrs: vec![IRStatement::VarAssign { lhs: "1", rhs: IRExpr::IntLit { val : 10}}],
                next: ControlXfer::Ret { val: IRExpr::IntLit { val:0 } }
            })));
        assert_eq!(parse_basic_block("mB(this):\r\n\tret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, BasicBlock {
                        name: "mB",
                        formals: vec!["this"],
                instrs: vec![],
                next: ControlXfer::Ret { val: IRExpr::IntLit { val:0 } }
            })));
    }

    #[test]
    fn check_global() {
        let empty : &[u8] = b"";
        assert_eq!(parse_global("global array vtblA: { mA }\n".as_bytes()),
            Ok((empty, GlobalStatic::Array { name: "vtblA", vals: vec![VirtualVal::CodePtr{val:"mA"}]})));
    }
}


pub fn parse_program(i: &[u8]) -> IResult<&[u8], IRProgram> {
    let (rst,_) = tuple((multispace0,tag("data:"),opt(tag("\r")),tag("\n")))(i)?;
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
            let (rst2,_) = tuple((multispace0,tag("code:"),opt(tag("\r")),tag("\n")))(postglobals)?;
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
                            Ok(("".as_bytes(), IRProgram { globals: globals, blocks: bs}))
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


// We'll just hack it all together in one file for now
extern crate nom;
use std::fs;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::collections::HashMap;
use std::str::{from_utf8,FromStr};
use nom::{IResult,Finish};
use nom::bytes::complete::{tag,is_not};
use nom::branch::{alt};
use nom::character::complete::{digit1,alpha1,multispace1, multispace0,alphanumeric1, none_of};
use nom::sequence::{delimited,tuple,pair};
use nom::combinator::{recognize,all_consuming};
use nom::multi::{many0,many1,separated_list1,separated_list0};

// We will model an architecture where code and data live in separate address spaces
// We don't need to have a global pointer because those actually get flattened into memory
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum VirtualVal<'a> {
    Data { val: u64 },
    CodePtr { val: &'a str }
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
    fn checkIRExpr() {
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
    GetElt { base: IRExpr<'a>, offset: IRExpr<'a> },
    SetElt { base: IRExpr<'a>, offset: IRExpr<'a>, val: IRExpr<'a> },
    Load { base: IRExpr<'a> },
    Store { base: IRExpr<'a>, val: IRExpr<'a> },
    Fail { reason: Reason }
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
mod TestParseArgList {
    use crate::*;
    #[test]
    fn checkArgs() {
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


pub fn parsePhiArgList(i: &[u8]) -> IResult<&[u8], Vec<(&str,IRExpr)>> {
    alt((|i| tuple((separated_list1(tuple((multispace0,tag(","),multispace0)),
                                    |x| tuple((identifier,tuple((multispace0,tag(","),multispace0)),parse_ir_expr))(x).map(|(rest,(i,_,e))| (rest,(i,e)))
                                ),multispace0,tag(")")))(i).map(|(rest,(v,_,_))| (rest,v) ),
         |i| tag(")")(i).map(|(rest,_)| (rest, Vec::new()))
    ))(i)
}
#[cfg(test)]
mod TestParsePhiArgList {
    use crate::*;
    #[test]
    fn checkPhiArgs() {
        let empty : &[u8] = b"";
        assert_eq!(parsePhiArgList(")".as_bytes()), Ok((empty, vec![])));
        assert_eq!(parsePhiArgList("blah, 3)".as_bytes()), Ok((empty, vec![("blah",IRExpr::IntLit {val:3})])));
        assert_eq!(parsePhiArgList("blah, 3, asdf, %v3)".as_bytes()), Ok((empty, vec![("blah",IRExpr::IntLit {val:3}), ("asdf",IRExpr::Var {id:"v3"})])));
        assert_eq!(parsePhiArgList("blah ,  3 )".as_bytes()), Ok((empty, vec![("blah",IRExpr::IntLit {val:3})])));
        assert_eq!(parsePhiArgList("blah ,  3  ,   asdf , %v3  )".as_bytes()), Ok((empty, vec![("blah",IRExpr::IntLit {val:3}), ("asdf",IRExpr::Var {id:"v3"})])));

        assert_eq!(parsePhiArgList("bb1,%q,bb3,5)".as_bytes()), 
                   Ok((empty, vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})])));
        assert_eq!(parsePhiArgList("bb1 , %q , bb3 , 5 )".as_bytes()), 
                   Ok((empty, vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})])));
    }
}
pub fn parseIRStatement(i: &[u8]) -> IResult<&[u8], Prim> {
    // TODO: Very sensitive to ordering. Should reject input that results in parsing a blockname phi or alloc
    let (i,_) = multispace0(i)?;
    alt((
        |i| tuple((tag("%"),parse_register_name,multispace1,tag("="),multispace1,tag("phi("),multispace0,parsePhiArgList))(i).map(|(rest,(_,l,_,_,_,_,_,a1))| (rest,Prim::Phi { lhs: l, opts: a1 })),
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
        // print, getelt, setelt, load, store
        |i| tuple((tag("print("),multispace0,parse_ir_expr,multispace0,tag(")")))(i).map(|(rest,(_,_,e,_,_))| (rest, Prim::Print { out: e})),
        |i| tuple((tag("fail"),multispace1,parse_reason))(i).map(|(rest,(_,_,r))| (rest, Prim::Fail { reason: r}))
    ))(i)
}
pub fn parseIRStatements(i: &[u8]) -> IResult<&[u8], Vec<Prim>> {
    separated_list0(tag("\n"), 
        parseIRStatement
        //|x|tuple((parseIRStatement, 
        //          alt((|y| multispace0(y).map(|(r,_)| (r,())), |y| tuple((multispace0, tag("#"), (is_not("\n")) ))(y).map(|(r,_)| (r,())) )) 
        //    ))(x).map(|(rest,(ss,_))| (rest,ss))
    )(i)
}
#[cfg(test)]
mod TestParseIRStatement {
    use crate::*;
    #[test]
    fn checkStatements() {
        let empty : &[u8] = b"";
        assert_eq!(parseIRStatement("print(3)".as_bytes()), Ok((empty, Prim::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parseIRStatement("print( 3 )".as_bytes()), Ok((empty, Prim::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parseIRStatement("print(\t3 )".as_bytes()), Ok((empty, Prim::Print { out: IRExpr::IntLit { val : 3}})));
        assert_eq!(parseIRStatement("\t\tprint( 3 )".as_bytes()), Ok((empty, Prim::Print { out: IRExpr::IntLit { val : 3}})));

        assert_eq!(parseIRStatement("%v = 3".as_bytes()), Ok((empty, Prim::VarAssign { lhs: "v", rhs: IRExpr::IntLit { val : 3}})));
        assert_eq!(parseIRStatement("  %v  =   3".as_bytes()), Ok((empty, Prim::VarAssign { lhs: "v", rhs: IRExpr::IntLit { val : 3}})));
        assert_eq!(parseIRStatement("%1 = 10".as_bytes()), Ok((empty, Prim::VarAssign { lhs: "1", rhs: IRExpr::IntLit { val : 10}})));

        assert_eq!(parseIRStatement("%v = phi(bb1,%q,bb3,5)".as_bytes()), 
                   Ok((empty, Prim::Phi { lhs: "v", opts: vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})]})));
        assert_eq!(parseIRStatement("  %v  =   phi( bb1 , %q , bb3 , 5 )".as_bytes()), 
                   Ok((empty, Prim::Phi { lhs: "v", opts: vec![("bb1",IRExpr::Var{id:"q"}), ("bb3",IRExpr::IntLit{val:5})]})));

        assert_eq!(parseIRStatement("%v = 3 + 4".as_bytes()), Ok((empty, Prim::Op { lhs: "v", arg1: IRExpr::IntLit { val : 3}, op: "+", arg2: IRExpr::IntLit { val:4}})));
        assert_eq!(parseIRStatement("\t %v   =  %q   * 4".as_bytes()), Ok((empty, Prim::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}})));


        assert_eq!(parseIRStatements("\t %v   =  %q   * 4\nprint( %v )".as_bytes()), 
            Ok((empty, vec![Prim::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}},
                            Prim::Print { out: IRExpr::Var { id: "v"}}
            ])));
    }
}

#[derive(Debug,PartialEq)]
pub enum ControlXfer<'a> {
    Jump { block: &'a str },
    If { var: &'a str, tblock: &'a str, fblock: &'a str },
    Ret { val: IRExpr<'a> }
}
pub fn parseControl(i: &[u8]) -> IResult<&[u8], ControlXfer> {
    let (i,_) = multispace0(i)?;
    alt((
        |i| tuple((tag("jump"),multispace1,identifier))(i).map(|(rest,(_,_,n))| (rest,ControlXfer::Jump { block: n})),
        |i| tuple((tag("if"),multispace1,tag("%"),parse_register_name,multispace1,tag("then"),multispace1,identifier,multispace1,tag("else"),multispace1,identifier))(i).map(|(rest,(_,_,_,b,_,_,_,t,_,_,_,f))| (rest,ControlXfer::If { var: b, tblock: t, fblock: f})),
        |i| tuple((tag("ret"),multispace1,parse_ir_expr))(i).map(|(rest,(_,_,n))| (rest,ControlXfer::Ret { val: n})),
    ))(i)
}
#[cfg(test)]
mod TestParseControl {
    use crate::*;
    #[test]
    fn checkControl() {
        let empty : &[u8] = b"";
        assert_eq!(parseControl("\tjump loophead".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, ControlXfer::Jump { block: "loophead" })));
        assert_eq!(parseControl("\tret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, ControlXfer::Ret { val: IRExpr::IntLit { val: 0 } })));
    }
}

#[derive(Debug,PartialEq)]
pub struct BasicBlock<'a> {
    name: &'a str,
    instrs: Vec<Prim<'a>>,
    next: ControlXfer<'a>
}
pub fn parse_optionalBlockArgList(i: &[u8]) -> IResult<&[u8], Vec<IRExpr>> {
    alt((
        |x| tag(":\n")(x).map(|(rest,_)| (rest, vec![])),
        |x| tuple((tag("("), multispace0, separated_list0(tuple((multispace0,tag(","),multispace0)),parse_ir_expr), multispace0, tag("):\n")))(x).map(|(rest,(_,_,args,_,_))| (rest,args))
    ))(i)
}
pub fn parse_basic_block(i: &[u8]) -> IResult<&[u8], BasicBlock> {
    let (i,_) = multispace0(i)?;
    tuple((
        identifier, parse_optionalBlockArgList, parseIRStatements, parseControl
    ))(i).map(|(rest,(name,formals,prims,ctrl))| (rest,BasicBlock { name: name, instrs: prims, next: ctrl}))
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
                instrs: vec![Prim::VarAssign { lhs: "1", rhs: IRExpr::IntLit { val : 10}}],
                next: ControlXfer::Ret { val: IRExpr::IntLit { val:0 } }
            })));
        assert_eq!(parse_basic_block("mB(this):\n\tret 0".as_bytes()).finish().map_err(|nom::error::Error { input: x, code: _}| from_utf8(x).unwrap()),
            Ok((empty, BasicBlock {
                        name: "mB",
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

pub fn parseArrayElt(i: &[u8]) -> IResult<&[u8], VirtualVal> {
    alt((
        |i| identifier(i).map(|(rest,x)| (rest,VirtualVal::CodePtr { val: x })),
        |i| digit1(i).map(|(rest,x)| (rest,VirtualVal::Data { val: from_utf8(x).unwrap().parse::<u64>().unwrap() }))
    ))(i)
}
pub fn parseArrayBody(i: &[u8]) -> IResult<&[u8], Vec<VirtualVal>> {
    tuple((multispace0,separated_list0(tuple((multispace0,tag(","),multispace0)),parseArrayElt),multispace0,tag("}")))(i).map(|(rest,(_,v,_,_))| (rest,v) )
}
pub fn parseGlobal(i: &[u8]) -> IResult<&[u8], GlobalStatic> {
    tuple((
        tuple((multispace0,tag("global"), multispace1, tag("array"), multispace0)),
        identifier,
        tuple((multispace0,tag(":"), multispace0, tag("{"))),
        parseArrayBody,
        multispace0
    ))(i).map(|(rest,(_,name,_,vs,_))| (rest,GlobalStatic::Array {name: name, vals: vs}))
}
#[cfg(test)]
mod TestParseGlobal {
    use crate::*;
    #[test]
    fn check_global() {
        let empty : &[u8] = b"";
        assert_eq!(parseGlobal("global array vtblA: { mA }\n".as_bytes()),
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
    let mut lastGlobalParse = parseGlobal(rst);
    print!("Initial global parse {:?}", lastGlobalParse);
    while let Ok((remaining,g)) = lastGlobalParse {
        print!("Parsed {:?}", g);
        print!("Global remaining = {}", from_utf8(remaining).unwrap());
        globals.push(g);
        lastGlobalParse = parseGlobal(remaining);
    }
    match lastGlobalParse.finish() {
        Err(nom::error::Error{ input: postglobals, code: _}) => {
            // TODO: figure out what happens with 
            let (rst2,_) = tuple((multispace0,tag("code:\n")))(postglobals)?;
            let mut last_block_parse = parse_basic_block(rst2);
            let mut blocks = vec![];
            while let Ok((remaining2,b)) = last_block_parse {
                println!("Parsed basic block:\n{:?}", &b);
                println!("remaining text: {:?}", from_utf8(remaining2).unwrap());
                blocks.push(b);
                last_block_parse = parse_basic_block(remaining2);
            println!("last_block_parse={:?}", &last_block_parse);
            }
            println!("last_block_parse={:?}", &last_block_parse);
            match last_block_parse.finish() {
                Err(nom::error::Error{ input: postcode, code: _}) => {
                    println!("postcode={}", from_utf8(postcode).unwrap());
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
    UnalignedAccess,
    UnallocatedAddress,
    UninitializedVariable { name: &'a str },
    MissingMain,
}


// Memory is a map from u64 to u64. Lookup will fail for unaligned accesses for now
type Memory<'a> = HashMap<u64,VirtualVal<'a>>;
type Locals<'a> = HashMap<&'a str, VirtualVal<'a>>;
type Globals<'a> = HashMap<&'a str, u64>;
fn memLookup<'a>(m:&Memory<'a>, addr:u64) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    if addr % 8 == 0 {
        match m.get(&addr) {
            None => Err(RuntimeError::UnallocatedAddress),
            Some(&v) => Ok(v)
        }
    } else {
        Err(RuntimeError::UnalignedAccess)
    }
}
fn readVar<'a>(l:&Locals<'a>, v:&'a str) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    match l.get(v) {
        Some(&x) => Ok(x),
        None => Err(RuntimeError::UninitializedVariable { name : v})
    }
}
fn setVar<'a>(l:&mut Locals<'a>, x:&'a str, val:VirtualVal<'a>) {
    l.insert(x, val);
}


fn execBBBody<'a>(b:&BasicBlock<'a>,m:Memory,l:Locals<'a>) -> Result<(), RuntimeError<'a>> {
    for p in &b.instrs {
        println!("{:?}", p);
    }
    Ok(())
}

fn init_memory<'a>(prog: &'a IRProgram) -> (u64,Memory<'a>,Globals<'a>) {
    let mut nextFree : u64 = 0x32;
    let mut m : Memory = HashMap::new();
    let mut globs : Globals = HashMap::new();

    for g in prog.Globals.iter() {

    }

    (nextFree,m,globs)
}

fn run_prog<'a>(prog: &'a IRProgram) -> Result<(),RuntimeError<'a>> {

    let main = prog.Blocks.get("main");
    if main.is_none() {
        return Err(RuntimeError::MissingMain);
    }
    let mut cur_block = main.unwrap();

    Err(RuntimeError::MissingMain)
}

fn check_warnings(prog: &IRProgram) {
    if !prog.Blocks.contains_key("main") {
        println!("WARNING: No main block found");
    }
    for (_,b) in prog.Blocks.iter() {
        for i in b.instrs.iter() {
            // Check that all phi targets exist
        }
        match b.next {
            ControlXfer::If { var:_, tblock:t, fblock:f } => {
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
    let cmd = std::env::args().nth(1).expect("need subcommand check|run|compile");
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
    } else if cmd_str == "run" {
        let _ = run_prog(&prog);
    } else {
        panic!("Unsupported command (possibly not-yet-implemented): {}", cmd);
    }
    
    Ok(())
}

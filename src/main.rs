// We'll just hack it all together in one file for now
extern crate nom;
use std::fs;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::collections::HashMap;
use std::str::{from_utf8,FromStr};
use nom::{IResult};
use nom::bytes::complete::{tag};
use nom::branch::{alt};
use nom::character::complete::{digit1,alpha1, multispace1, multispace0, alphanumeric1, none_of};
use nom::sequence::{delimited,tuple,pair};
use nom::combinator::{recognize};
use nom::multi::{many0,many1,separated_list1,separated_list0};

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
pub fn parseOp(i: &[u8]) -> IResult<&[u8], &str> {
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
pub fn parseIRExpr(i: &[u8]) -> IResult<&[u8], IRExpr> {
    let (i,_) = multispace0(i)?;
    alt((
        |i| tuple((tag("@"),identifier))(i).map(|(rest,(_,id))| (rest,IRExpr::GlobalRef { name : id })),
        |i| tuple((tag("%"),identifier))(i).map(|(rest,(_,id))| (rest,IRExpr::Var { id: id })),
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
        assert_eq!(parseIRExpr("%v3".as_bytes()), Ok((empty, IRExpr::Var { id : "v3" })));
        assert_eq!(parseIRExpr("%asdf".as_bytes()), Ok((empty, IRExpr::Var { id : "asdf" })));
        assert_eq!(parseIRExpr("@v3".as_bytes()), Ok((empty, IRExpr::GlobalRef { name : "v3" })));
        assert_eq!(parseIRExpr("@asdf".as_bytes()), Ok((empty, IRExpr::GlobalRef { name : "asdf" })));
        assert_eq!(parseIRExpr("v3".as_bytes()), Ok((empty, IRExpr::BlockRef { bname : "v3" })));
        assert_eq!(parseIRExpr("asdf".as_bytes()), Ok((empty, IRExpr::BlockRef { bname : "asdf" })));
        assert_eq!(parseIRExpr("3".as_bytes()), Ok((empty, IRExpr::IntLit { val : 3 })));
        assert_eq!(parseIRExpr("2342342".as_bytes()), Ok((empty, IRExpr::IntLit { val : 2342342 })));
        assert_eq!(parseIRExpr("23432241".as_bytes()), Ok((empty, IRExpr::IntLit { val : 23432241 })));
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
pub fn parseReason(i: &[u8]) -> IResult<&[u8], Reason> {
    let (i,_) = multispace0(i)?;
    alt((
        |i| tag("NotAPointer")(i).map(|(rest,_)| (rest, Reason::NotAPointer)),
        |i| tag("NotANumber")(i).map(|(rest,_)| (rest, Reason::NotANumber)),
        |i| tag("NoSuchMethod")(i).map(|(rest,_)| (rest, Reason::NoSuchMethod)),
        |i| tag("NoSuchField")(i).map(|(rest,_)| (rest, Reason::NoSuchField))
    ))(i)
}
pub fn parseArgList(i: &[u8]) -> IResult<&[u8], Vec<IRExpr>> {
    alt((|i| tuple((separated_list0(tuple((multispace0,tag(","),multispace0)),parseIRExpr),tag(")")))(i).map(|(rest,(v,_))| (rest,v) ),
         |i| tag(")")(i).map(|(rest,_)| (rest, Vec::new()))
    ))(i)
}
pub fn parsePhiArgList(i: &[u8]) -> IResult<&[u8], Vec<(&str,IRExpr)>> {
    alt((|i| tuple((separated_list1(tuple((multispace0,tag(","),multispace0)),
                                    |x| tuple((identifier,tuple((multispace0,tag(","),multispace0)),parseIRExpr))(x).map(|(rest,(i,_,e))| (rest,(i,e)))
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
    }
}
pub fn parseIRStatement(i: &[u8]) -> IResult<&[u8], Prim> {
    let (i,_) = multispace0(i)?;
    alt((
        |i| tuple((tag("%"),identifier,multispace1,tag("="),multispace1,parseIRExpr,multispace1,parseOp,multispace1,parseIRExpr))(i).map(|(rest,(_,l,_,_,_,a1,_,o,_,a2))| (rest,Prim::Op { lhs: l, arg1: a1, op: o, arg2: a2 })),
        |i| tuple((tag("%"),identifier,multispace1,tag("="),multispace1,parseIRExpr))(i).map(|(rest,(_,l,_,_,_,a1))| (rest,Prim::VarAssign { lhs: l, rhs: a1 })),
        |i| tuple((tag("%"),identifier,multispace1,tag("="),multispace1,tag("phi("),parsePhiArgList))(i).map(|(rest,(_,l,_,_,_,_,a1))| (rest,Prim::Phi { lhs: l, opts: a1 })),
        |i| tuple((tag("%"),
                   identifier,
                   tuple((multispace1,tag("="),multispace1)),
                   tag("call("),
                   parseIRExpr,
                   tuple((multispace0,tag(","),multispace0)),
                   parseIRExpr,
                   multispace0,
                   parseArgList, // TODO: check handling of that first comma before the varargs part
            ))(i).map(|(rest,(_,l,_,_,cd,_,rcv,_,args))| (rest,Prim::Call { lhs: l, code: cd, receiver: rcv, args: args })),
        |i| tuple((tag("%"),identifier,multispace1,tag("="),multispace1,tag("alloc("),digit1,tag(")")))(i).map(
            |(rest,(_,l,_,_,_,_,d,_))| (rest,Prim::Alloc { lhs: l, slots: from_utf8(d).unwrap().parse::<u32>().unwrap() })),
        // print, getelt, setelt, load, store
        |i| tuple((tag("print("),parseIRExpr,tag(")")))(i).map(|(rest,(_,e,_))| (rest, Prim::Print { out: e})),
        |i| tuple((tag("fail"),multispace1,parseReason))(i).map(|(rest,(_,_,r))| (rest, Prim::Fail { reason: r}))
    ))(i)
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
        |i| tuple((tag("if"),multispace1,tag("%"),identifier,multispace1,tag("then"),multispace1,identifier,multispace1,tag("else"),multispace1,identifier))(i).map(|(rest,(_,_,_,b,_,_,_,t,_,_,_,f))| (rest,ControlXfer::If { var: b, tblock: t, fblock: f})),
        |i| tuple((tag("ret"),multispace1,parseIRExpr))(i).map(|(rest,(_,_,n))| (rest,ControlXfer::Ret { val: n})),
    ))(i)
}

#[derive(Debug,PartialEq)]
pub struct BasicBlock<'a> {
    instrs: Vec<Prim<'a>>,
    next: ControlXfer<'a>
}
pub fn parseBB(i: &[u8]) -> IResult<&[u8], BasicBlock> {
    let (i,_) = multispace0(i)?;
    tuple((
        identifier, tag(":\n"), separated_list1(tag("\n"),parseIRStatement), parseControl
    ))(i).map(|(rest,(name,_,prims,ctrl))| (rest,BasicBlock { instrs: prims, next: ctrl}))
}

#[derive(Debug,PartialEq)]
pub enum GlobalStatic<'a> {
    Array { name: &'a str, vals: Vec<IRExpr<'a>> }
}
pub struct IRProgram<'a> {
    Globals: Vec<&'a GlobalStatic<'a>>,
    Blocks: HashMap<&'a str, &'a BasicBlock<'a>>
}






#[derive(Debug,PartialEq)]
pub enum RuntimeError<'a> {
    UnalignedAccess,
    UnallocatedAddress,
    UninitializedVariable { name: &'a str },
}

// Memory is a map from u64 to u64. Lookup will fail for unaligned accesses for now
type Memory = HashMap<u64,u64>;
fn memLookup(m:&Memory, addr:u64) -> Result<u64,RuntimeError> {
    if addr % 8 == 0 {
        match m.get(&addr) {
            None => Err(RuntimeError::UnallocatedAddress),
            Some(&v) => Ok(v)
        }
    } else {
        Err(RuntimeError::UnalignedAccess)
    }
}
type Locals<'a> = HashMap<&'a str, u64>;
fn readVar<'a>(l:&Locals<'a>, v:&'a str) -> Result<u64,RuntimeError<'a>> {
    match (l.get(v)) {
        Some(&x) => Ok(x),
        None => Err(RuntimeError::UninitializedVariable { name : v})
    }
}
fn setVar<'a>(l:&mut Locals<'a>, x:&'a str, val:u64) {
    l.insert(x, val);
}


fn execBBBody<'a>(b:&BasicBlock<'a>,m:Memory,l:Locals<'a>) -> Result<(), RuntimeError<'a>> {
    for p in &b.instrs {
        println!("{:?}", p);
    }
    Ok(())
}


fn main() {
    println!("Hello, world!");
}

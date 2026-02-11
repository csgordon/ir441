extern crate nom;
use std::collections::HashMap;

use crate::ir441::nodes::*;
use nom::branch::alt;
use nom::bytes::complete::{is_not, tag};
use nom::character::complete::{alpha1, alphanumeric1, digit1, multispace0, multispace1};
use nom::combinator::{all_consuming, cut, eof, opt, recognize};
use nom::error::{VerboseError, context, convert_error};
use nom::multi::{many0, many1, separated_list0, separated_list1};
use nom::sequence::{pair, tuple};
use nom::{Finish, IResult};

// Adapted from nom recipes
pub fn identifier(input: &str) -> IResult<&str, &str, VerboseError<&str>> {
    recognize(pair(
        alt((alpha1, tag("_"))),
        many0(alt((alphanumeric1, tag("_")))),
    ))(input)
}
pub fn parse_op(i: &str) -> IResult<&str, &str, VerboseError<&str>> {
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
        tag("=="),
        tag("!="),
    ))(i)
}
pub fn parse_register_name(i: &str) -> IResult<&str, &str, VerboseError<&str>> {
    alphanumeric1(i) //.map(|(rest, id)| (rest, from_utf8(id).unwrap()))
}
pub fn parse_ir_expr<'a>(i: &'a str) -> IResult<&'a str, IRExpr<'a>, VerboseError<&'a str>> {
    let (i, _) = multispace0(i)?;
    alt((
        |i| {
            tuple((tag("@"), identifier))(i)
                .map(|(rest, (_, id))| (rest, IRExpr::GlobalRef { name: id }))
        },
        |i| {
            tuple((tag("%"), parse_register_name))(i)
                .map(|(rest, (_, id))| (rest, IRExpr::Var { id: id }))
        },
        |i| identifier(i).map(|(rest, id)| (rest, IRExpr::BlockRef { bname: id })),
        |i: &'a str| {
            digit1(i).map(|(rest, n)| {
                (
                    rest,
                    IRExpr::IntLit {
                        val: n.parse::<u64>().unwrap(), //from_utf8(n).unwrap().parse::<u64>().unwrap(),
                    },
                )
            })
        },
    ))(i)
}

pub fn parse_reason(i: &str) -> IResult<&str, Reason, VerboseError<&str>> {
    let (i, _) = multispace0(i)?;
    alt((
        |i| tag("NotAPointer")(i).map(|(rest, _)| (rest, Reason::NotAPointer)),
        |i| tag("NotANumber")(i).map(|(rest, _)| (rest, Reason::NotANumber)),
        |i| tag("NoSuchMethod")(i).map(|(rest, _)| (rest, Reason::NoSuchMethod)),
        |i| tag("NoSuchField")(i).map(|(rest, _)| (rest, Reason::NoSuchField)),
    ))(i)
}
pub fn parse_arg_list<'a>(i: &'a str) -> IResult<&'a str, Vec<IRExpr<'a>>, VerboseError<&'a str>> {
    alt((
        |i| {
            tuple((
                tag(","),
                multispace0,
                separated_list0(tuple((multispace0, tag(","), multispace0)), parse_ir_expr),
                multispace0,
                tag(")"),
            ))(i)
            .map(|(rest, (_, _, v, _, _))| (rest, v))
        },
        |i| tag(")")(i).map(|(rest, _)| (rest, Vec::new())),
    ))(i)
}

pub fn parse_phi_arg_list(i: &str) -> IResult<&str, Vec<(&str, IRExpr)>, VerboseError<&str>> {
    alt((
        |i| {
            tuple((
                separated_list1(tuple((multispace0, tag(","), multispace0)), |x| {
                    tuple((
                        identifier,
                        tuple((multispace0, tag(","), multispace0)),
                        parse_ir_expr,
                    ))(x)
                    .map(|(rest, (i, _, e))| (rest, (i, e)))
                }),
                multispace0,
                tag(")"),
            ))(i)
            .map(|(rest, (v, _, _))| (rest, v))
        },
        |i| tag(")")(i).map(|(rest, _)| (rest, Vec::new())),
    ))(i)
}

pub fn parse_ir_statement(i: &str) -> IResult<&str, IRStatement, VerboseError<&str>> {
    // TODO: Very sensitive to ordering. Should reject input that results in parsing a blockname phi or alloc
    let (i, _) = multispace0(i)?;
    // This is a dumb hack, but we'll just hard-code for up to 10 comments...
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = opt(tuple((tag("#"), (is_not("\n")), tag("\n"))))(i)?;
    let (i, _) = multispace0(i)?;
    alt((
        |i| {
            tuple((
                tag("%"),
                parse_register_name,
                multispace1,
                tag("="),
                multispace1,
                tag("phi("),
                multispace0,
                parse_phi_arg_list,
            ))(i)
            .map(|(rest, (_, l, _, _, _, _, _, a1))| (rest, IRStatement::Phi { lhs: l, opts: a1 }))
        },
        |i| {
            tuple((
                tag("%"),
                parse_register_name,
                multispace1,
                tag("="),
                multispace1,
                tag("load("),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(")"),
            ))(i)
            .map(|(rest, (_, l, _, _, _, _, _, a1, _, _))| {
                (rest, IRStatement::Load { lhs: l, base: a1 })
            })
        },
        |i| {
            tuple((
                tag("store("),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(","),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(")"),
            ))(i)
            .map(|(rest, (_, _, base, _, _, _, v, _, _))| {
                (rest, IRStatement::Store { base: base, val: v })
            })
        },
        |i| {
            tuple((
                tag("setelt("),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(","),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(","),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(")"),
            ))(i)
            .map(|(rest, (_, _, base, _, _, _, off, _, _, _, v, _, _))| {
                (
                    rest,
                    IRStatement::SetElt {
                        base: base,
                        offset: off,
                        val: v,
                    },
                )
            })
        },
        |i| {
            tuple((
                tag("%"),
                parse_register_name,
                multispace1,
                tag("="),
                multispace1,
                tag("getelt("),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(","),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(")"),
            ))(i)
            .map(
                |(rest, (_, lhs, _, _, _, _, _, base, _, _, _, off, _, _))| {
                    (
                        rest,
                        IRStatement::GetElt {
                            lhs: lhs,
                            base: base,
                            offset: off,
                        },
                    )
                },
            )
        },
        |i| {
            tuple((
                tag("%"),
                parse_register_name,
                multispace1,
                tag("="),
                multispace1,
                tag("load("),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(")"),
            ))(i)
            .map(|(rest, (_, l, _, _, _, _, _, a1, _, _))| {
                (rest, IRStatement::Load { lhs: l, base: a1 })
            })
        },
        |i| {
            tuple((
                tag("%"),
                parse_register_name,
                tuple((multispace1, tag("="), multispace1)),
                tag("call("),
                parse_ir_expr,
                tuple((multispace0, tag(","), multispace0)),
                parse_ir_expr,
                multispace0,
                parse_arg_list, // TODO: check handling of that first comma before the varargs part
            ))(i)
            .map(|(rest, (_, l, _, _, cd, _, rcv, _, args))| {
                (
                    rest,
                    IRStatement::Call {
                        lhs: l,
                        code: cd,
                        receiver: rcv,
                        args: args,
                    },
                )
            })
        },
        |i| {
            tuple((
                tag("%"),
                parse_register_name,
                multispace1,
                tag("="),
                multispace1,
                tag("alloc("),
                digit1,
                tag(")"),
            ))(i)
            .map(|(rest, (_, l, _, _, _, _, d, _))| {
                (
                    rest,
                    IRStatement::Alloc {
                        lhs: l,
                        slots: d.parse::<u32>().unwrap(),
                    },
                )
            })
        },
        |i| {
            tuple((
                tag("%"),
                parse_register_name,
                multispace1,
                tag("="),
                multispace1,
                parse_ir_expr,
                multispace1,
                parse_op,
                multispace1,
                parse_ir_expr,
            ))(i)
            .map(|(rest, (_, l, _, _, _, a1, _, o, _, a2))| {
                (
                    rest,
                    IRStatement::Op {
                        lhs: l,
                        arg1: a1,
                        op: o,
                        arg2: a2,
                    },
                )
            })
        },
        |i| {
            tuple((
                tag("%"),
                parse_register_name,
                multispace1,
                tag("="),
                multispace1,
                parse_ir_expr,
            ))(i)
            .map(|(rest, (_, l, _, _, _, a1))| (rest, IRStatement::VarAssign { lhs: l, rhs: a1 }))
        },
        // print
        |i| {
            tuple((
                tag("print("),
                multispace0,
                parse_ir_expr,
                multispace0,
                tag(")"),
            ))(i)
            .map(|(rest, (_, _, e, _, _))| (rest, IRStatement::Print { out: e }))
        },
    ))(i)
}
pub fn parse_ir_statements(i: &str) -> IResult<&str, Vec<IRStatement>, VerboseError<&str>> {
    // This needs to eat trailing whitespace as well, but tuple((multispace0,tag("\n"))) seems to stick the \n into the whitespace....
    separated_list0(
        tuple((opt(tag("\r")), tag("\n"))), //tuple((multispace0,tag("\n"))),
        parse_ir_statement,                 //|x|tuple((parse_ir_statement,
                                            //          alt((|y| multispace0(y).map(|(r,_)| (r,())), |y| tuple((multispace0, tag("#"), (is_not("\n")) ))(y).map(|(r,_)| (r,())) ))
                                            //    ))(x).map(|(rest,(ss,_))| (rest,ss))
    )(i)
}

pub fn parse_control(i: &str) -> IResult<&str, ControlXfer, VerboseError<&str>> {
    let (i, _) = multispace0(i)?;
    alt((
        |i| {
            tuple((tag("jump"), multispace1, identifier))(i)
                .map(|(rest, (_, _, n))| (rest, ControlXfer::Jump { block: n }))
        },
        |i| {
            tuple((
                tag("if"),
                multispace1,
                parse_ir_expr,
                multispace1,
                tag("then"),
                multispace1,
                identifier,
                multispace1,
                tag("else"),
                multispace1,
                identifier,
            ))(i)
            .map(|(rest, (_, _, b, _, _, _, t, _, _, _, f))| {
                (
                    rest,
                    ControlXfer::If {
                        cond: b,
                        tblock: t,
                        fblock: f,
                    },
                )
            })
        },
        |i| {
            tuple((tag("ret"), multispace1, parse_ir_expr))(i)
                .map(|(rest, (_, _, n))| (rest, ControlXfer::Ret { val: n }))
        },
        |i| {
            tuple((tag("fail"), multispace1, parse_reason))(i)
                .map(|(rest, (_, _, r))| (rest, ControlXfer::Fail { reason: r }))
        },
    ))(i)
}

// They're not really supposed to have leading %s, but I shipped some demo code that did it, so let's accept it.
pub fn parse_block_arg(i: &str) -> IResult<&str, &str, VerboseError<&str>> {
    alt((identifier, |x| {
        tuple((tag("%"), identifier))(x).map(|(rst, (_, id))| (rst, (id)))
    }))(i)
}
pub fn parse_opt_block_arg_list(i: &str) -> IResult<&str, Vec<&str>, VerboseError<&str>> {
    alt((
        |x| tuple((tag(":"), opt(tag("\r")), tag("\n")))(x).map(|(rest, _)| (rest, vec![])),
        |x| {
            tuple((
                tag("("),
                multispace0,
                separated_list0(tuple((multispace0, tag(","), multispace0)), parse_block_arg),
                multispace0,
                tag("):"),
                opt(tag("\r")),
                tag("\n"),
            ))(x)
            .map(|(rest, (_, _, args, _, _, _, _))| (rest, args))
        },
    ))(i)
}
pub fn parse_basic_block(i: &str) -> IResult<&str, BasicBlock, VerboseError<&str>> {
    let (i, _) = multispace0(i)?;
    let (aftername, name) = identifier(i)?;
    let (afterformals, formals) = cut(context(
        "Expecting block arguments or colon: ",
        parse_opt_block_arg_list,
    ))(aftername)?;
    let (afterprims, prims) = parse_ir_statements(afterformals)?;
    let (rest, ctrl) = cut(context(
        "Expecting basic block to end with control transfer",
        parse_control,
    ))(afterprims)?;
    Ok((
        rest,
        BasicBlock {
            name: name,
            instrs: prims,
            next: ctrl,
            formals: formals,
        },
    ))
    // })
}

pub fn parse_array_elt<'a>(i: &'a str) -> IResult<&str, VirtualVal, VerboseError<&str>> {
    alt((
        |i| identifier(i).map(|(rest, x)| (rest, VirtualVal::CodePtr { val: x })),
        |i: &'a str| {
            digit1(i).map(|(rest, x)| {
                (
                    rest,
                    VirtualVal::Data {
                        val: x.parse::<u64>().unwrap(),
                    },
                )
            })
        },
    ))(i)
}
pub fn parse_array_body(i: &str) -> IResult<&str, Vec<VirtualVal>, VerboseError<&str>> {
    tuple((
        multispace0,
        separated_list0(tuple((multispace0, tag(","), multispace0)), parse_array_elt),
        multispace0,
        tag("}"),
    ))(i)
    .map(|(rest, (_, v, _, _))| (rest, v))
}
pub fn parse_global(i: &str) -> IResult<&str, GlobalStatic, VerboseError<&str>> {
    // TODO: rewrite using cut with context after the 'global' keyword for better parsing errors
    let (i, _) = multispace0(i)?;
    let (i, kwd) = alt((tag::<&str, &str, VerboseError<_>>("global"), tag("debug")))(i)?;
    if kwd == "global" {
        cut(context(
            "Expecting global array:",
            tuple((
                tuple((
                    multispace1,
                    cut(context("Expecting 'array' keyword:", tag("array"))),
                    multispace0,
                )),
                cut(context("Expecting global identifier name", identifier)),
                tuple((multispace0, tag(":"), multispace0, tag("{"))),
                parse_array_body,
                multispace0,
            )),
        ))(i)
        .map(|(rest, (_, name, _, vs, _))| {
            (
                rest,
                GlobalStatic::Array {
                    name: name,
                    vals: vs,
                },
            )
        })
    } else if kwd == "debug" {
        cut(context("Expecting debug declaration:", parse_debug_info))(i)
    } else {
        // Not a global
        panic!()
    }
}
pub fn parse_debug_info(i: &str) -> IResult<&str, GlobalStatic, VerboseError<&str>> {
    // This combinator is only called after the 'debug' keyword is matched in the data section
    let (info, ((_, kwd, _), _)) = tuple((
        tuple((
            multispace1,
            cut(context(
                "Expecting 'fieldnames' or 'classinfo' keyword:",
                alt((tag("fieldnames"), tag("classinfo"))),
            )),
            multispace0,
        )),
        tuple((multispace0, tag(":"), multispace0, tag("{"), multispace0)),
    ))(i)?;
    if kwd == "fieldnames" {
        // Parse a sequence of unquoted strings, followed by a closing brace
        cut(context(
            "Expected array of field names",
            tuple((
                separated_list0(tuple((multispace0, tag(","), multispace0)), identifier),
                multispace0,
                tag("}"),
                multispace0,
            )),
        ))(info)
        .map(|(rest, (ids, _, _, _))| (rest, GlobalStatic::DebugFieldNames { names: ids }))
    } else {
        // was "classinfo"
        // Parse a sequence of triples (<class name>, <vtbl name>, <field map name>)
        cut(context(
            "Expected flag list of class name, vtable, fieldmap triples",
            tuple((
                separated_list0(
                    tuple((multispace0, tag(","), multispace0)),
                    tuple((
                        identifier,
                        multispace0,
                        tag(","),
                        multispace0,
                        identifier,
                        multispace0,
                        tag(","),
                        multispace0,
                        identifier,
                    )),
                ),
                multispace0,
                tag("}"),
                multispace0,
            )),
        ))(info)
        .map(|(rest, (paddedtriples, _, _, _))| {
            let mut triples = vec![];
            for (a, _, _, _, b, _, _, _, c) in paddedtriples {
                triples.push((a, b, c));
            }
            (rest, GlobalStatic::DebugClassMeta { classinfo: triples })
        })
    }
}

#[cfg(test)]
mod parsing_tests {
    use crate::ir441::parsing::*;
    #[test]
    fn check_ir_txpr() {
        let empty = "";
        assert_eq!(parse_ir_expr("%v3"), Ok((empty, IRExpr::Var { id: "v3" })));
        assert_eq!(parse_ir_expr("%3"), Ok((empty, IRExpr::Var { id: "3" })));
        assert_eq!(
            parse_ir_expr("%asdf"),
            Ok((empty, IRExpr::Var { id: "asdf" }))
        );
        assert_eq!(
            parse_ir_expr("@v3"),
            Ok((empty, IRExpr::GlobalRef { name: "v3" }))
        );
        assert_eq!(
            parse_ir_expr("@asdf"),
            Ok((empty, IRExpr::GlobalRef { name: "asdf" }))
        );
        assert_eq!(
            parse_ir_expr("v3"),
            Ok((empty, IRExpr::BlockRef { bname: "v3" }))
        );
        assert_eq!(
            parse_ir_expr("asdf"),
            Ok((empty, IRExpr::BlockRef { bname: "asdf" }))
        );
        assert_eq!(parse_ir_expr("3"), Ok((empty, IRExpr::IntLit { val: 3 })));
        assert_eq!(
            parse_ir_expr("2342342"),
            Ok((empty, IRExpr::IntLit { val: 2342342 }))
        );
        assert_eq!(
            parse_ir_expr("23432241"),
            Ok((empty, IRExpr::IntLit { val: 23432241 }))
        );
        assert_eq!(
            parse_ir_expr("18446744073709551614"),
            Ok((
                empty,
                IRExpr::IntLit {
                    val: 18446744073709551614
                }
            ))
        );
    }

    #[test]
    fn check_args() {
        let empty = "";
        assert_eq!(parse_arg_list(")"), Ok((empty, vec![])));
        assert_eq!(
            parse_arg_list(", 3)"),
            Ok((empty, vec![IRExpr::IntLit { val: 3 }]))
        );
        assert_eq!(
            parse_arg_list(", %v3, 3)"),
            Ok((
                empty,
                vec![IRExpr::Var { id: "v3" }, IRExpr::IntLit { val: 3 }]
            ))
        );
        assert_eq!(
            parse_arg_list(", %3, 3)"),
            Ok((
                empty,
                vec![IRExpr::Var { id: "3" }, IRExpr::IntLit { val: 3 }]
            ))
        );
        assert_eq!(
            parse_arg_list(", %v3 , 3 )"), //.map(|(rest, r)| (from_utf8(rest).unwrap(), r)),
            Ok((
                "",
                vec![IRExpr::Var { id: "v3" }, IRExpr::IntLit { val: 3 }]
            ))
        );
    }

    #[test]
    fn check_phi_args() {
        let empty = "";
        assert_eq!(parse_phi_arg_list(")"), Ok((empty, vec![])));
        assert_eq!(
            parse_phi_arg_list("blah, 3)"),
            Ok((empty, vec![("blah", IRExpr::IntLit { val: 3 })]))
        );
        assert_eq!(
            parse_phi_arg_list("blah, 3, asdf, %v3)"),
            Ok((
                empty,
                vec![
                    ("blah", IRExpr::IntLit { val: 3 }),
                    ("asdf", IRExpr::Var { id: "v3" })
                ]
            ))
        );
        assert_eq!(
            parse_phi_arg_list("blah ,  3 )"),
            Ok((empty, vec![("blah", IRExpr::IntLit { val: 3 })]))
        );
        assert_eq!(
            parse_phi_arg_list("blah ,  3  ,   asdf , %v3  )"),
            Ok((
                empty,
                vec![
                    ("blah", IRExpr::IntLit { val: 3 }),
                    ("asdf", IRExpr::Var { id: "v3" })
                ]
            ))
        );

        assert_eq!(
            parse_phi_arg_list("bb1,%q,bb3,5)"),
            Ok((
                empty,
                vec![
                    ("bb1", IRExpr::Var { id: "q" }),
                    ("bb3", IRExpr::IntLit { val: 5 })
                ]
            ))
        );
        assert_eq!(
            parse_phi_arg_list("bb1 , %q , bb3 , 5 )"),
            Ok((
                empty,
                vec![
                    ("bb1", IRExpr::Var { id: "q" }),
                    ("bb3", IRExpr::IntLit { val: 5 })
                ]
            ))
        );
    }

    #[test]
    fn check_statements() {
        let empty = "";
        assert_eq!(
            parse_ir_statement("print(3)"),
            Ok((
                empty,
                IRStatement::Print {
                    out: IRExpr::IntLit { val: 3 }
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("print( 3 )"),
            Ok((
                empty,
                IRStatement::Print {
                    out: IRExpr::IntLit { val: 3 }
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("print(\t3 )"),
            Ok((
                empty,
                IRStatement::Print {
                    out: IRExpr::IntLit { val: 3 }
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("\t\tprint( 3 )"),
            Ok((
                empty,
                IRStatement::Print {
                    out: IRExpr::IntLit { val: 3 }
                }
            ))
        );

        assert_eq!(
            parse_ir_statement("%v = 3"),
            Ok((
                empty,
                IRStatement::VarAssign {
                    lhs: "v",
                    rhs: IRExpr::IntLit { val: 3 }
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("  %v  =   3"),
            Ok((
                empty,
                IRStatement::VarAssign {
                    lhs: "v",
                    rhs: IRExpr::IntLit { val: 3 }
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("%1 = 10"),
            Ok((
                empty,
                IRStatement::VarAssign {
                    lhs: "1",
                    rhs: IRExpr::IntLit { val: 10 }
                }
            ))
        );

        assert_eq!(
            parse_ir_statement("%1 = call(%code, %recv, %arg1, %arg2)"),
            Ok((
                empty,
                IRStatement::Call {
                    lhs: "1",
                    code: IRExpr::Var { id: "code" },
                    receiver: IRExpr::Var { id: "recv" },
                    args: vec![IRExpr::Var { id: "arg1" }, IRExpr::Var { id: "arg2" },]
                }
            ))
        );

        assert_eq!(
            parse_ir_statement("%1 = load(%4)"),
            Ok((
                empty,
                IRStatement::Load {
                    lhs: "1",
                    base: IRExpr::Var { id: "4" }
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("%3 = load(%2)"),
            Ok((
                empty,
                IRStatement::Load {
                    lhs: "3",
                    base: IRExpr::Var { id: "2" }
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("  %3  =  load( %2 )"),
            Ok((
                empty,
                IRStatement::Load {
                    lhs: "3",
                    base: IRExpr::Var { id: "2" }
                }
            ))
        );

        assert_eq!(
            parse_ir_statement("%v = phi(bb1,%q,bb3,5)"),
            Ok((
                empty,
                IRStatement::Phi {
                    lhs: "v",
                    opts: vec![
                        ("bb1", IRExpr::Var { id: "q" }),
                        ("bb3", IRExpr::IntLit { val: 5 })
                    ]
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("  %v  =   phi( bb1 , %q , bb3 , 5 )"),
            Ok((
                empty,
                IRStatement::Phi {
                    lhs: "v",
                    opts: vec![
                        ("bb1", IRExpr::Var { id: "q" }),
                        ("bb3", IRExpr::IntLit { val: 5 })
                    ]
                }
            ))
        );

        assert_eq!(
            parse_ir_statement("%v = 3 + 4"),
            Ok((
                empty,
                IRStatement::Op {
                    lhs: "v",
                    arg1: IRExpr::IntLit { val: 3 },
                    op: "+",
                    arg2: IRExpr::IntLit { val: 4 }
                }
            ))
        );
        assert_eq!(
            parse_ir_statement("\t %v   =  %q   * 4"),
            Ok((
                empty,
                IRStatement::Op {
                    lhs: "v",
                    arg1: IRExpr::Var { id: "q" },
                    op: "*",
                    arg2: IRExpr::IntLit { val: 4 }
                }
            ))
        );

        assert_eq!(
            parse_ir_statements("\t %v   =  %q   * 4\nprint( %v )"),
            Ok((
                empty,
                vec![
                    IRStatement::Op {
                        lhs: "v",
                        arg1: IRExpr::Var { id: "q" },
                        op: "*",
                        arg2: IRExpr::IntLit { val: 4 }
                    },
                    IRStatement::Print {
                        out: IRExpr::Var { id: "v" }
                    }
                ]
            ))
        );
        //assert_eq!(parse_ir_statements("\t %v   =  %q   * 4     \nprint( %v )".as_bytes()),
        //    Ok((empty, vec![IRStatement::Op { lhs: "v", arg1: IRExpr::Var { id: "q"}, op: "*", arg2: IRExpr::IntLit { val:4}},
        //                    IRStatement::Print { out: IRExpr::Var { id: "v"}}
        //    ])));
    }

    #[test]
    fn check_control() {
        let empty = "";
        assert_eq!(
            parse_control("\tjump loophead").finish(),
            Ok((empty, ControlXfer::Jump { block: "loophead" }))
        );
        assert_eq!(
            parse_control("\tret 0").finish(),
            Ok((
                empty,
                ControlXfer::Ret {
                    val: IRExpr::IntLit { val: 0 }
                }
            ))
        );
        assert_eq!(
            parse_control("  ret 0").finish(),
            Ok((
                empty,
                ControlXfer::Ret {
                    val: IRExpr::IntLit { val: 0 }
                }
            ))
        );
    }

    #[test]
    fn check_basicblock() {
        let empty = "";
        assert_eq!(
            parse_basic_block("main:\n\t%1 = 10\nret 0").finish(),
            Ok((
                empty,
                BasicBlock {
                    name: "main",
                    formals: vec![],
                    instrs: vec![IRStatement::VarAssign {
                        lhs: "1",
                        rhs: IRExpr::IntLit { val: 10 }
                    }],
                    next: ControlXfer::Ret {
                        val: IRExpr::IntLit { val: 0 }
                    }
                }
            ))
        );
        assert_eq!(
            parse_basic_block("main:\n  %1 = 10\n  ret 0").finish(),
            Ok((
                empty,
                BasicBlock {
                    name: "main",
                    formals: vec![],
                    instrs: vec![IRStatement::VarAssign {
                        lhs: "1",
                        rhs: IRExpr::IntLit { val: 10 }
                    }],
                    next: ControlXfer::Ret {
                        val: IRExpr::IntLit { val: 0 }
                    }
                }
            ))
        );
        assert_eq!(
            parse_basic_block("main:\n  ret 0").finish(),
            Ok((
                empty,
                BasicBlock {
                    name: "main",
                    formals: vec![],
                    instrs: vec![],
                    next: ControlXfer::Ret {
                        val: IRExpr::IntLit { val: 0 }
                    }
                }
            ))
        );
        assert_eq!(
            parse_basic_block("mB(this):\n\tret 0").finish(),
            Ok((
                empty,
                BasicBlock {
                    name: "mB",
                    formals: vec!["this"],
                    instrs: vec![],
                    next: ControlXfer::Ret {
                        val: IRExpr::IntLit { val: 0 }
                    }
                }
            ))
        );
        // Also, windows line endings
        assert_eq!(
            parse_basic_block("main:\r\n\t%1 = 10\r\nret 0").finish(),
            Ok((
                empty,
                BasicBlock {
                    name: "main",
                    formals: vec![],
                    instrs: vec![IRStatement::VarAssign {
                        lhs: "1",
                        rhs: IRExpr::IntLit { val: 10 }
                    }],
                    next: ControlXfer::Ret {
                        val: IRExpr::IntLit { val: 0 }
                    }
                }
            ))
        );
        assert_eq!(
            parse_basic_block("mB(this):\r\n\tret 0").finish(),
            Ok((
                empty,
                BasicBlock {
                    name: "mB",
                    formals: vec!["this"],
                    instrs: vec![],
                    next: ControlXfer::Ret {
                        val: IRExpr::IntLit { val: 0 }
                    }
                }
            ))
        );
    }

    #[test]
    fn check_global() {
        let empty = "";
        assert_eq!(
            parse_global("global array vtblA: { mA }\n"),
            Ok((
                empty,
                GlobalStatic::Array {
                    name: "vtblA",
                    vals: vec![VirtualVal::CodePtr { val: "mA" }]
                }
            ))
        );
        assert_eq!(
            parse_global("debug fieldnames: { x, y, foo }\n"),
            Ok((
                empty,
                GlobalStatic::DebugFieldNames {
                    names: vec!["x", "y", "foo"]
                }
            ))
        );
        assert_eq!(
            parse_global("debug fieldnames: { x,y , foo }\n"),
            Ok((
                empty,
                GlobalStatic::DebugFieldNames {
                    names: vec!["x", "y", "foo"]
                }
            ))
        );
        assert_eq!(
            parse_global("debug classinfo : { Foo, vtblFoo,fieldsFoo }\n"),
            Ok((
                empty,
                GlobalStatic::DebugClassMeta {
                    classinfo: vec![("Foo", "vtblFoo", "fieldsFoo")]
                }
            ))
        );
    }
}

pub fn parse_program<'a>(
    i: &'a str,
) -> IResult<&'a str, IRProgram<'a>, nom::error::VerboseError<&'a str>> {
    let (rst, _) = tuple((
        multispace0,
        cut(context(
            "Program missing initial data: section",
            tag("data:"),
        )),
        opt(tag("\r")),
        tag("\n"),
    ))(i)?;
    let mut globals = vec![];
    let mut last_global_parse = parse_global(rst);
    //print!("Initial global parse {:?}", last_global_parse);
    while let Ok((remaining, g)) = last_global_parse {
        //print!("Parsed {:?}", g);
        //print!("Global remaining = {}", from_utf8(remaining).unwrap());
        globals.push(g);
        last_global_parse = parse_global(remaining);
    }
    match last_global_parse.finish() {
        Err(nom::error::VerboseError { errors }) => {
            let postglobals = errors[0].0;
            // TODO: figure out what happens with
            let (rst2, _) = tuple((
                multispace0,
                cut(context(
                    "Program missing 'code:' section header",
                    tag("code:"),
                )),
                opt(tag("\r")),
                tag("\n"),
            ))(postglobals)?;
            let blockparse: IResult<&'a str, Vec<BasicBlock<'a>>, VerboseError<&'a str>> =
                cut(context(
                    "Expecting at least one valid basic block",
                    many1(parse_basic_block),
                ))(rst2);
            let (postcode, mut blocks) = blockparse?;
            let tail = cut(context(
                "Only blank spaces are permitted after the last valid block",
                all_consuming::<_, _, nom::error::VerboseError<&str>, _>(multispace0),
            ))(postcode)
            .finish();

            match tail {
                Ok(_) => {
                    let mut bs = HashMap::new();
                    while let Some(b) = blocks.pop() {
                        bs.insert(b.name, b);
                    }
                    Ok((
                        "",
                        IRProgram {
                            globals: globals,
                            blocks: bs,
                        },
                    ))
                }
                Err(ve) => {
                    eprintln!(
                        "Leftover text after parsing blocks: {}",
                        convert_error(i, ve)
                    );
                    panic!("Aborting due to unparseable input")
                }
            }
        }
        _ => panic!("This should be impossible"),
    }
}

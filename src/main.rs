// We'll just hack it all together in one file for now
extern crate nom;
mod ir441;

use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

use std::str::{from_utf8};
use nom::{Finish};

use crate::ir441::nodes::*;
use crate::ir441::parsing::*;
use crate::ir441::exec::*;

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{BasicValue, BasicValueEnum, BasicMetadataValueEnum, FunctionValue, PointerValue, IntValue, AnyValue};
use inkwell::IntPredicate;
use std::collections::{HashMap,HashSet};
use std::iter::repeat;
use either::*;

// The following is heavily based on the inkwell port of the LLVM Kaleidoscope language
fn compile_expr<'ctx,'b,'a>(context: &'ctx Context, builder: &'b Builder<'ctx>, vars: &HashMap<&'a str,Either<PointerValue<'ctx>,BasicValueEnum<'ctx>>>, e: &'a IRExpr) -> Result<BasicValueEnum<'ctx>, &'static str> {
    match *e {
        IRExpr::IntLit { val } => Ok(context.i64_type().const_int(val, false).as_basic_value_enum()),
        IRExpr::Var { id } => {
            let lkp = vars.get(id).unwrap();
            match lkp {
                Either::Left(ptr) => Ok(builder.build_load(*ptr, id)),
                Either::Right(var) => Ok(*var)
            }
        },
        _ => panic!("NYI expression form for LLVM")
    }
}

fn compile_statement<'ctx,'b,'a>(context: &'ctx Context, builder: &'b Builder<'ctx>, vars: &mut HashMap<&'a str,Either<PointerValue<'ctx>,BasicValueEnum<'ctx>>>, s: &'a IRStatement) -> Result<(),&'static str> {
    match &*s {
        IRStatement::Op { lhs, arg1, op, arg2 } => {
            let e1 = compile_expr(&context, &builder, &vars, &arg1)?.into_int_value();
            let e2 = compile_expr(&context, &builder, &vars, &arg2)?.into_int_value();
            let res = match *op {
                        "+" => builder.build_int_add::<IntValue<'ctx>>(e1, e2, lhs),
                        "-" => builder.build_int_sub::<IntValue<'ctx>>(e1, e2, lhs),
                        "/" => builder.build_int_unsigned_div::<IntValue<'ctx>>(e1, e2, lhs),
                        "*" => builder.build_int_mul::<IntValue<'ctx>>(e1, e2, lhs),
                        "==" => builder.build_int_compare::<IntValue<'ctx>>(IntPredicate::EQ, e1, e2, lhs),
                        "!=" => builder.build_int_compare::<IntValue<'ctx>>(IntPredicate::NE, e1, e2, lhs),
                        "<" => builder.build_int_compare::<IntValue<'ctx>>(IntPredicate::ULT, e1, e2, lhs),
                        ">" => builder.build_int_compare::<IntValue<'ctx>>(IntPredicate::UGT, e1, e2, lhs),
                        "<=" => builder.build_int_compare::<IntValue<'ctx>>(IntPredicate::ULE, e1, e2, lhs),
                        ">=" => builder.build_int_compare::<IntValue<'ctx>>(IntPredicate::UGE, e1, e2, lhs),
                        "<<" => builder.build_left_shift::<IntValue<'ctx>>(e1, e2, lhs),
                        ">>" => builder.build_right_shift::<IntValue<'ctx>>(e1, e2, true, lhs),
                        "|" => builder.build_or::<IntValue<'ctx>>(e1, e2, lhs),
                        "&" => builder.build_and::<IntValue<'ctx>>(e1, e2, lhs),
                        _ => panic!("Unknown IR operation in LLVM gen: {}", *op)
                    };
            // DEBUG
            res.print_to_stderr();
            if let Some(Either::Left(ptr)) = vars.get(lhs) {
                builder.build_store(*ptr, res);
            } else {
                // Not in there as a pointer, so we just need the subsequent lookup
                vars.insert(lhs, Either::Right(res.as_basic_value_enum()));
            }
        },
        IRStatement::VarAssign{lhs,rhs} => {
            let e = compile_expr(&context, &builder, &vars, &rhs)?.into_int_value();
            // Store only stores into allocated locations, it's not really for SSA variable assignment
            match vars.get(lhs).unwrap() {
                Either::Left(ptr) => { 
                    println!("Generating store into: {:?}", ptr);
                    builder.build_store(*ptr, e); 
                },
                Either::Right(v) => { panic!("Not sure how to store to a var yet") }
            }
        },
        _ => panic!("NYI statement form for LLVM: {:?}", *s)
    };
    Ok(())
}
fn compile_control<'ctx,'b,'a>(
                            prog: &'a IRProgram,
                            func: FunctionValue<'ctx>,
                            module: &Module<'ctx>,
                            context: &'ctx Context,
                            builder: &'b Builder<'ctx>, 
                            mut blocks: &mut HashMap<&'a str,inkwell::basic_block::BasicBlock<'ctx>>,
                            mut vars: &mut HashMap<&'a str,Either<PointerValue<'ctx>,BasicValueEnum<'ctx>>>,
                            llbb: inkwell::basic_block::BasicBlock<'ctx>,
                            s: &'a ControlXfer) -> Result<(),&'static str> {
    match &*s {
        ControlXfer::Ret{val} => {
            let v = compile_expr(context, builder, vars, &val)?;
            builder.build_return(Some(&v));
        },
        ControlXfer::Jump{block} => {
            // We may or may not have already built the block
            let bv = compile_basic_block(prog, func, module, context, builder, &mut blocks, &mut vars, prog.blocks.get(block).unwrap())?;
            // The above may build those blocks, need to reset builder location
            builder.position_at_end(llbb);
            builder.build_unconditional_branch(bv);
        },
        ControlXfer::If{cond,tblock,fblock} => {
            let tbv = compile_basic_block(prog, func, module, context, builder, &mut blocks, &mut vars, prog.blocks.get(tblock).unwrap())?;
            let fbv = compile_basic_block(prog, func, module, context, builder, &mut blocks, &mut vars, prog.blocks.get(fblock).unwrap())?;
            // The above may build those blocks, need to reset builder location
            builder.position_at_end(llbb);

            let cval = compile_expr(context, builder, vars, &cond)?;

            let isz = builder.build_int_compare(IntPredicate::EQ, context.i64_type().const_int(0,false), cval.into_int_value(), "isz");
            builder.build_conditional_branch(isz, tbv, fbv);
        },
        ControlXfer::Fail{reason} => {
            panic!("NYI: Cannot generate LLVM for {:?}", reason);
        }
    };
    Ok(())
}

fn compile_function<'ctx,'b,'a>(prog: &'a IRProgram, module: &'b Module<'ctx>, context: &'ctx Context, builder: &'b Builder<'ctx>, b : &'a BasicBlock<'a>) -> Result<FunctionValue<'ctx>, &'static str> {
    let itype = context.i64_type();
    let args = repeat(itype).take(b.formals.len()).map(|x| x.into()).collect::<Vec<BasicMetadataTypeEnum>>();
    let args2 = args.as_slice();
    let ftype = context.i64_type().fn_type(args2, false);
    let f = module.add_function(b.name, ftype, None);
    for (i, arg) in f.get_param_iter().enumerate() {
        arg.into_int_value().set_name(b.formals[i])
    }

    // Need to do some analysis to identify variables that are assigned to
    // multiple times (including use as a method arg as a "definition").
    // This is because there's actually no non-SSA version of the code, so if
    // we're going to tolerate non-SSA code in this backend, we need to 
    // allocate stack space for (only) those variables
    // I *could* just do the SSA transformation, but we want this code to be
    // public so students can look at how some of the things I *don't* ask
    // them to implement can work.

    // TODO: This is inefficient, we do this for every function, and blocks includes *all* functions
    let mut block_asgns = HashMap::new();
    for name in b.formals.iter() {
        block_asgns.insert(name, 1);
    }
    for (name, b) in prog.blocks.iter() {
        for i in b.instrs.iter() {
            if let Some(var) = match i {
                            // ehh, this should be swapped to just count assignments for every lhs, not compute the sets, which I don't actually need
                            IRStatement::Alloc{lhs, ..} =>      Some(lhs),
                            IRStatement::Call{lhs, ..} =>       Some(lhs),
                            IRStatement::GetElt{lhs, ..} =>     Some(lhs),
                            IRStatement::Load{lhs, ..} =>       Some(lhs),
                            IRStatement::Op{lhs, ..} =>         Some(lhs),
                            IRStatement::Phi{lhs, ..} =>        Some(lhs),
                            IRStatement::VarAssign{lhs, ..} =>  Some(lhs),
                            _ => None
                            } {
                if let Some(cnt) = block_asgns.get_mut(var) {
                    *cnt = *cnt + 1;
                    println!("Found multiple writes to {}", var);
                } else {
                    block_asgns.insert(var, 1);
                }
            }
        }
    }


    let entry = context.append_basic_block(f, b.name);
    builder.position_at_end(entry);
    let mut blocks = HashMap::new();
    blocks.insert(b.name, entry);
    let mut vars : HashMap<&'a str,Either<PointerValue<'ctx>,BasicValueEnum<'ctx>>> = HashMap::new();
    vars.reserve(b.formals.len());
    for (i, arg) in f.get_param_iter().enumerate() {
        if (*block_asgns.get(&b.formals[i]).unwrap() > 1) {
            let alloca = builder.build_alloca(context.i64_type(), b.formals[i]);
            builder.build_store(alloca, arg);
            vars.insert(b.formals[i], Either::Left(alloca));
        }
    }
    for (name, cnt) in block_asgns.iter() {
        if !vars.contains_key(*name) {
            let tmp = block_asgns.get(*name);
            if (tmp.is_some() && *tmp.unwrap() > 1) {
                // Not an argument, so allocate but no initial store is needed
                let alloca = builder.build_alloca(context.i64_type(), *name);
                vars.insert(*name, Either::Left(alloca));
            }
        }
    }
    // Now vars contains allocations for all variables that are overwritten.
    // Stores should then be tweaked to update those locations with the appropriate value

    // Don't just reuse compile_basic_block, because 
    //compile_basic_block(f, &module, &context, &builder, &mut blocks, &mut vars, &b)?;
    for i in &b.instrs {
        compile_statement(context, builder, &mut vars, &i)?;
    }
    compile_control(prog, f, module, context, builder, &mut blocks, &mut vars, entry, &b.next)?;
    f.verify(true);
    Ok(f)
}
fn compile_basic_block<'ctx,'b,'a>(prog: &'a IRProgram,
                                   f: FunctionValue<'ctx>,
                                   module: &'b Module<'ctx>, 
                                   context: &'ctx Context, 
                                   builder: &'b Builder<'ctx>, 
                                   mut blocks: &mut HashMap<&'a str,inkwell::basic_block::BasicBlock<'ctx>>,
                                   mut vars: &mut HashMap<&'a str,Either<PointerValue<'ctx>,BasicValueEnum<'ctx>>>,
                                   b : &'a BasicBlock<'a>) -> Result<inkwell::basic_block::BasicBlock<'ctx>, &'static str> {
    let prior = blocks.get(b.name);
    if prior.is_some() {
        return Ok(*prior.unwrap());
    }
    let bb = context.append_basic_block(f, b.name);
    blocks.insert(b.name, bb);
    builder.position_at_end(bb);
    for i in &b.instrs {
        compile_statement(context, builder, &mut vars, &i)?;
    }
    compile_control(prog, f, module, context, builder, &mut blocks, &mut vars, bb, &b.next)?;

    Ok(bb)
}






fn check_warnings(prog: &IRProgram) {
    if !prog.blocks.contains_key("main") {
        println!("WARNING: No main block found");
    }
    for (_,b) in prog.blocks.iter() {
        let mut past_phis = false;
        for i in b.instrs.iter() {
            // Check that all phi targets exist
            match i {
                IRStatement::Phi { .. } => {
                    if past_phis {
                        println!("ERROR: phi instruction after non-phis in basic block {}: {:?}", b.name, i);
                    }
                },
                _ => (past_phis = true)
            }
        }
        match &b.next {
            ControlXfer::If { cond: _, tblock:t, fblock:f } => {
                if !prog.blocks.contains_key(t) {
                    println!("ERROR: next block |{}| in block {} does not exist!", t, b.name);
                }
                if !prog.blocks.contains_key(f) {
                    println!("ERROR: next block |{}| in block {} does not exist!", f, b.name);
                }
            }
            ControlXfer::Jump { block:l } => {
                if !prog.blocks.contains_key(l) {
                    println!("ERROR: next block |{}| in block {} does not exist!", l, b.name);
                }
            }
            _ => ()
        }
    }
}

fn main() -> Result<(),Box<dyn std::error::Error>> {
    let cmd = std::env::args().nth(1).expect("need subcommand [check|exec|trace|perf]");
    let txt = std::env::args().nth(2).expect("441 IR code to process");

    let libfile = Path::new(&txt);
    let display = libfile.display();

    let mut file = match File::open(&txt) {
        Err(why) => panic!("Couldn't open {}: {}", display, why),
        Ok(file) => file,
    };
    let mut bytes : Vec<u8> = vec![];
    file.read_to_end(&mut bytes)?; 
    let (_leftover,prog) = parse_program(&bytes[..]).finish().map_err(|nom::error::Error { input, code: _ }| from_utf8(input).unwrap())?;
    let cmd_str = cmd.as_str();

    let mut cycles = ExecStats { allocs: 0, calls: 0, fast_alu_ops: 0, slow_alu_ops: 0, phis: 0, conditional_branches: 0, unconditional_branches: 0, mem_reads: 0, mem_writes: 0, prints: 0, rets: 0 };

    if cmd_str == "check" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
    } else if cmd_str == "exec" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _fresult = run_prog(&prog, false, &mut cycles);
    } else if cmd_str == "trace" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _ = run_prog(&prog, true, &mut cycles);
    } else if cmd_str == "perf" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _ = run_prog(&prog, false, &mut cycles);
        println!("Execution stats:\n{:?}", cycles);
    } else if cmd_str == "llvm" {
        let context = Context::create();
        let module = context.create_module(&txt);
        let builder = context.create_builder();
        for (name, entry) in prog.blocks.iter() {
            // Strictly speaking we should have a more robust way to identify function entry points, but
            // since our language only has instance methods with explicit 'this' params, this is
            // effective.
            // Note that some students choose to emit only a single error block for each kind of error,
            // for their whole program. Doing this function-at-a-time means we will actually
            // traverse all reachable blocks for each function, in effect duplicating those error-handling
            // blocks for each function that needs them in the LLVM IR, where blocks are grouped by function.
            if (*name == "main" || entry.formals.len() > 0) {
                compile_function(&prog, &module, &context, &builder, entry)?;
            }
        }
        //fmain.print_to_stderr();
        module.print_to_stderr();
    } else {
        panic!("Unsupported command (possibly not-yet-implemented): {}", cmd);
    }
    
    Ok(())
}

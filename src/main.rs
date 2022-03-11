#![feature(is_some_with)]
// We'll just hack it all together in one file for now
extern crate nom;
mod ir441;

use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::collections::{HashMap,BTreeMap};

use std::str::{from_utf8};
use nom::{IResult,Finish};

use crate::ir441::nodes::*;
use crate::ir441::parsing::*;
use crate::ir441::exec::*;






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
        let _fresult = run_prog(&prog, false, &mut cycles, None);
    } else if cmd_str == "trace" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _ = run_prog(&prog, true, &mut cycles, None);
    } else if cmd_str == "perf" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _ = run_prog(&prog, false, &mut cycles, None);
        println!("Execution stats:\n{:?}", cycles);
    } else {
        panic!("Unsupported command (possibly not-yet-implemented): {}", cmd);
    }
    
    Ok(())
}

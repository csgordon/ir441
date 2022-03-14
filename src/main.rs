#![feature(is_some_with)]
// We'll just hack it all together in one file for now
extern crate nom;
mod ir441;

use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::io::{self, BufReader};
use std::path::Path;
use std::collections::{HashMap,BTreeMap};

use std::str::{from_utf8};
use nom::{Finish};

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
    let txt = std::env::args().nth(2);
    let mut reader: Box<dyn BufRead> = match txt {
        None => Box::new(BufReader::new(io::stdin())),
        Some(filepath) => {
            let libfile = Path::new(&filepath);
            let display = libfile.display();
            match File::open(&filepath) {
                Err(why) => panic!("Couldn't open {}: {}", display, why),
                Ok(file) => Box::new(BufReader::new(file)),
            }
        }
    };

    let mut bytes : Vec<u8> = vec![];
    reader.read_to_end(&mut bytes)?; 
    let (_leftover,prog) = parse_program(&bytes[..]).finish().map_err(|nom::error::Error { input, code: _ }| from_utf8(input).unwrap())?;
    let cmd_str = cmd.as_str();

    let mut cycles = ExecStats::new();

    if cmd_str == "check" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
    } else if cmd_str == "exec" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _fresult = run_prog(&prog, false, &mut cycles, ExecMode::Unlimited);
    } else if cmd_str == "exec-fixedmem" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _fresult = run_prog(&prog, true, &mut cycles, ExecMode::MemCap {limit:100});
    } else if cmd_str == "exec-gc" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _fresult = run_prog(&prog, false, &mut cycles, ExecMode::GC {limit:100});
    } else if cmd_str == "exec-gc-logging" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _fresult = run_prog(&prog, false, &mut cycles, ExecMode::GC {limit:100});
    } else if cmd_str == "trace" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _ = run_prog(&prog, true, &mut cycles, ExecMode::Unlimited);
    } else if cmd_str == "perf" {
        println!("Parsed: {}", prog);
        check_warnings(&prog);
        let _ = run_prog(&prog, false, &mut cycles, ExecMode::Unlimited);
        println!("Execution stats:\n{:?}", cycles);
    } else {
        println!("Unsupported command (possibly not-yet-implemented): {}", cmd);
        panic!("Usage: ir441 (check|exec|exec-fixedmem|exec-gc|exec-gc-logging|trace|perf)");
    }
    
    Ok(())
}

#[cfg(test)]
mod systests {
    use std::path::Path;
    use std::fs::File;
    use std::io::{BufReader,BufRead};
    use crate::ir441::nodes::*;
    use crate::ir441::parsing::*;
    use crate::ir441::exec::*;
    use std::str::{from_utf8};
    use nom::{Finish};

    fn load_program(filepath: &str) -> Result<Vec<u8>,Box<dyn std::error::Error>> {
        let libfile = Path::new(&filepath);
        let display = libfile.display();
        let mut reader: Box<dyn BufRead> = 
        match File::open(&filepath) {
            Err(why) => panic!("Couldn't open {}: {}", display, why),
            Ok(file) => Box::new(BufReader::new(file)),
        };
        let mut bytes : Vec<u8> = vec![];
        reader.read_to_end(&mut bytes)?; 
        Ok(bytes)
    }
    fn parse(bytes:&Vec<u8>) -> Result<IRProgram,Box<dyn std::error::Error>> {
        let (_leftover,prog) = parse_program(&bytes[..]).finish().map_err(|nom::error::Error { input, code: _ }| from_utf8(input).unwrap())?;
        Ok(prog)
    }
    #[test]
    fn check_trivial() -> Result<(),Box<dyn std::error::Error>>{
        let bytes = load_program("examples/trivial.ir")?;
        let prog = parse(&bytes)?;
        let mut cycles = ExecStats::new();
        let result = run_prog(&prog, false, &mut cycles, ExecMode::Unlimited);
        assert_eq!(result,Ok(VirtualVal::Data { val: 23 }));
        Ok(())
    }
    #[test]
    fn check_countdown() -> Result<(),Box<dyn std::error::Error>>{
        let bytes = load_program("examples/countdown.ir")?;
        let prog = parse(&bytes)?;
        let mut cycles = ExecStats { allocs: 0, calls: 0, fast_alu_ops: 0, slow_alu_ops: 0, phis: 0, conditional_branches: 0, unconditional_branches: 0, mem_reads: 0, mem_writes: 0, prints: 0, rets: 0 };
        let result = run_prog(&prog, false, &mut cycles, ExecMode::Unlimited);
        assert_eq!(result,Ok(VirtualVal::Data { val: 0 }));
        Ok(())
    }
    #[test]
    fn check_basicoo() -> Result<(),Box<dyn std::error::Error>>{
        let bytes = load_program("examples/basicoo.ir")?;
        let prog = parse(&bytes)?;
        let mut cycles = ExecStats { allocs: 0, calls: 0, fast_alu_ops: 0, slow_alu_ops: 0, phis: 0, conditional_branches: 0, unconditional_branches: 0, mem_reads: 0, mem_writes: 0, prints: 0, rets: 0 };
        let result = run_prog(&prog, false, &mut cycles, ExecMode::Unlimited);
        assert_eq!(result,Ok(VirtualVal::Data { val: 3 }));
        Ok(())
    }
    #[test]
    fn check_gctest1() -> Result<(),Box<dyn std::error::Error>>{
        let bytes = load_program("examples/gctest1.ir")?;
        let prog = parse(&bytes)?;
        let mut cycles = ExecStats { allocs: 0, calls: 0, fast_alu_ops: 0, slow_alu_ops: 0, phis: 0, conditional_branches: 0, unconditional_branches: 0, mem_reads: 0, mem_writes: 0, prints: 0, rets: 0 };
        let result = run_prog(&prog, false, &mut cycles, ExecMode::GC { limit: 100 });
        assert_eq!(result,Ok(VirtualVal::Data { val: 0 }));
        Ok(())
    }
    #[test]
    fn check_gctest2() -> Result<(),Box<dyn std::error::Error>>{
        let bytes = load_program("examples/gctest2.ir")?;
        let prog = parse(&bytes)?;
        let mut cycles = ExecStats { allocs: 0, calls: 0, fast_alu_ops: 0, slow_alu_ops: 0, phis: 0, conditional_branches: 0, unconditional_branches: 0, mem_reads: 0, mem_writes: 0, prints: 0, rets: 0 };
        let result = run_prog(&prog, false, &mut cycles, ExecMode::GC { limit: 100 });
        assert_eq!(result,Ok(VirtualVal::Data { val: 0 }));
        Ok(())
    }
    #[test]
    fn check_gctest3() -> Result<(),Box<dyn std::error::Error>>{
        let bytes = load_program("examples/gctest3.ir")?;
        let prog = parse(&bytes)?;
        let mut cycles = ExecStats { allocs: 0, calls: 0, fast_alu_ops: 0, slow_alu_ops: 0, phis: 0, conditional_branches: 0, unconditional_branches: 0, mem_reads: 0, mem_writes: 0, prints: 0, rets: 0 };
        let result = run_prog(&prog, false, &mut cycles, ExecMode::GC { limit: 100 });
        assert_eq!(result,Ok(VirtualVal::Data { val: 4096 }));
        Ok(())
    }
}
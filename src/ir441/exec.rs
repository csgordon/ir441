

use std::fmt;
use std::collections::{HashMap,BTreeMap};

use crate::ir441::nodes::*;

#[derive(Debug,PartialEq)]
pub enum RuntimeError<'a> {
    NYI,
    BadCallArity { instr: &'a IRStatement<'a> },
    CallingNonCode,
    WriteToImmutableData,
    NullPointer,
    UnalignedAccess { addr: u64 },
    UnallocatedAddressRead { addr: u64 },
    UnallocatedAddressWrite { addr: u64 },
    UninitializedVariable { name: &'a str },
    MissingMain,
    UndefinedVariable,
    UndefinedGlobal { name: &'a str },
    CodeAddressArithmetic { bname: &'a str },
    AccessingCodeInMemory { bname: &'a str },
    InvalidBlock { bname: &'a str },
    InvalidBlockInControl { instr: &'a ControlXfer<'a>, bname: &'a str },
    PhiInFirstBlock { instr: &'a IRStatement<'a> },
    BadPhiPredecessor { instr: &'a IRStatement<'a>, actual_predecessor: &'a str }
}


// Memory is a map from u64 to u64. Lookup will fail for unaligned accesses for now
type Memory<'a> = BTreeMap<u64,VirtualVal<'a>>;
type Locals<'a> = HashMap<&'a str, VirtualVal<'a>>;
type Globals<'a> = HashMap<&'a str, u64>;
fn mem_lookup<'a>(m:&Memory<'a>, addr:u64) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    if addr == 0 {
        Err(RuntimeError::NullPointer)
    } else if addr % 8 == 0 {
        match m.get(&addr) {
            None => Err(RuntimeError::UnallocatedAddressRead { addr }),
            Some(&v) => Ok(v)
        }
    } else {
        Err(RuntimeError::UnalignedAccess { addr })
    }
}
fn mem_store<'a>(m:&mut Memory<'a>, first_writable:u64, addr:u64, val:VirtualVal<'a>) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    if addr == 0 {
        Err(RuntimeError::NullPointer)
    } else if addr < first_writable {
        Err(RuntimeError::WriteToImmutableData)
    } else if addr % 8 == 0 {
        match m.get(&addr) {
            None => Err(RuntimeError::UnallocatedAddressWrite { addr }),
            Some(_) => { Ok(m.insert(addr, val).unwrap()) }
        }
    } else {
        Err(RuntimeError::UnalignedAccess { addr })
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
    let mut next_free : u64 = 32;
    let mut m : Memory = BTreeMap::new();
    let mut globs : Globals = HashMap::new();

    for g in prog.globals.iter() {
        let GlobalStatic::Array { name: n, vals: vs } = g;
        globs.insert(n, next_free);
        for v in vs.iter() {
            m.insert(next_free, v.clone());
            next_free = next_free + 8;
        }
    }

    (next_free,m,globs)
}
fn print_memory<'a>(first_mutable: u64, _prog: &'a IRProgram, m: &'a Memory<'a>, globs: &'a Globals<'a>) {
    println!("Global Addresses:");
    for (name,addr) in globs.iter() {
        println!("\t@{} -> {}", name, addr)
    }
    println!("Memory Contents:");
    let mut split_globals = false;
    for (addr,val) in m.iter() {
        if !split_globals && *addr > first_mutable {
            println!("\t---------------- <end of globals, start of mutable memory>");
            split_globals = true;
        }
        println!("\t{}: {}", addr, val);
    }
}

#[derive(Debug,PartialEq)]
pub struct ExecStats {
    // + - & | << >> ^ and also register copies
    pub fast_alu_ops: u64,
    // * /
    pub slow_alu_ops: u64,
    pub conditional_branches: u64,
    pub unconditional_branches: u64,
    // Currently we'll "ammortize" argument passing into a general call cost
    pub calls: u64,
    pub rets: u64,
    pub mem_reads: u64,
    pub mem_writes: u64,
    // TODO: In the future we may want to track sizes of individual allocations
    pub allocs: u64,
    // Recall: we only print ints, not strings, so it's fixed-cost
    pub prints: u64,
    pub phis: u64
}
impl ExecStats {
    fn fast_op(&mut self) {
        self.fast_alu_ops = self.fast_alu_ops + 1
    }
    fn slow_op(&mut self) {
        self.slow_alu_ops = self.slow_alu_ops + 1
    }
    fn cond(&mut self) {
        self.conditional_branches = self.conditional_branches + 1
    }
    fn uncond(&mut self) {
        self.unconditional_branches = self.unconditional_branches + 1
    }
    fn call(&mut self) {
        self.calls = self.calls + 1
    }
    fn ret(&mut self) {
        self.rets = self.rets + 1
    }
    fn read(&mut self) {
        self.mem_reads = self.mem_reads + 1
    }
    fn write(&mut self) {
        self.mem_writes = self.mem_writes + 1
    }
    fn alloc(&mut self) {
        self.allocs = self.allocs + 1
    }
    fn print(&mut self) {
        self.prints = self.prints + 1
    }
    fn phi(&mut self) {
        self.phis = self.phis + 1
    }
}

fn expr_val<'a>(l:&Locals<'a>, globs:&Globals<'a>, prog:&IRProgram<'a>, e:&IRExpr<'a>) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    // TODO need globals and program to detect invalid block and global references,
    // and to map global names to locations
    match e {
        IRExpr::IntLit { val: v } => Ok(VirtualVal::Data { val: u64::from(*v) }),
        // TODO: for now we assume we have infinite registers, so this is "constant"
        IRExpr::Var { id: n } => read_var(l, n),
        IRExpr::BlockRef { bname: b } =>
            match prog.blocks.get(b) {
                None => Err(RuntimeError::InvalidBlock { bname: b}),
                Some(_) => Ok(VirtualVal::CodePtr { val: b } )
            },
        IRExpr::GlobalRef { name: n } => { 
            match globs.get(n) {
                None => Err(RuntimeError::UndefinedGlobal { name: n }),
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
                m: &mut Memory<'a>,
                tracing: bool,
                mut cycles: &mut ExecStats
            ) -> Result<VirtualVal<'a>,RuntimeError<'a>> {
    // on entry no previous block
    let mut prevblock : Option<&'a str> = None;
    let mut finalresult = None;
    while let None = finalresult {
        for i in cur_block.instrs.iter() {
            if tracing {
                println!("Executing: {}", i);
            }
            let _step =
            match i {
                IRStatement::Print { out: e } => {
                    let v = expr_val(&locs, &globs, &prog, &e)?;
                    println!("{}",v);
                    cycles.print();
                    Ok(())
                },
                IRStatement::Alloc { lhs: v, slots: n } => {
                    // reserve n addresses at 8-byte offsets from next alloc
                    *next_alloc = *next_alloc + 8; // Skip 8 bytes to catch some memory errors
                    let result = *next_alloc;
                    let mut allocd = 0;
                    while allocd < *n {
                        // Must insert directly to side-step allocation checks
                        m.insert(*next_alloc, VirtualVal::Data { val: 0 });
                        *next_alloc = *next_alloc + 8;
                        allocd = allocd + 1;
                    }
                    cycles.alloc();
                    set_var(&mut locs, v, VirtualVal::Data { val: result })
                },
                IRStatement::VarAssign { lhs: var, rhs: e } => {
                    let v = expr_val(&locs, &globs, &prog, &e)?;
                    cycles.fast_op();
                    set_var(&mut locs, var, v)
                },
                IRStatement::Phi { lhs: dest, opts } => {
                    if prevblock.is_none() {
                        return Err(RuntimeError::PhiInFirstBlock { instr: i });
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
                    cycles.phi();
                    if done {
                        Ok(())
                    } else {
                        Err(RuntimeError::BadPhiPredecessor { instr: i, actual_predecessor: pred })
                    }
                },
                IRStatement::Call { lhs: dest, code, receiver: rec, args } => {
                    let mut calleevars = HashMap::new();
                    let vcode = expr_val(&locs, &globs, &prog, &code)?;
                    let target_block_name = match vcode {
                        VirtualVal::CodePtr { val: b } => Ok(b),
                        VirtualVal::Data { .. } => Err(RuntimeError::CallingNonCode)
                    }?;
                    let target_block = match prog.blocks.get(target_block_name) {
                        Some(b) => Ok(b),
                        None => Err(RuntimeError::InvalidBlock { bname: target_block_name })
                    }?;
                    let vrec = expr_val(&locs, &globs, &prog, &rec)?;
                    set_var(&mut calleevars, target_block.formals[0], vrec)?;
                    if args.len() + 1 != target_block.formals.len() {
                        return Err(RuntimeError::BadCallArity { instr: i });
                    }
                    // args are in left-to-right order. Receiver is idx 0.
                    let mut argidx = 1;
                    for arg in args.iter() {
                        let varg = expr_val(&locs, &globs, &prog, &arg)?;
                        set_var(&mut calleevars, target_block.formals[argidx], varg)?;
                        argidx = argidx + 1;
                    }
                    cycles.call();
                    let callresult = run_code(prog, target_block, calleevars, globs, next_alloc, mut_mem_start, m, tracing, &mut cycles)?;
                    set_var(&mut locs, dest, callresult)
                },
                IRStatement::SetElt { base, offset: off, val: v } => {
                    let vbase = expr_val(&locs, &globs, &prog, &base)?;
                    let offv = expr_val(&locs, &globs, &prog, &off)?;
                    let v = expr_val(&locs, &globs, &prog, &v)?;
                    match vbase {
                        VirtualVal::CodePtr { val: b } => Err(RuntimeError::AccessingCodeInMemory { bname: b }),
                        VirtualVal::Data { val: n } => 
                            match offv {
                                // TODO: should be different error
                                VirtualVal::CodePtr { val: offb } => Err(RuntimeError::AccessingCodeInMemory { bname: offb }),
                                VirtualVal::Data { val: offset } => {
                                    cycles.slow_op(); // multiplication
                                    cycles.fast_op(); // addition
                                    cycles.write(); // memory access
                                    mem_store(m, mut_mem_start, n+(8*offset), v).map(|_| ())
                                }
                            }
                    }
                },
                IRStatement::GetElt { lhs: dest, base: e, offset: off } => {
                    let v = expr_val(&locs, &globs, &prog, &e)?;
                    let offv = expr_val(&locs, &globs, &prog, &off)?;
                    match v {
                        VirtualVal::CodePtr { val: b } => Err(RuntimeError::AccessingCodeInMemory { bname: b }),
                        VirtualVal::Data { val: n } => 
                            match offv {
                                // TODO: should be different error
                                VirtualVal::CodePtr { val: offb } => Err(RuntimeError::AccessingCodeInMemory { bname: offb }),
                                VirtualVal::Data { val: offset } => {
                                    cycles.slow_op(); // multiplication
                                    cycles.fast_op(); // addition
                                    cycles.read(); // memory access
                                    let mval = mem_lookup(&m, n+(8*offset))?;
                                    set_var(&mut locs, dest, mval)
                                }
                            }
                    }
                },
                IRStatement::Load { lhs: dest, base: e } => {
                    let v = expr_val(&locs, &globs, &prog, &e)?;
                    match v {
                        VirtualVal::CodePtr { val: b } => Err(RuntimeError::AccessingCodeInMemory { bname: b }),
                        VirtualVal::Data { val: n } => {
                            cycles.read(); // memory access
                            let memval = mem_lookup(&m, n)?;
                            set_var(&mut locs, dest, memval)
                        }
                    }
                },
                IRStatement::Store { base: e, val: ve } => {
                    let bv = expr_val(&locs, &globs, &prog, &e)?;
                    let vv = expr_val(&locs, &globs, &prog, &ve)?;
                    match bv {
                        VirtualVal::CodePtr { val: b } => Err(RuntimeError::AccessingCodeInMemory { bname: b }),
                        VirtualVal::Data { val: n } => {
                            cycles.write(); // memory access
                            mem_store(m, mut_mem_start, n, vv).map(|_| ())
                        }
                    }
                },
                IRStatement::Op { lhs: v, arg1: e1, op: o, arg2: e2} => {
                    let v1 = expr_val(&locs, &globs, &prog, &e1)?;
                    let v2 = expr_val(&locs, &globs, &prog, &e2)?;
                    match (v1,v2) {
                        (VirtualVal::CodePtr{ val: b },_) => Err(RuntimeError::CodeAddressArithmetic { bname: b}),
                        (_,VirtualVal::CodePtr{ val: b }) => Err(RuntimeError::CodeAddressArithmetic { bname: b}),
                        (VirtualVal::Data { val: n1 }, VirtualVal::Data { val: n2 }) => 
                            // We've ruled out computing with code addresses, which we don't plan to allow
                            match *o {
                                "+"  => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1+n2 }) },
                                "<<" => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1<<n2 }) },
                                ">>" => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1>>n2 }) },
                                "-"  => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1-n2 }) },
                                "/"  => { cycles.slow_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1/n2 }) },
                                "*"  => { cycles.slow_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1*n2 }) },
                                "&"  => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1&n2 }) },
                                "|"  => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1|n2 }) },
                                "^"  => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: n1^n2 }) },
                                "<"  => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: if n1<n2 { 1 } else {0} }) },
                                ">"  => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: if n1>n2 {1} else {0} }) },
                                "==" => { cycles.fast_op(); set_var(&mut locs, v, VirtualVal::Data { val: if n1==n2 {1} else {0}}) },
                                _ => Err(RuntimeError::NYI) 
                            }
                        
                    }
                },
            }?;
        }
        if tracing {
            println!("Transfering via: {}", &cur_block.next);
        }
        match &cur_block.next {
            ControlXfer::Fail {reason: r} => { panic!("Failure: {:?}", r )},
            ControlXfer::Ret { val: e } => {
                let result = expr_val(&locs, &globs, &prog, &e)?;
                cycles.ret();
                finalresult = Some(result);
            },
            ControlXfer::Jump { block: b } => {
                let target_block = match prog.blocks.get(b) {
                        Some(b) => Ok(b),
                        None => Err(RuntimeError::InvalidBlockInControl { instr: &cur_block.next, bname: b })
                }?;
                cycles.uncond();
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
                let target_block = match prog.blocks.get(target_block_name) {
                        Some(b) => Ok(b),
                        None => Err(RuntimeError::InvalidBlockInControl { instr: &cur_block.next, bname: target_block_name })
                }?;
                cycles.cond();
                prevblock = Some(cur_block.name);
                cur_block = target_block;
            }
        }
    }
    Ok(finalresult.unwrap())
}
pub fn run_prog<'a>(prog: &'a IRProgram, tracing: bool, mut cycles: &mut ExecStats) -> Result<VirtualVal<'a>,RuntimeError<'a>> {

    let main = prog.blocks.get("main");
    if main.is_none() {
        return Err(RuntimeError::MissingMain);
    }
    let cur_block = main.unwrap();
    let (mut_mem_start, mut m, mut globs) = init_memory(prog);
    if tracing {
        println!("Initial Globals:\n{:?}", globs);
    }
    // mut_mem_start is the starting allocation point, but more importantly is also the dividing line between read-only and writable memory, so we can warn about invalid writes to RO mem
    let mut next_alloc = mut_mem_start;
    // Run main with an empty variable
    let fresult = run_code(prog, cur_block, HashMap::new(), &mut globs, &mut next_alloc, mut_mem_start, &mut m, tracing, &mut cycles);
    match &fresult {
        Ok(v) => {
            println!("Final result: {:?}", v);
        },
        Err(err) => {
            println!("Program crashed with: {:?}", err);
            print_memory(mut_mem_start, prog, &m, &globs);
        }
    };
    fresult
}
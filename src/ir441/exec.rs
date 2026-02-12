use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use crate::ir441::nodes::*;

#[derive(Debug, PartialEq)]
pub enum ExecMode {
    Unlimited,
    MemCap { limit: u64 },
    GC { limit: u64 },
    LoggingGC { limit: u64 },
}
impl ExecMode {
    fn effective_cap(&self) -> u64 {
        match self {
            ExecMode::Unlimited => u64::MAX,
            ExecMode::MemCap { limit } => *limit,
            ExecMode::GC { limit } => *limit,
            ExecMode::LoggingGC { limit } => *limit,
        }
    }
    fn is_gc(&self) -> bool {
        match self {
            ExecMode::GC { .. } => true,
            ExecMode::LoggingGC { .. } => true,
            _ => false,
        }
    }
    fn is_logging_gc(&self) -> bool {
        match self {
            ExecMode::LoggingGC { .. } => true,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum RuntimeError<'a> {
    AccessingCodeInMemory {
        bname: &'a str,
    },
    AccessingDeallocatedAddress {
        addr: u64,
    },
    BadCallArity {
        instr: &'a IRStatement<'a>,
    },
    BadGCField,
    BadPhiPredecessor {
        instr: &'a IRStatement<'a>,
        actual_predecessor: &'a str,
    },
    CallingNonCode,
    CodeAddressArithmetic {
        bname: &'a str,
    },
    CorruptGCMetadata {
        val: VirtualVal<'a>,
    },
    GCRequired,
    InvalidBlock {
        bname: &'a str,
    },
    InvalidBlockInControl {
        instr: &'a ControlXfer<'a>,
        bname: &'a str,
    },
    MissingMain,
    NullPointer,
    OutOfMemory,
    PhiInFirstBlock {
        instr: &'a IRStatement<'a>,
    },
    UnalignedAccess {
        addr: u64,
    },
    UnallocatedAddressRead {
        addr: u64,
    },
    UnallocatedAddressWrite {
        addr: u64,
    },
    UninitializedVariable {
        name: &'a str,
    },
    UndefinedGlobal {
        name: &'a str,
    },
    ReadFromGCedData,
    WriteToGCedData {
        addr: u64,
        val: VirtualVal<'a>,
    },
    WriteToImmutableData,
    NYI,
}

// Memory is a map from u64 to u64. Lookup will fail for unaligned accesses for now
struct Memory<'a> {
    /// Underlying storage for memory
    map: BTreeMap<u64, VirtualVal<'a>>,
    /// First address in the current allocation space
    base: u64,
    /// First address of mutable (i.e., non-read-only) memory. Anything below this is considered an immutable global
    first_writable: u64,
    /// Next unallocated address
    next_alloc: u64,
    /// Optionally, a limit on how many slots can be allocated
    slot_cap: ExecMode,
    /// How many slots *are* allocated in the current allocation space
    slots_alloced: u64,
    /// Allocated object addresses, used to filter GC roots without a stack map.
    /// This does result in semi-conservative GC since we can occasionally mistake an int for a valid pointer, but it's unlikely to persist beyond a single GC cycle.
    allocations: HashSet<u64>,
    /// Optional debug information tracking field names for each offset
    fieldnames: Option<Vec<&'a str>>,
    /// Optional class table information
    classmeta: Option<Vec<(&'a str, &'a str, &'a str)>>,
}
type Locals<'a> = HashMap<&'a str, VirtualVal<'a>>;
type Globals<'a> = HashMap<&'a str, u64>;

impl<'a> Memory<'a> {
    // Okay, a little weird for this to also allocate the globals, but whatever
    fn new(prog: &'a IRProgram, slot_cap: ExecMode) -> (Memory<'a>, Globals<'a>) {
        let mut next_free: u64 = 32;
        let mut m: BTreeMap<u64, VirtualVal<'a>> = BTreeMap::new();
        let mut globs: Globals = HashMap::new();
        let mut classdata: Option<Vec<(&str, &str, &str)>> = None;
        let mut fieldinfo: Option<Vec<&str>> = None;

        for g in prog.globals.iter() {
            match g {
                GlobalStatic::Array { name: n, vals: vs } => {
                    if *n == "_" {
                        panic!("Globals may not be named '_'")
                    }
                    globs.insert(n, next_free);
                    for v in vs.iter() {
                        m.insert(next_free, v.clone());
                        next_free = next_free + 8;
                    }
                }
                GlobalStatic::DebugFieldNames { names } => {
                    fieldinfo = Some((*names).clone());
                }
                GlobalStatic::DebugClassMeta { classinfo } => {
                    classdata = Some((*classinfo).clone());
                }
            }
        }

        let mem = Memory {
            map: m,
            first_writable: next_free,
            base: next_free,
            next_alloc: next_free,
            slot_cap,
            slots_alloced: 0,
            allocations: HashSet::new(),
            classmeta: classdata,
            fieldnames: fieldinfo,
        };
        (mem, globs)
    }

    fn gc(&mut self, stack: &mut Vec<Locals<'a>>) -> Result<(), RuntimeError<'a>> {
        if !self.slot_cap.is_gc() {
            panic!("Error: GC triggered in a mode where GC header is not allocated!");
        } else if self.slot_cap.is_logging_gc() {
            println!("Beginning GC")
        }
        // Simple copying collector.
        // Hard limit of 64 slots (including vtbl) due to width of slotmap
        // TODO: Hmm, I need *all* locals... I need this to handle stuff from earlier stack frames....
        let new_base = self.next_alloc;
        let was_alloced = self.slots_alloced;
        // Snapshot old allocations and clear them for the next GC
        let old_allocations = self.allocations.clone();
        self.allocations.clear();
        self.allocations = HashSet::new();
        self.slots_alloced = 0;
        for locals in stack.iter_mut() {
            for (x, v) in locals.iter_mut() {
                if self.slot_cap.is_logging_gc() {
                    println!("Tracing from root: {}={}", x, v);
                }
                match v {
                    VirtualVal::CodePtr { .. } => (),
                    VirtualVal::Data { val } => {
                        if old_allocations.contains(val) {
                            let newloc = self.trace(*val)?;
                            if self.slot_cap.is_logging_gc() {
                                println!("Moved {} from {} to {}", x, val, newloc);
                            }
                            *v = VirtualVal::Data { val: newloc };
                            self.allocations.insert(newloc);
                        } else {
                            if self.slot_cap.is_logging_gc() {
                                println!(
                                    "Skipping {}={} b/c it does not appear to be a valid allocation",
                                    x, val
                                );
                            }
                        }
                    }
                    VirtualVal::GCTombstone => {
                        panic!("Found GCTombstone in local variable slot: %{}", x)
                    }
                }
            }
        }
        // After relocating, wipe everything from the old base to the start of the new "semispace" with tombstones for debugging
        // TODO: Eventually, actually remove these and adjust lookup to automatically return tombstone for anything in the GC'ed range (i.e., between first_writable and )
        for loc in (self.base..new_base).step_by(8) {
            self.map.insert(loc, VirtualVal::GCTombstone);
        }
        self.base = new_base;
        if self.slot_cap.is_logging_gc() {
            println!(
                "Updated semispace base to {}, next alloc at {}",
                self.base, self.next_alloc
            );
            println!(
                "Reduced memory consumption from {} to {} slots",
                was_alloced, self.slots_alloced
            );
        }
        Ok(())
    }
    fn reserve(&mut self, slots_including_metadata: u64) -> Result<u64, RuntimeError<'a>> {
        if self.slots_alloced + slots_including_metadata > self.slot_cap.effective_cap() {
            return Err(RuntimeError::OutOfMemory);
        }
        let metadata_base = self.next_alloc;
        for i in 0..slots_including_metadata {
            self.map
                .insert(metadata_base + i * 8, VirtualVal::Data { val: 0 });
        }
        self.next_alloc = self.next_alloc + slots_including_metadata * 8;
        self.slots_alloced = self.slots_alloced + slots_including_metadata;
        Ok(metadata_base)
    }
    // We're going to optimistically assume for now that we won't blow the stack by just doing this recursively;
    // probably fine for the scope of programs students write in this course
    fn trace(&mut self, addr: u64) -> Result<u64, RuntimeError<'a>> {
        let allocsize_loc = addr - 3 * 8;
        let fwd_ptr_loc = addr - 2 * 8;
        let slotmap_loc = addr - 8;
        if self.slot_cap.is_logging_gc() {
            println!("GC Tracing of {}", addr);
        }
        match self.map.get(&fwd_ptr_loc) {
            None => Err(RuntimeError::UnallocatedAddressRead { addr }),
            Some(VirtualVal::Data { val }) => {
                if self.slot_cap.is_logging_gc() {
                    println!("Found address {} forwarded to {}", addr, val);
                }
                if *val != 0 {
                    assert!(self.map.contains_key(val));
                    Ok(*val)
                } else {
                    // Need to trace and move
                    let allocsizev = *self
                        .map
                        .get(&allocsize_loc)
                        .ok_or_else(|| RuntimeError::UnallocatedAddressRead { addr })?;
                    let allocsize = allocsizev
                        .as_u64_or_else(|v| RuntimeError::CorruptGCMetadata { val: *v })?;
                    let slotmapv = *self
                        .map
                        .get(&slotmap_loc)
                        .ok_or_else(|| RuntimeError::UnallocatedAddressRead { addr })?;
                    let mut slotmap =
                        slotmapv.as_u64_or_else(|v| RuntimeError::CorruptGCMetadata { val: *v })?;
                    if self.slot_cap.is_logging_gc() {
                        println!(
                            "Tracing {} with alloc size {} and slotmap {:X}",
                            addr, allocsize, slotmap
                        );
                    }
                    let new_metadata_loc = self.reserve(allocsize)?;
                    self.mem_store(new_metadata_loc, allocsizev)?;
                    // Set new forwarding pointer to 0
                    self.mem_store(new_metadata_loc + 8, VirtualVal::Data { val: 0 })?;
                    self.mem_store(new_metadata_loc + 16, slotmapv)?;
                    // Compute new program address for object's moved version
                    let new_obj_base = new_metadata_loc + 24;
                    // Set forwarding pointer
                    self.mem_store(fwd_ptr_loc, VirtualVal::Data { val: new_obj_base })?;
                    // Iterate through the fields and slot map in parallel
                    for i in 0..(allocsize - 3) {
                        // recursively copy or trace from addr[i] to new_obj_base[i]
                        let orig = self.mem_lookup(addr + i * 8)?;
                        if slotmap & 0x1 == 1 {
                            // trace
                            let to_trace = match orig {
                                VirtualVal::GCTombstone => {
                                    Err(RuntimeError::CorruptGCMetadata { val: orig })
                                }
                                VirtualVal::CodePtr { .. } => Err(RuntimeError::BadGCField),
                                VirtualVal::Data { val: trace_val } => Ok(trace_val),
                            }?;
                            if to_trace != 0 {
                                let moved_to = self.trace(to_trace)?;
                                self.mem_store(
                                    new_obj_base + i * 8,
                                    VirtualVal::Data { val: moved_to },
                                )?;
                                if self.slot_cap.is_logging_gc() {
                                    println!("Rewrote slot {} from {} to {}", i, orig, moved_to);
                                }
                            }
                            // No else for the 0 case is necessary, as slots are initialized to 0
                        } else {
                            // blind copy
                            self.mem_store(new_obj_base + i * 8, orig)?;
                        }
                        slotmap = slotmap >> 1;
                    }
                    Ok(new_obj_base)
                }
            }
            Some(v) => Err(RuntimeError::CorruptGCMetadata { val: *v }),
        }
    }
    fn alloc(&mut self, n: u64) -> Result<u64, RuntimeError<'a>> {
        if self.slot_cap != ExecMode::Unlimited
            && self.slots_alloced + n + 1 > self.slot_cap.effective_cap()
        {
            match self.slot_cap {
                ExecMode::Unlimited => return Ok(0), // unreachable since we checked it's not unlimited
                ExecMode::MemCap { .. } => return Err(RuntimeError::OutOfMemory),
                ExecMode::GC { .. } => return Err(RuntimeError::GCRequired),
                ExecMode::LoggingGC { .. } => return Err(RuntimeError::GCRequired),
            }
        } else {
            if self.slot_cap.is_logging_gc() {
                println!(
                    "Alloc'ing {} slots on top of {} with cap {}",
                    n,
                    self.slots_alloced,
                    self.slot_cap.effective_cap()
                );
            }
        }

        // Skip 8 bytes to catch some memory errors
        self.next_alloc = self.next_alloc + 8;
        if self.slot_cap != ExecMode::Unlimited {
            // Reserve GC header space
            // Technically unnecessary when running with limits but without GC
            self.map
                .insert(self.next_alloc, VirtualVal::Data { val: n + 3 });
            self.map
                .insert(self.next_alloc + 8, VirtualVal::Data { val: 0 });
            self.map
                .insert(self.next_alloc + 16, VirtualVal::Data { val: 0 });
            self.next_alloc = self.next_alloc + 24;
            self.slots_alloced = self.slots_alloced + 3;
        }
        let result = self.next_alloc;
        let mut allocd = 0;
        while allocd < n {
            // Must insert directly to side-step allocation checks
            self.map
                .insert(self.next_alloc, VirtualVal::Data { val: 0 });
            self.next_alloc = self.next_alloc + 8;
            allocd = allocd + 1;
        }
        self.slots_alloced = self.slots_alloced + allocd;
        self.allocations.insert(result);
        Ok(result)
    }

    fn mem_lookup(&mut self, addr: u64) -> Result<VirtualVal<'a>, RuntimeError<'a>> {
        if addr == 0 {
            Err(RuntimeError::NullPointer)
        } else if addr >= self.first_writable && addr < self.base {
            Err(RuntimeError::ReadFromGCedData)
        } else if addr % 8 == 0 {
            match self.map.get(&addr) {
                None => Err(RuntimeError::UnallocatedAddressRead { addr }),
                Some(VirtualVal::GCTombstone) => {
                    Err(RuntimeError::AccessingDeallocatedAddress { addr })
                }
                Some(&v) => Ok(v),
            }
        } else {
            Err(RuntimeError::UnalignedAccess { addr })
        }
    }

    fn mem_store(
        &mut self,
        addr: u64,
        val: VirtualVal<'a>,
    ) -> Result<VirtualVal<'a>, RuntimeError<'a>> {
        if addr == 0 {
            Err(RuntimeError::NullPointer)
        } else if addr < self.first_writable {
            Err(RuntimeError::WriteToImmutableData)
        } else if addr < self.base {
            Err(RuntimeError::WriteToGCedData { addr, val })
        } else if addr % 8 == 0 {
            match self.map.get(&addr) {
                None => Err(RuntimeError::UnallocatedAddressWrite { addr }),
                Some(VirtualVal::GCTombstone) => {
                    Err(RuntimeError::AccessingDeallocatedAddress { addr })
                }
                Some(_) => Ok(self.map.insert(addr, val).unwrap()),
            }
        } else {
            Err(RuntimeError::UnalignedAccess { addr })
        }
    }

    fn print(&self, _prog: &'a IRProgram, globs: &'a Globals<'a>) {
        println!("Global Addresses:");
        let mut global_allocs_map = BTreeMap::new();
        for (name, addr) in globs.iter() {
            println!("\t@{} -> {}", name, addr);
            global_allocs_map.insert(*addr, *name);
        }
        let mut global_allocs: VecDeque<&str> = global_allocs_map.into_values().collect();

        // Build type information
        let mut offset_to_field: HashMap<usize, &str> = HashMap::new();
        if let Some(fieldnames) = &self.fieldnames {
            for (off, fname) in fieldnames.iter().enumerate() {
                offset_to_field.insert(off, *fname);
            }
        }
        let mut classinfo = HashMap::new();
        if let Some(classdata) = &self.classmeta {
            for (cname, vtname, fmname) in classdata {
                if let Some(vtable_addr) = globs.get(*vtname) {
                    // Found the vtable. May or may not have a field map.
                    let mut offsetmap = None;
                    if *fmname != "_" {
                        let mut map = HashMap::new();
                        // TODO: Restructure the global representation as a map instead of a vector
                        for g in &_prog.globals {
                            if let GlobalStatic::Array { name, vals } = g
                                && *name == *fmname
                            {
                                for (index, field_offset) in vals.iter().enumerate() {
                                    if field_offset.as_u64().unwrap() != 0 {
                                        map.insert(
                                            field_offset.as_u64().unwrap(),
                                            offset_to_field.get(&index).unwrap(),
                                        );
                                    }
                                }
                                break;
                            }
                        }
                        offsetmap = Some(map);
                    }
                    classinfo.insert(*vtable_addr, (*cname, offsetmap, *fmname));
                } else {
                    eprintln!(
                        "Warning: Could not find vtable named {} to match debug info for class {}",
                        *vtname, *cname
                    );
                }
            }
        }

        println!("Memory Contents:");
        let mut split_globals = false;
        let mut split_gcspace = false;
        let mut last_object_base: u64 = 0;
        let mut last_object_field_info = &None;
        let mut last_object_fmap_name = None;
        for (addr, val) in self.map.iter() {
            if !split_globals && *addr > self.first_writable {
                println!("\t---------------- <end of globals, start of mutable memory>");
                split_globals = true;
            }
            if !split_gcspace && *addr > self.base {
                println!(
                    "\t---------------- <end of GC'ed memory, start of current \"semispace\">"
                );
                split_gcspace = true;
            }

            let valwidth: usize = 20; // TODO: calculate based on longest block name

            // Printing cells of the last global, the vecdeque is empty
            if *addr <= self.first_writable && global_allocs.len() > 0 {
                if let Some(v) = globs.get(global_allocs.get(0).unwrap())
                    && *v == *addr
                {
                    println!("    Start of global '{}'", global_allocs.get(0).unwrap());
                    global_allocs.pop_front();
                }
            }

            // Note: We pre-format! the value so that printf's alignment works --- alignment is apparently a property
            // of the type being formatted, so by converting to a string first we ensure we can align
            if let VirtualVal::CodePtr { .. } = val {
                println!(
                    "\t{}: {:.>valwidth$}\t(Block/code pointer)",
                    addr,
                    format!("{}", val)
                );
            } else if let VirtualVal::Data { val: v } = val
                && let Some((cname, finfo, fmname)) = classinfo.get(v)
            {
                println!(
                    "\t{}: {:.>valwidth$}\t(Object header for class '{}')",
                    addr,
                    format!("{}", val),
                    *cname
                );
                last_object_base = *addr;
                last_object_field_info = finfo;
                last_object_fmap_name = Some(*fmname);
            } else if let VirtualVal::Data { val: v } = val
                && last_object_base == *addr - 8
            {
                if let Some(fmname) = last_object_fmap_name {
                    // If running with field maps, this is the fieldmap.
                    if fmname == "_" {
                        // No field map, print normally
                        println!("\t{}: {:.>valwidth$}", addr, format!("{}", val));
                    } else {
                        // Field maps exist
                        if let Some(fmap_addr) = globs.get(fmname)
                            && fmap_addr == v
                        {
                            println!(
                                "\t{}: {:.>valwidth$}\t(field map {})",
                                addr,
                                format!("{}", val),
                                fmname
                            );
                        } else {
                            println!(
                                "\t{}: {:.>valwidth$}\t(*should* be field map {}, but appears corrupted)",
                                addr,
                                format!("{}", val),
                                fmname
                            );
                        }
                    }
                } else {
                    panic!(
                        "Inconsistent data structures: empty last_object_fmap_name despite non-trivial last_object_base {}",
                        last_object_base
                    );
                }
            } else if let VirtualVal::Data { val: v } = val
                && let Some(reverse_fmap) = last_object_field_info
                && let Some(&fname) = reverse_fmap.get(&((addr - last_object_base) / 8))
            {
                // Not an object header, but we have current object info and the field name
                println!(
                    "\t{}: {:.>valwidth$}\t(.{})",
                    addr,
                    format!("{}", val),
                    *fname
                );
            } else {
                // No class info for this
                println!(
                    "\t{}: {:.>valwidth$}\t(No debugging info available!)",
                    addr,
                    format!("{}", val)
                );
            }
        }
    }
}

fn read_var<'a>(l: &Locals<'a>, v: &'a str) -> Result<VirtualVal<'a>, RuntimeError<'a>> {
    match l.get(v) {
        Some(&x) => Ok(x),
        None => Err(RuntimeError::UninitializedVariable { name: v }),
    }
}
fn set_var<'a>(
    l: &mut Locals<'a>,
    x: &'a str,
    val: VirtualVal<'a>,
) -> Result<(), RuntimeError<'a>> {
    l.insert(x, val);
    Ok(())
}

#[derive(Debug, PartialEq)]
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
    pub phis: u64,
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
    pub fn new() -> ExecStats {
        ExecStats {
            allocs: 0,
            calls: 0,
            fast_alu_ops: 0,
            slow_alu_ops: 0,
            phis: 0,
            conditional_branches: 0,
            unconditional_branches: 0,
            mem_reads: 0,
            mem_writes: 0,
            prints: 0,
            rets: 0,
        }
    }
}

fn expr_val<'a>(
    l: &Locals<'a>,
    globs: &Globals<'a>,
    prog: &IRProgram<'a>,
    e: &IRExpr<'a>,
) -> Result<VirtualVal<'a>, RuntimeError<'a>> {
    // TODO need globals and program to detect invalid block and global references,
    // and to map global names to locations
    match e {
        IRExpr::IntLit { val: v } => Ok(VirtualVal::Data { val: u64::from(*v) }),
        // TODO: for now we assume we have infinite registers, so this is "constant"
        IRExpr::Var { id: n } => read_var(l, n),
        IRExpr::BlockRef { bname: b } => match prog.blocks.get(b) {
            None => Err(RuntimeError::InvalidBlock { bname: b }),
            Some(_) => Ok(VirtualVal::CodePtr { val: b }),
        },
        IRExpr::GlobalRef { name: n } => match globs.get(n) {
            None => Err(RuntimeError::UndefinedGlobal { name: n }),
            Some(v) => Ok(VirtualVal::Data { val: v.clone() }),
        },
    }
}

// Run one basic block's function to completion. We abuse the Rust stack to encode the target code stack, so don't be on tail call optimization in interpreted code.
fn run_code<'a>(
    prog: &'a IRProgram<'a>,
    entry_block: &'a BasicBlock<'a>,
    locs: &mut Vec<Locals<'a>>,
    globs: &mut Globals<'a>,
    m: &mut Memory<'a>,
    tracing: bool,
    memdump: bool,
    mut cycles: &mut ExecStats,
) -> Result<VirtualVal<'a>, RuntimeError<'a>> {
    let mut cur_block = entry_block;
    let localsindex = locs.len() - 1;
    // on entry no previous block
    let mut prevblock: Option<&'a str> = None;
    let mut finalresult = None;
    let mut phi_updates = Locals::new();
    while let None = finalresult {
        for i in cur_block.instrs.iter() {
            if tracing {
                println!("Executing: {}", i);
            }
            // Phi nodes are evaluated "simultaneously," so we cache phi updates in a separate map.
            // Since phi nodes must appear consecutively at the start of a block, as soon as we hit a non-phi node we drain any pending phi node updates
            if !i.is_phi() && !phi_updates.is_empty() {
                for (var, val) in &phi_updates {
                    set_var(&mut locs[localsindex], var, val.clone())?;
                }
                phi_updates.clear();
            }
            let _step = match i {
                IRStatement::Print { out: e } => {
                    let v = expr_val(&locs[locs.len() - 1], &globs, &prog, &e)?;
                    println!("{}", v);
                    cycles.print();
                    Ok(())
                }
                IRStatement::Alloc { lhs: v, slots: n } => {
                    let result = m.alloc((*n).into());
                    if result.is_ok() {
                        cycles.alloc();
                        set_var(
                            &mut locs[localsindex],
                            v,
                            VirtualVal::Data {
                                val: result.unwrap(),
                            },
                        )
                    } else if result == Err(RuntimeError::GCRequired) {
                        // GC, then try again
                        if m.slot_cap.is_logging_gc() {
                            println!("Triggering GC");
                        }
                        m.gc(locs)?;
                        let result = m.alloc((*n).into());
                        match result {
                            Err(RuntimeError::GCRequired) => Err(RuntimeError::OutOfMemory),
                            Err(_) => result.map(|_| ()),
                            Ok(result) => {
                                set_var(
                                    &mut locs[localsindex],
                                    v,
                                    VirtualVal::Data { val: result },
                                )?;
                                Ok(())
                            }
                        }
                    } else {
                        result.map(|_| ())
                    }
                }
                IRStatement::VarAssign { lhs: var, rhs: e } => {
                    let v = expr_val(&locs[locs.len() - 1], &globs, &prog, &e)?;
                    cycles.fast_op();
                    set_var(&mut locs[localsindex], var, v)
                }
                IRStatement::Phi { lhs: dest, opts } => {
                    if prevblock.is_none() {
                        return Err(RuntimeError::PhiInFirstBlock { instr: i });
                    }
                    let pred = prevblock.unwrap();
                    let mut done = false;
                    for (bname, src) in opts {
                        if pred.eq(*bname) {
                            let v = expr_val(&locs[locs.len() - 1], &globs, &prog, &src)?;
                            //set_var(&mut locs[localsindex], &dest, v)?;
                            // Defer update until all phis are evaluated (i.e., eval simultaneously)
                            phi_updates.insert(&dest, v);
                            done = true;
                            break;
                        }
                    }
                    cycles.phi();
                    if done {
                        Ok(())
                    } else {
                        Err(RuntimeError::BadPhiPredecessor {
                            instr: i,
                            actual_predecessor: pred,
                        })
                    }
                }
                IRStatement::Call {
                    lhs: dest,
                    code,
                    receiver: rec,
                    args,
                } => {
                    let mut calleevars = HashMap::new();
                    let vcode = expr_val(&locs[locs.len() - 1], &globs, &prog, &code)?;
                    let target_block_name = match vcode {
                        VirtualVal::CodePtr { val: b } => Ok(b),
                        VirtualVal::Data { .. } => Err(RuntimeError::CallingNonCode),
                        VirtualVal::GCTombstone { .. } => Err(RuntimeError::CallingNonCode),
                    }?;
                    let target_block = match prog.blocks.get(target_block_name) {
                        Some(b) => Ok(b),
                        None => Err(RuntimeError::InvalidBlock {
                            bname: target_block_name,
                        }),
                    }?;
                    let vrec = expr_val(&locs[locs.len() - 1], &globs, &prog, &rec)?;
                    set_var(&mut calleevars, target_block.formals[0], vrec)?;
                    if args.len() + 1 != target_block.formals.len() {
                        return Err(RuntimeError::BadCallArity { instr: i });
                    }
                    // args are in left-to-right order. Receiver is idx 0.
                    let mut argidx = 1;
                    for arg in args.iter() {
                        let varg = expr_val(&locs[locs.len() - 1], &globs, &prog, &arg)?;
                        set_var(&mut calleevars, target_block.formals[argidx], varg)?;
                        argidx = argidx + 1;
                    }
                    cycles.call();
                    locs.push(calleevars);
                    let callresult = run_code(
                        prog,
                        target_block,
                        locs,
                        globs,
                        m,
                        tracing,
                        memdump,
                        &mut cycles,
                    )?;
                    locs.pop();
                    if tracing {
                        println!(
                            "Call to {:?} returned {:?}, storing into %{:?}",
                            target_block.name, callresult, dest
                        );
                    }
                    set_var(&mut locs[localsindex], dest, callresult)
                }
                IRStatement::SetElt {
                    base,
                    offset: off,
                    val: v,
                } => {
                    let vbase = expr_val(&locs[locs.len() - 1], &globs, &prog, &base)?;
                    let offv = expr_val(&locs[locs.len() - 1], &globs, &prog, &off)?;
                    let v = expr_val(&locs[locs.len() - 1], &globs, &prog, &v)?;
                    match vbase {
                        VirtualVal::CodePtr { val: b } => {
                            Err(RuntimeError::AccessingCodeInMemory { bname: b })
                        }
                        VirtualVal::GCTombstone => {
                            Err(RuntimeError::WriteToGCedData { addr: 0, val: v })
                        }
                        VirtualVal::Data { val: n } => match offv {
                            // TODO: should be different error
                            VirtualVal::CodePtr { val: offb } => {
                                Err(RuntimeError::AccessingCodeInMemory { bname: offb })
                            }
                            VirtualVal::GCTombstone => Err(RuntimeError::ReadFromGCedData),
                            VirtualVal::Data { val: offset } => {
                                cycles.slow_op(); // multiplication
                                cycles.fast_op(); // addition
                                cycles.write(); // memory access
                                m.mem_store(n + (8 * offset), v).map(|_| ())
                            }
                        },
                    }
                }
                IRStatement::GetElt {
                    lhs: dest,
                    base: e,
                    offset: off,
                } => {
                    let v = expr_val(&locs[localsindex], &globs, &prog, &e)?;
                    let offv = expr_val(&locs[localsindex], &globs, &prog, &off)?;
                    match v {
                        VirtualVal::CodePtr { val: b } => {
                            Err(RuntimeError::AccessingCodeInMemory { bname: b })
                        }
                        VirtualVal::GCTombstone => Err(RuntimeError::ReadFromGCedData),
                        VirtualVal::Data { val: n } => match offv {
                            // TODO: should be different error
                            VirtualVal::CodePtr { val: offb } => {
                                Err(RuntimeError::AccessingCodeInMemory { bname: offb })
                            }
                            VirtualVal::GCTombstone => Err(RuntimeError::ReadFromGCedData),
                            VirtualVal::Data { val: offset } => {
                                cycles.slow_op(); // multiplication
                                cycles.fast_op(); // addition
                                cycles.read(); // memory access
                                let mval = m.mem_lookup(n + (8 * offset))?;
                                set_var(&mut locs[localsindex], dest, mval)
                            }
                        },
                    }
                }
                IRStatement::Load { lhs: dest, base: e } => {
                    let v = expr_val(&locs[locs.len() - 1], &globs, &prog, &e)?;
                    match v {
                        VirtualVal::CodePtr { val: b } => {
                            Err(RuntimeError::AccessingCodeInMemory { bname: b })
                        }
                        VirtualVal::GCTombstone => Err(RuntimeError::ReadFromGCedData),
                        VirtualVal::Data { val: n } => {
                            cycles.read(); // memory access
                            let memval = m.mem_lookup(n)?;
                            set_var(&mut locs[localsindex], dest, memval)
                        }
                    }
                }
                IRStatement::Store { base: e, val: ve } => {
                    let bv = expr_val(&locs[localsindex], &globs, &prog, &e)?;
                    let vv = expr_val(&locs[localsindex], &globs, &prog, &ve)?;
                    match bv {
                        VirtualVal::CodePtr { val: b } => {
                            Err(RuntimeError::AccessingCodeInMemory { bname: b })
                        }
                        VirtualVal::GCTombstone => {
                            Err(RuntimeError::WriteToGCedData { addr: 0, val: vv })
                        }
                        VirtualVal::Data { val: n } => {
                            cycles.write(); // memory access
                            m.mem_store(n, vv).map(|_| ())
                        }
                    }
                }
                IRStatement::Op {
                    lhs: v,
                    arg1: e1,
                    op: o,
                    arg2: e2,
                } => {
                    let v1 = expr_val(&locs[localsindex], &globs, &prog, &e1)?;
                    let v2 = expr_val(&locs[localsindex], &globs, &prog, &e2)?;
                    match (v1, v2) {
                        (VirtualVal::CodePtr { val: b }, _) => {
                            Err(RuntimeError::CodeAddressArithmetic { bname: b })
                        }
                        (_, VirtualVal::CodePtr { val: b }) => {
                            Err(RuntimeError::CodeAddressArithmetic { bname: b })
                        }
                        (VirtualVal::GCTombstone, _) => Err(RuntimeError::ReadFromGCedData),
                        (_, VirtualVal::GCTombstone) => Err(RuntimeError::ReadFromGCedData),
                        (VirtualVal::Data { val: n1 }, VirtualVal::Data { val: n2 }) =>
                        // We've ruled out computing with code addresses, which we don't plan to allow
                        {
                            match *o {
                                "+" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 + n2 },
                                    )
                                }
                                "<<" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 << n2 },
                                    )
                                }
                                ">>" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 >> n2 },
                                    )
                                }
                                "-" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 - n2 },
                                    )
                                }
                                "/" => {
                                    cycles.slow_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 / n2 },
                                    )
                                }
                                "*" => {
                                    cycles.slow_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 * n2 },
                                    )
                                }
                                "&" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 & n2 },
                                    )
                                }
                                "|" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 | n2 },
                                    )
                                }
                                "^" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data { val: n1 ^ n2 },
                                    )
                                }
                                "<" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data {
                                            val: if n1 < n2 { 1 } else { 0 },
                                        },
                                    )
                                }
                                ">" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data {
                                            val: if n1 > n2 { 1 } else { 0 },
                                        },
                                    )
                                }
                                "==" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data {
                                            val: if n1 == n2 { 1 } else { 0 },
                                        },
                                    )
                                }
                                "!=" => {
                                    cycles.fast_op();
                                    set_var(
                                        &mut locs[localsindex],
                                        v,
                                        VirtualVal::Data {
                                            val: if n1 != n2 { 1 } else { 0 },
                                        },
                                    )
                                }
                                _ => Err(RuntimeError::NYI),
                            }
                        }
                    }
                }
            }?;
        }
        if tracing {
            println!("Transfering via: {}", &cur_block.next);
        }

        // It's possible to get here with pending phi updates if the block is a series of phi nodes followed immediately by a control transfer.
        if !phi_updates.is_empty() {
            for (var, val) in &phi_updates {
                set_var(&mut locs[localsindex], var, val.clone())?;
            }
            phi_updates.clear();
        }
        match &cur_block.next {
            ControlXfer::Fail { reason: r } => {
                panic!("Failure: {:?}", r)
            }
            ControlXfer::Ret { val: e } => {
                let result = expr_val(&locs[locs.len() - 1], &globs, &prog, &e)?;
                cycles.ret();
                finalresult = Some(result);
            }
            ControlXfer::Jump { block: b } => {
                let target_block = match prog.blocks.get(b) {
                    Some(b) => Ok(b),
                    None => Err(RuntimeError::InvalidBlockInControl {
                        instr: &cur_block.next,
                        bname: b,
                    }),
                }?;
                cycles.uncond();
                prevblock = Some(cur_block.name);
                cur_block = target_block;
            }
            ControlXfer::If {
                cond,
                tblock,
                fblock,
            } => {
                let vcond = expr_val(&locs[locs.len() - 1], &globs, &prog, &cond)?;
                // TODO: Reconsider if we really want global addresses to count as true instead of errors
                let target_block_name = match vcond {
                    VirtualVal::Data { val: 0 } => fblock,
                    _ => tblock,
                };
                let target_block = match prog.blocks.get(target_block_name) {
                    Some(b) => Ok(b),
                    None => Err(RuntimeError::InvalidBlockInControl {
                        instr: &cur_block.next,
                        bname: target_block_name,
                    }),
                }?;
                cycles.cond();
                prevblock = Some(cur_block.name);
                cur_block = target_block;
            }
        }
    }
    if memdump {
        println!("Dumping memory on exit from {:?}\n", entry_block.name);
        m.print(prog, &globs);
    }
    Ok(finalresult.unwrap())
}
pub fn run_prog<'a>(
    prog: &'a IRProgram,
    tracing: bool,
    memdump: bool,
    mut cycles: &mut ExecStats,
    cap: ExecMode,
) -> Result<VirtualVal<'a>, RuntimeError<'a>> {
    let main = prog.blocks.get("main");
    if main.is_none() {
        return Err(RuntimeError::MissingMain);
    }
    let cur_block = main.unwrap();
    let (mut m, mut globs) = Memory::new(prog, cap);
    if tracing {
        println!("Initial Globals:\n{:?}", globs);
    }
    // Run main with an empty variable
    let mut stack = Vec::new();
    stack.push(HashMap::new());
    let fresult = run_code(
        prog,
        cur_block,
        &mut stack,
        &mut globs,
        &mut m,
        tracing,
        memdump,
        &mut cycles,
    );
    match &fresult {
        Ok(v) => {
            println!("Final result: {:?}", v);
        }
        Err(err) => {
            println!("Program crashed with: {:?}", err);
            m.print(prog, &globs);
        }
    };
    fresult
}

use std::collections::HashMap;
use std::fmt;

// We will model an architecture where code and data live in separate address spaces
// We don't need to have a global pointer because those actually get flattened into memory
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum VirtualVal<'a> {
    Data { val: u64 },
    CodePtr { val: &'a str },
    GCTombstone,
}
impl<'a> fmt::Display for VirtualVal<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VirtualVal::Data { val } => write!(f, "{}", val),
            VirtualVal::CodePtr { val } => write!(f, "{}", val),
            VirtualVal::GCTombstone => write!(f, "GCTombstone"),
        }
    }
}
impl<'a> VirtualVal<'a> {
    pub fn as_u64(&self) -> Option<u64> {
        match *self {
            VirtualVal::Data { val } => Some(val),
            _ => None,
        }
    }
    pub fn as_u64_or_else<E, F>(&self, f: F) -> Result<u64, E>
    where
        F: FnOnce(&VirtualVal<'a>) -> E,
    {
        match *self {
            VirtualVal::Data { val } => Ok(val),
            _ => Err(f(self)),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Reason {
    NotAPointer,
    NotANumber,
    NoSuchField,
    NoSuchMethod,
}
impl fmt::Display for Reason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reason::NotANumber => write!(f, "NotANumber"),
            Reason::NotAPointer => write!(f, "NotAPointer"),
            Reason::NoSuchField => write!(f, "NoSuchField"),
            Reason::NoSuchMethod => write!(f, "NoSuchMethod"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum IRExpr<'a> {
    IntLit { val: u64 },
    GlobalRef { name: &'a str },
    Var { id: &'a str },
    BlockRef { bname: &'a str },
}
impl<'a> fmt::Display for IRExpr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IRExpr::IntLit { val } => write!(f, "{}", val),
            IRExpr::GlobalRef { name } => write!(f, "@{}", name),
            IRExpr::BlockRef { bname } => write!(f, "{}", bname),
            IRExpr::Var { id } => write!(f, "%{}", id),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum IRStatement<'a> {
    VarAssign {
        lhs: &'a str,
        rhs: IRExpr<'a>,
    },
    Op {
        lhs: &'a str,
        arg1: IRExpr<'a>,
        op: &'a str,
        arg2: IRExpr<'a>,
    },
    Call {
        lhs: &'a str,
        code: IRExpr<'a>,
        receiver: IRExpr<'a>,
        args: Vec<IRExpr<'a>>,
    },
    Phi {
        lhs: &'a str,
        opts: Vec<(&'a str, IRExpr<'a>)>,
    },
    Alloc {
        lhs: &'a str,
        slots: u32,
    },
    Print {
        out: IRExpr<'a>,
    },
    GetElt {
        lhs: &'a str,
        base: IRExpr<'a>,
        offset: IRExpr<'a>,
    },
    SetElt {
        base: IRExpr<'a>,
        offset: IRExpr<'a>,
        val: IRExpr<'a>,
    },
    Load {
        lhs: &'a str,
        base: IRExpr<'a>,
    },
    Store {
        base: IRExpr<'a>,
        val: IRExpr<'a>,
    },
}

// Frequent question in the interpreter
impl<'a> IRStatement<'a> {
    pub fn is_phi(&self) -> bool {
        match self {
            IRStatement::Phi { .. } => true,
            _ => false,
        }
    }
}

impl<'a> fmt::Display for IRStatement<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IRStatement::VarAssign { lhs, rhs } => write!(f, "%{} = {}", lhs, rhs),
            IRStatement::Op {
                lhs,
                arg1,
                op,
                arg2,
            } => write!(f, "%{} = {} {} {}", lhs, arg1, op, arg2),
            IRStatement::Alloc { lhs, slots } => write!(f, "%{} = alloc({})", lhs, slots),
            IRStatement::Print { out } => write!(f, "print({})", out),
            IRStatement::GetElt { lhs, base, offset } => {
                write!(f, "%{} = getelt({}, {})", lhs, base, offset)
            }
            IRStatement::SetElt { base, offset, val } => {
                write!(f, "setelt({}, {}, {})", base, offset, val)
            }
            IRStatement::Load { lhs, base } => write!(f, "%{} = load({})", lhs, base),
            IRStatement::Store { base, val } => write!(f, "store({}, {})", base, val),
            IRStatement::Call {
                lhs,
                code,
                receiver,
                args,
            } => {
                write!(f, "%{} = call({}, {}", lhs, code, receiver)?;
                for elt in args {
                    write!(f, ", ")?;
                    elt.fmt(f)?;
                }
                write!(f, ")")
            }
            IRStatement::Phi { lhs, opts } => {
                let mut skip_comma = true;
                write!(f, "%{} = phi(", lhs)?;
                for (bname, src) in opts {
                    if skip_comma {
                        write!(f, "{}, ", bname)?;
                        skip_comma = false;
                    } else {
                        write!(f, ", {}, ", bname)?;
                    }
                    src.fmt(f)?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ControlXfer<'a> {
    Jump {
        block: &'a str,
    },
    If {
        cond: IRExpr<'a>,
        tblock: &'a str,
        fblock: &'a str,
    },
    Ret {
        val: IRExpr<'a>,
    },
    Fail {
        reason: Reason,
    },
}
impl<'a> fmt::Display for ControlXfer<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ControlXfer::Jump { block } => write!(f, "jump {}", block),
            ControlXfer::If {
                cond,
                tblock,
                fblock,
            } => {
                write!(f, "if ")?;
                cond.fmt(f)?;
                write!(f, " then {} else {}", tblock, fblock)
            }
            ControlXfer::Ret { val } => {
                write!(f, "ret ")?;
                val.fmt(f)
            }
            ControlXfer::Fail { reason } => {
                write!(f, "fail ")?;
                reason.fmt(f)
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct BasicBlock<'a> {
    pub name: &'a str,
    pub formals: Vec<&'a str>,
    pub instrs: Vec<IRStatement<'a>>,
    pub next: ControlXfer<'a>,
}
impl<'a> fmt::Display for BasicBlock<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.formals.len() == 0 {
            writeln!(f, "{}:", self.name)?;
        } else {
            write!(f, "{}(", self.name)?;
            let mut first = true;
            for arg in &self.formals {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
                first = false;
            }
            writeln!(f, "):")?;
        }
        for i in &self.instrs {
            write!(f, "    ")?;
            i.fmt(f)?;
            writeln!(f, "")?;
        }
        write!(f, "    ")?;
        self.next.fmt(f)?;
        writeln!(f, "")
    }
}

#[derive(Debug, PartialEq)]
pub enum GlobalStatic<'a> {
    Array {
        name: &'a str,
        vals: Vec<VirtualVal<'a>>,
    },
    DebugFieldNames {
        names: Vec<&'a str>,
    },
    DebugClassMeta {
        classinfo: Vec<(&'a str, &'a str, &'a str)>,
    },
}

#[derive(Debug, PartialEq)]
pub struct IRProgram<'a> {
    pub globals: Vec<GlobalStatic<'a>>,
    pub blocks: HashMap<&'a str, BasicBlock<'a>>,
}
impl<'a> fmt::Display for IRProgram<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (_, b) in &self.blocks {
            b.fmt(f)?;
        }
        writeln!(f, "")
    }
}

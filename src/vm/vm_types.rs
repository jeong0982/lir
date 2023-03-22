use std::{fmt, collections::HashMap};
use crate::ir;
#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct ProgramCounter(pub usize);

impl fmt::Debug for ProgramCounter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("0x{:06x}", self.0))
    }
}

impl From<ProgramCounter> for usize {
    fn from(addr: ProgramCounter) -> usize {
        addr.0
    }
}

impl From<usize> for ProgramCounter {
    fn from(pc: usize) -> Self {
        ProgramCounter(pc)
    }
}

impl ProgramCounter {
    pub fn inc(&mut self) {
        self.0 += 1;
    }
    /// Increase Self by one and return the value before the increase.
    pub fn inc_pre(&mut self) -> Self {
        let pre = *self;
        self.inc();
        pre
    }
}

/// register id -> value
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Register(pub HashMap<ir::RegisterId, u8>);

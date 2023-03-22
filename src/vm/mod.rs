mod vm_types;

use crate::ir;
use vm_types::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecTrace {
    pub logs: Vec<ExecStep>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecStep {
    pub pc: ProgramCounter,
    pub op: ir::Instruction,
    pub register: Register,
}

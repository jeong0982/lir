mod calculate_c;
mod execute;
mod vm_types;

use crate::ir;
use vm_types::*;
pub use execute::execute;

#[derive(Clone, Debug)]
pub struct ExecTrace {
    pub logs: Vec<ExecStep>,
}

#[derive(Clone, Debug)]
pub struct ExecStep {
    pub pc: ProgramCounter,
    pub op: ir::Instruction,
    pub register: RegisterMap,
}

#[inline]
pub fn sign_extension(value: u8, width: u8) -> u8 {
    let base = 1u8 << (width - 1);
    if value >= base {
        let bit_mask = -1i8 << (width as i128);
        value | bit_mask as u8
    } else {
        value
    }
}

#[inline]
pub fn trim_unnecessary_bits(value: u8, width: u8) -> u8 {
    let bit_mask = (1u8 << width) - 1;
    value & bit_mask
}

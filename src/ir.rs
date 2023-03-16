pub enum Instruction {
    LType { instr: LType },
}

pub enum LType {
    Add,
    Sub,
    Mul,
    Div,
    Xor,
    Or,
    And,
}

use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Deref;

use crate::ir::*;
use crate::opt::{opt_utils::*, FunctionPass};
use crate::*;

pub type Deadcode = FunctionPass<Repeat<DeadcodeInner>>;

#[derive(Default, Clone, Copy, Debug)]
pub struct DeadcodeInner {}

impl Optimize<FunctionDefinition> for DeadcodeInner {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let unused_alloc = unused_allocation(code);
        let mut replaces = HashMap::new();
        let mut allocation = Vec::new();
        for (i, a) in code.allocations.clone().iter().enumerate() {
            if let Some(name) = a.name() {
                if unused_alloc.contains(name) {
                } else {
                    let from = RegisterId::local(i);
                    let to = RegisterId::local(allocation.len());
                    allocation.push(a.clone());
                    replaces.insert(from, to);
                }
            }
        }
        code.allocations = allocation;
        code.walk(|operand| replace_register_id(operand, &replaces));

        let mut replaces = HashMap::<RegisterId, Operand>::new();
        let mut unused_instrs = HashSet::<RegisterId>::new();
        let mut nop_instrs = HashSet::<RegisterId>::new();
        for (bid, block) in code.blocks.clone() {
            for (i, instr) in block.instructions.iter().enumerate() {
                unused_instrs.insert(RegisterId::temp(bid, i));
                match instr.deref() {
                    Instruction::Nop => {
                        nop_instrs.insert(RegisterId::temp(bid, i));
                    }
                    Instruction::Call { .. } => {
                        unused_instrs.remove(&RegisterId::temp(bid, i));
                    }
                    Instruction::Save { .. } => {
                        unused_instrs.remove(&RegisterId::temp(bid, i));
                    }
                    _ => {}
                }
            }
        }
        for (_, block) in code.blocks.clone() {
            unused_instrs = self.find_unused_instr(&block, &unused_instrs);
        }

        let mut new_blocks = BTreeMap::new();
        let mut result = false;
        for (bid, block) in code.blocks.clone() {
            let mut new_instrs = Vec::<Named<Instruction>>::new();
            let mut new_block = block.clone();
            for (i, instr) in block.instructions.iter().enumerate() {
                let len = new_instrs.len();
                if unused_instrs.contains(&RegisterId::temp(bid, i))
                    || nop_instrs.contains(&RegisterId::temp(bid, i))
                {
                    let from = RegisterId::temp(bid, i);
                    let to = Operand::constant(Constant::unit());
                    replaces.insert(from, to);
                    result = true;
                } else {
                    if len != i {
                        let from = RegisterId::temp(bid, i);
                        let to = Operand::register(RegisterId::temp(bid, len), instr.dtype());
                        replaces.insert(from, to);
                        result = true;
                    }
                    new_instrs.push(instr.clone());
                }
            }
            new_block.instructions = new_instrs;
            new_blocks.insert(bid, new_block);
        }
        code.blocks = new_blocks;
        code.walk(|operand| replace_operands(operand, &replaces));
        result
    }
}

fn unused_allocation(code: &mut FunctionDefinition) -> HashSet<String> {
    let mut alloc = HashMap::<String, usize>::new();
    let mut alloc_name = HashMap::<usize, String>::new();
    for (i, a) in code.allocations.iter_mut().enumerate() {
        if let Some(name) = a.name() {
            alloc_name.insert(i, name.clone());
            alloc.insert(name.clone(), 0);
        }
    }
    for block in code.blocks.values() {
        let instrs = &block.instructions;
        for instr in instrs {
            match instr.deref() {
                Instruction::Save { ptr, .. } => {
                    if let Operand::Register { rid, .. } = ptr {
                        if let RegisterId::Local { aid } = rid {
                            if let Some(name) = alloc_name.get(aid) {
                                *alloc.get_mut(name).unwrap() += 1;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    let mut unused = HashSet::<String>::new();
    for (name, used) in alloc {
        if used == 0 {
            unused.insert(name);
        }
    }
    unused
}

fn get_operand(operand: &Operand) -> Option<RegisterId> {
    match operand {
        Operand::Constant(_) => None,
        Operand::Register { rid, .. } => Some(rid.clone()),
    }
}

fn get_exit_used(exit: &BlockExit) -> Vec<Option<RegisterId>> {
    match exit {
        BlockExit::Jump { arg } => {
            let mut res = Vec::<Option<RegisterId>>::new();
            arg.args.iter().for_each(|e| {
                res.push(get_operand(&e));
            });
            res
        }
        BlockExit::ConditionalJump {
            condition,
            arg_then,
            arg_else,
        } => {
            let mut res = Vec::<Option<RegisterId>>::new();
            res.push(get_operand(&condition));
            arg_then.args.iter().for_each(|e| {
                res.push(get_operand(&e));
            });
            arg_else.args.iter().for_each(|e| {
                res.push(get_operand(&e));
            });
            res
        }
        BlockExit::Return { value } => {
            let mut res = Vec::<Option<RegisterId>>::new();
            res.push(get_operand(&value));
            res
        }
        BlockExit::Unreachable => Vec::<Option<RegisterId>>::new(),
    }
}

impl DeadcodeInner {
    fn find_unused_instr(
        &self,
        block: &Block,
        unused: &HashSet<RegisterId>,
    ) -> HashSet<RegisterId> {
        let mut unused_instrs = unused.clone();

        for instr in block.clone().instructions {
            match instr.deref() {
                Instruction::Nop => (),
                Instruction::BinOp { lhs, rhs, .. } => {
                    let lhs_operand = get_operand(lhs);
                    let rhs_operand = get_operand(rhs);
                    if let Some(iid) = lhs_operand {
                        unused_instrs.remove(&iid);
                    }
                    if let Some(iid) = rhs_operand {
                        unused_instrs.remove(&iid);
                    }
                }
                Instruction::UnaryOp { operand, .. } => {
                    let op = get_operand(operand);
                    if let Some(iid) = op {
                        unused_instrs.remove(&iid);
                    }
                }
                Instruction::Save { ptr, value } => {
                    let ptr_operand = get_operand(ptr);
                    let value_operand = get_operand(value);
                    if let Some(iid) = ptr_operand {
                        unused_instrs.remove(&iid);
                    }
                    if let Some(iid) = value_operand {
                        unused_instrs.remove(&iid);
                    }
                }
                Instruction::Lookup { ptr } => {
                    let ptr_operand = get_operand(ptr);
                    if let Some(iid) = ptr_operand {
                        unused_instrs.remove(&iid);
                    }
                }
                Instruction::Call { callee, args, .. } => {
                    let callee_operand = get_operand(callee);
                    if let Some(iid) = callee_operand {
                        unused_instrs.remove(&iid);
                    }
                    for arg in args {
                        let arg_operand = get_operand(arg);
                        if let Some(iid) = arg_operand {
                            unused_instrs.remove(&iid);
                        }
                    }
                }
            }
        }
        let exit_used = get_exit_used(&block.exit);
        for u in exit_used {
            if let Some(iid) = u {
                unused_instrs.remove(&iid);
            }
        }

        unused_instrs
    }
}

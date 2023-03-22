use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::ops::Deref;

use crate::ir::*;
use crate::opt::{opt_utils::*, FunctionPass};
use crate::*;

use lang_c::ast;

pub type Gvn = FunctionPass<GvnInner>;

#[derive(Default, Clone, Copy, Debug)]
pub struct GvnInner {}

#[derive(Debug, Eq, Clone, Hash)]
enum Num {
    RegNum(i32),
    Constant(ir::Constant),
}

impl PartialEq for Num {
    fn eq(&self, other: &Num) -> bool {
        match (self, other) {
            (Self::RegNum(a), Self::RegNum(b)) => a == b,
            (Self::Constant(a), Self::Constant(b)) => a == b,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Eq)]
enum Expr {
    BinaryOp(ast::BinaryOperator, Num, Num),
    UnaryOp(ast::UnaryOperator, Num),
}

impl PartialEq for Expr {
    fn eq(&self, other: &Expr) -> bool {
        match (self, other) {
            (Self::BinaryOp(op1, lhs1, rhs1), Self::BinaryOp(op2, lhs2, rhs2)) => {
                op1 == op2 && lhs1 == lhs2 && rhs1 == rhs2
            }
            (Self::UnaryOp(op1, operand1), Self::UnaryOp(op2, operand2)) => {
                op1 == op2 && operand1 == operand2
            }
            _ => false,
        }
    }
}

impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::BinaryOp(op, l, r) => {
                op.hash(state);
                l.hash(state);
                r.hash(state);
            }
            Self::UnaryOp(op, operand) => {
                op.hash(state);
                operand.hash(state);
            }
        }
    }
}

impl Optimize<ir::FunctionDefinition> for GvnInner {
    fn optimize(&mut self, code: &mut ir::FunctionDefinition) -> bool {
        let mut register_table = HashMap::<RegisterId, Num>::new();
        let mut exp_table = HashMap::<Expr, Num>::new();
        let mut number: i32 = 1;

        let cfg = make_cfg(code);
        let reverse_cfg = reverse_cfg(&cfg);
        let domtree = Domtree::new(code.bid_init, &cfg, &reverse_cfg);

        let mut leader_table = HashMap::<BlockId, HashMap<Num, Operand>>::new();
        let mut replaces = HashMap::<RegisterId, Operand>::new();

        let mut phinode_todo = HashSet::<RegisterId>::new();
        let mut phinode_not = HashSet::<RegisterId>::new();
        let mut phinodes = HashMap::<(usize, BlockId), (Dtype, HashMap<BlockId, Operand>)>::new();

        for bid in domtree.reverse_post_order() {
            // println!("{}", bid);
            let block = some_or!(code.blocks.get(&bid), panic!("??"));
            let mut leader_table_block = HashMap::new();
            let bid_parent = domtree.parent(bid);
            if let Some(parent_bid) = bid_parent {
                // println!("parent bid: {}", parent_bid);
                if let Some(lt) = leader_table.get(&parent_bid) {
                    for (num, operand) in lt {
                        leader_table_block.insert(num.clone(), operand.clone());
                    }
                }
            }

            if let Some(prevs) = reverse_cfg.get(&bid) {
                if !prevs.is_empty() {
                    for (i, dtype) in block.clone().phinodes.iter().enumerate() {
                        let dtype = dtype.deref();
                        let register = RegisterId::arg(bid, i);
                        if let Some(num) = register_table.get(&register) {
                            if phinode_todo.contains(&register) {
                                if let Num::Constant(c) = num {
                                    let operand = ir::Operand::constant(c.clone());
                                    replaces.insert(register.clone(), operand.clone());
                                } else if let Some(operand) = leader_table_block.get(&num) {
                                    replaces.insert(register.clone(), operand.clone());
                                } else {
                                    leader_table_block.insert(
                                        num.clone(),
                                        Operand::register(register, dtype.clone()),
                                    );
                                }
                            } else {
                                let new_operand =
                                    Operand::register(register.clone(), dtype.clone());
                                number += 1;
                                let new_num = Num::RegNum(number);
                                register_table.insert(register.clone(), new_num.clone());
                                leader_table_block.insert(new_num.clone(), new_operand.clone());
                            }
                        } else {
                            let new_operand = Operand::register(register.clone(), dtype.clone());
                            number += 1;
                            let new_num = Num::RegNum(number);
                            register_table.insert(register.clone(), new_num.clone());
                            leader_table_block.insert(new_num.clone(), new_operand.clone());
                        }
                    }
                }
            }
            for (i, instr) in block.clone().instructions.iter().enumerate() {
                let register = RegisterId::temp(bid, i);
                let collector = {
                    match instr.deref() {
                        Instruction::BinOp {
                            op,
                            lhs,
                            rhs,
                            dtype,
                        } => {
                            let lhs_num = get_num(lhs, &mut register_table, &mut number);
                            let rhs_num = get_num(rhs, &mut register_table, &mut number);
                            let inner = Expr::BinaryOp(op.clone(), lhs_num, rhs_num);
                            let dtype = dtype.clone();
                            Some((inner, dtype))
                        }
                        Instruction::UnaryOp { op, operand, dtype } => {
                            let operand_num = get_num(operand, &mut register_table, &mut number);
                            let inner = Expr::UnaryOp(op.clone(), operand_num);
                            let dtype = dtype.clone();
                            Some((inner, dtype))
                        }
                        _ => None,
                    }
                };
                if let Some((inner, dtype)) = collector {
                    if let Some(num) = exp_table.get(&inner) {
                        if let Some(operand) = leader_table_block.get(num) {
                            register_table.insert(register.clone(), num.clone());
                            replaces.insert(register.clone(), operand.clone());
                        } else {
                            // if there are same exp in previous blocks, create phi node
                            let mut is_all = true;
                            if let Some(prevs) = reverse_cfg.get(&bid) {
                                let mut prev_op = HashMap::<BlockId, Operand>::new();
                                for (bid_prev, _) in prevs {
                                    if let Some(lt) = leader_table.get(bid_prev) {
                                        let op = some_or!(lt.get(num), {
                                            is_all = false;
                                            break;
                                        });
                                        prev_op.insert(*bid_prev, op.clone());
                                    } else {
                                        panic!("no previous leader table");
                                    }
                                }
                                if is_all {
                                    let index = code.blocks.get(&bid).unwrap().phinodes.len();
                                    let new_phi = Operand::register(
                                        RegisterId::arg(bid, index),
                                        dtype.clone(),
                                    );
                                    phinodes.insert((index, bid), (dtype.clone(), prev_op));
                                    leader_table_block.insert(num.clone(), new_phi.clone());
                                    code.blocks
                                        .get_mut(&bid)
                                        .unwrap()
                                        .phinodes
                                        .push(Named::new(None, dtype.clone()));
                                    replaces.insert(register.clone(), new_phi.clone());
                                } else {
                                    let new_operand =
                                        Operand::register(register.clone(), dtype.clone());
                                    let new_num = num.clone();
                                    register_table.insert(register.clone(), new_num.clone());
                                    leader_table_block.insert(new_num.clone(), new_operand.clone());
                                }
                            } else {
                                leader_table_block.insert(
                                    num.clone(),
                                    Operand::register(register.clone(), dtype.clone()),
                                );
                            }
                            // else, leader_tabel_block.insert(num.clone(), register.clone());
                        }
                    } else {
                        let new_operand = Operand::register(register.clone(), dtype.clone());
                        number += 1;
                        let new_num = Num::RegNum(number);
                        exp_table.insert(inner, new_num.clone());
                        register_table.insert(register.clone(), new_num.clone());
                        leader_table_block.insert(new_num.clone(), new_operand.clone());
                    }
                }
            }
            leader_table.insert(bid, leader_table_block.clone());
            code.blocks
                .get(&bid)
                .cloned()
                .unwrap()
                .exit
                .walk_jump_args(|arg| {
                    let bid = arg.bid;
                    for (i, operand) in arg.args.iter().enumerate() {
                        let register = RegisterId::arg(bid, i);
                        if phinode_not.contains(&register) {
                            break;
                        }
                        let op_num = get_num(operand, &mut register_table, &mut number);
                        if let Some(num) = register_table.get(&register) {
                            phinode_todo.insert(register.clone());
                            if num.clone() != op_num {
                                phinode_not.insert(register.clone());
                                phinode_todo.remove(&register);
                            }
                        } else {
                            register_table.insert(register, op_num);
                        }
                    }
                });
        }
        for ((_, bid), (_, phinode)) in &phinodes {
            for (bid_prev, operand_prev) in phinode {
                let block_prev = code.blocks.get_mut(bid_prev).unwrap();
                block_prev.exit.walk_jump_args(|arg| {
                    if &arg.bid == bid {
                        arg.args.push(operand_prev.clone());
                    }
                });
            }
        }
        if replaces.is_empty() {
            return false;
        }
        code.walk(|operand| replace_operands(operand, &replaces));
        true
    }
}

fn get_num(operand: &ir::Operand, rt: &mut HashMap<RegisterId, Num>, number: &mut i32) -> Num {
    match operand {
        Operand::Register { rid, .. } => {
            if let Some(num) = rt.get(rid) {
                num.clone()
            } else {
                let new_num = Num::RegNum(*number);
                rt.insert(rid.clone(), new_num.clone());
                let new_number = *number + 1;
                *number = new_number;
                new_num
            }
        }
        Operand::Constant(c) => Num::Constant(c.clone()),
    }
}

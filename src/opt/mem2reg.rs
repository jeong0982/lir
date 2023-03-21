use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::{Deref, DerefMut};

use crate::ir::*;
use crate::opt::{opt_utils::*, FunctionPass};
use crate::*;

pub type Mem2reg = FunctionPass<Mem2regInner>;

#[derive(Default)]
pub struct Mem2regInner {}

fn mark_inpromotable(inpromotable: &mut HashSet<usize>, op: &ir::Operand) {
    if let Operand::Register { rid, .. } = op {
        if let RegisterId::Local { aid } = rid {
            inpromotable.insert(*aid);
        }
    }
}

#[derive(Clone)]
enum OperandVar {
    Operand(ir::Operand),
    Phi((usize, ir::BlockId)),
}

impl OperandVar {
    pub fn lookup(
        &self,
        dtype: &Dtype,
        phinode_indexes: &HashMap<(usize, ir::BlockId), usize>,
    ) -> Operand {
        match self {
            Self::Operand(op) => op.clone(),
            Self::Phi((aid, bid)) => {
                if let Some(index) = phinode_indexes.get(&(*aid, *bid)) {
                    let rid = RegisterId::arg(*bid, *index);
                    Operand::register(rid, dtype.clone())
                } else {
                    Operand::constant(Constant::undef(dtype.clone()))
                }
            }
        }
    }
}

impl Optimize<FunctionDefinition> for Mem2regInner {
    #[allow(clippy::cognitive_complexity)]
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        // A local allocation is promotable only if it is used only as the pointer of store/load
        let mut inpromotable = HashSet::new();
        let mut stores = HashMap::<usize, Vec<BlockId>>::new();

        for (bid, block) in &code.blocks {
            for instr in &block.instructions {
                match instr.deref() {
                    Instruction::Nop => {}
                    Instruction::BinOp { lhs, rhs, .. } => {
                        mark_inpromotable(&mut inpromotable, &lhs);
                        mark_inpromotable(&mut inpromotable, &rhs);
                    }
                    Instruction::UnaryOp { operand, .. } => {
                        mark_inpromotable(&mut inpromotable, &operand);
                    }
                    Instruction::Save { ptr, value } => {
                        mark_inpromotable(&mut inpromotable, &value);

                        let (rid, _dtype) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            stores.entry(*aid).or_insert_with(Vec::new).push(*bid);
                        }
                    }
                    Instruction::Lookup { .. } => {}
                    Instruction::Call { callee, args, .. } => {
                        mark_inpromotable(&mut inpromotable, &callee);
                        for arg in args {
                            mark_inpromotable(&mut inpromotable, &arg);
                        }
                    }
                }
            }
        }

        if (0..code.allocations.len()).all(|i| inpromotable.contains(&i)) {
            return false;
        }

        let cfg = make_cfg(code);
        let reverse_cfg = reverse_cfg(&cfg);
        let domtree = Domtree::new(code.bid_init, &cfg, &reverse_cfg);

        let joins: HashMap<usize, HashSet<BlockId>> = stores
            .iter()
            .filter(|(aid, _)| !inpromotable.contains(*aid))
            .map(|(aid, bids)| {
                (*aid, {
                    let mut stack = bids.clone();
                    let mut visited = HashSet::new();
                    while let Some(bid) = stack.pop() {
                        let bid_frontiers = some_or!(domtree.frontiers(bid), continue);
                        for bid_frontier in bid_frontiers {
                            if visited.insert(*bid_frontier) {
                                stack.push(*bid_frontier);
                            }
                        }
                    }
                    visited
                })
            })
            .collect();

        let mut replaces = HashMap::<RegisterId, OperandVar>::new();
        let mut phinode_indexes = HashSet::<(usize, BlockId)>::new();
        let mut end_values = HashMap::<(usize, BlockId), OperandVar>::new();

        for (bid, block) in &code.blocks {
            for (i, instr) in block.instructions.iter().enumerate() {
                match instr.deref() {
                    Instruction::Save { ptr, value } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if inpromotable.contains(aid) {
                                continue;
                            }
                            end_values.insert((*aid, *bid), OperandVar::Operand(value.clone()));
                        }
                    }
                    Instruction::Lookup { ptr } => {
                        let (rid, dtype) = some_or!(ptr.get_register(), continue);
                        let dtype = match dtype {
                            Dtype::Pointer { inner, .. } => inner.deref(),
                            _ => dtype,
                        };
                        if let RegisterId::Local { aid } = rid {
                            if inpromotable.contains(aid) {
                                continue;
                            }

                            let mut bid_join_to = Some(*bid);
                            loop {
                                if let Some(bid_to) = bid_join_to {
                                    if let Some(value) = end_values.get(&(*aid, bid_to)) {
                                        replaces.insert(RegisterId::temp(*bid, i), value.clone());
                                        break;
                                    }
                                    if let Some(join) = joins.get(aid) {
                                        if join.contains(&bid_to) {
                                            phinode_indexes.insert((*aid, bid_to));
                                            let var = OperandVar::Phi((*aid, bid_to));
                                            replaces.insert(RegisterId::temp(*bid, i), var.clone());
                                            break;
                                        }
                                    }
                                    bid_join_to = domtree.parent(bid_to);
                                } else {
                                    let var = OperandVar::Operand(Operand::constant(
                                        Constant::undef(dtype.clone()),
                                    ));
                                    replaces.insert(RegisterId::temp(*bid, i), var.clone());
                                    break;
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let mut phinode_visited = phinode_indexes;
        let mut phinode_stack = phinode_visited.iter().cloned().collect::<Vec<_>>();
        let mut phinodes =
            BTreeMap::<(usize, BlockId), (Dtype, HashMap<BlockId, OperandVar>)>::new();
        while let Some((aid, bid)) = phinode_stack.pop() {
            let mut cases = HashMap::new();
            let prevs = some_or!(reverse_cfg.get(&bid), continue);
            for (bid_prev, _) in prevs {
                let mut bid_prev_join_to = Some(*bid_prev);
                let mut bid_prev_join = *bid_prev;
                while let Some(bid_to) = bid_prev_join_to {
                    if let Some(_value) = end_values.get(&(aid, bid_to)) {
                        bid_prev_join = bid_to;
                        break;
                    }
                    if let Some(join) = joins.get(&aid) {
                        if join.contains(&bid_to) {
                            bid_prev_join = bid_to;
                            break;
                        }
                    }
                    bid_prev_join_to = domtree.parent(bid_to);
                }
                let end_value_prev_join = end_values.get(&(aid, bid_prev_join)).cloned();
                let var = end_values.entry((aid, *bid_prev)).or_insert_with(|| {
                    end_value_prev_join.unwrap_or_else(|| {
                        if phinode_visited.insert((aid, bid_prev_join)) {
                            phinode_stack.push((aid, bid_prev_join));
                        }
                        OperandVar::Phi((aid, bid_prev_join))
                    })
                });
                cases.insert(*bid_prev, var.clone());
            }

            phinodes.insert(
                (aid, bid),
                (code.allocations.get(aid).unwrap().deref().clone(), cases),
            );
        }

        let mut phinode_indexes = HashMap::<(usize, BlockId), usize>::new();

        for ((aid, bid), (dtype, _)) in &phinodes {
            let name = code.allocations.get(*aid).unwrap().name();
            let block = code.blocks.get_mut(bid).unwrap();
            let index = block.phinodes.len();
            block
                .phinodes
                .push(Named::new(name.cloned(), dtype.clone()));

            phinode_indexes.insert((*aid, *bid), index);
        }

        for ((aid, bid), (dtype, phinode)) in &phinodes {
            let index = *phinode_indexes.get(&(*aid, *bid)).unwrap();
            for (bid_prev, operand_prev) in phinode {
                let block_prev = code.blocks.get_mut(bid_prev).unwrap();
                let operand_prev = operand_prev.lookup(dtype, &phinode_indexes);
                block_prev.exit.walk_jump_args(|arg| {
                    if &arg.bid == bid {
                        assert_eq!(arg.args.len(), index);
                        arg.args.push(operand_prev.clone());
                    }
                });
            }
        }
        
        if replaces.is_empty() {
            return false;
        }

        code.walk(|operand| {
            let (rid, dtype) = some_or!(operand.get_register(), return);
            let operand_var = some_or!(replaces.get(rid), return);
            let mut new_operand = operand_var.lookup(dtype, &phinode_indexes);
            loop {
                if let Some((rid, dtype)) = &new_operand.get_register() {
                    if let Some(new_operand_var) = replaces.get(rid) {
                        new_operand = new_operand_var.lookup(dtype, &phinode_indexes);
                    } else {
                        *operand = new_operand;
                        break;
                    }
                } else {
                    *operand = new_operand;
                    break;
                }
            }
        });

        for block in code.blocks.values_mut() {
            for instr in block.instructions.iter_mut() {
                match instr.deref().deref() {
                    Instruction::Save { ptr, .. } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if !inpromotable.contains(aid) {
                                *instr.deref_mut() = Instruction::Nop;
                            }
                        }
                    }
                    Instruction::Lookup { ptr } => {
                        let (rid, _) = some_or!(ptr.get_register(), continue);
                        if let RegisterId::Local { aid } = rid {
                            if !inpromotable.contains(aid) {
                                *instr.deref_mut() = Instruction::Nop;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        true
    }
}

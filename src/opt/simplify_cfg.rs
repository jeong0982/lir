use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Deref;

use crate::ir::*;
use crate::opt::{FunctionPass, Optimize, opt_utils::*};
use crate::*;
use itertools::izip;

pub type SimplifyCfg = FunctionPass<
    Repeat<(
        SimplifyCfgConstProp,
        (SimplifyCfgReach, (SimplifyCfgMerge, SimplifyCfgEmpty)),
    )>,
>;

/// Simplifies block exits by propagating constants.
#[derive(Default)]
pub struct SimplifyCfgConstProp {}

/// Retains only those blocks that are reachable from the init.
#[derive(Default)]
pub struct SimplifyCfgReach {}

/// Merges two blocks if a block is pointed to only by another
#[derive(Default)]
pub struct SimplifyCfgMerge {}

/// Removes empty blocks
#[derive(Default)]
pub struct SimplifyCfgEmpty {}

impl Optimize<FunctionDefinition> for SimplifyCfgConstProp {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        code.blocks
            .iter_mut()
            .map(|(_, block)| {
                if let Some(exit) = self.simplify_block_exit(&block.exit) {
                    block.exit = exit;
                    true
                } else {
                    false
                }
            })
            .fold(false, |l, r| l || r)
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgReach {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let graph = make_cfg(code);

        let mut queue = vec![code.bid_init];
        let mut visited = HashSet::new();
        visited.insert(code.bid_init);
        while let Some(bid) = queue.pop() {
            if let Some(args) = graph.get(&bid) {
                for arg in args {
                    if visited.insert(arg.bid) {
                        queue.push(arg.bid);
                    }
                }
            }
        }
        let size_orig = code.blocks.len();
        let mut new_block = BTreeMap::new();
        for (bid, block) in code.blocks.clone().iter_mut() {
            if visited.contains(&bid) {
                new_block.insert(*bid, block.clone());
            }
        }
        code.blocks = new_block;
        code.blocks.len() < size_orig
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgMerge {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let graph = make_cfg(code);

        let mut indegrees = BTreeMap::<BlockId, usize>::new();
        for args in graph.values() {
            for arg in args {
                *indegrees.entry(arg.bid).or_insert(0) += 1;
            }
        }

        let mut result = false;

        let mut new_blocks = BTreeMap::new();
        let mut done_blocks = BTreeMap::<BlockId, bool>::new();
        let old_blocks = code.blocks.clone();
        for (bid_from, block_from) in &mut code.blocks {
            if done_blocks.get(&bid_from) == Some(&true) {
                continue;
            } else if let BlockExit::Jump { .. } = &block_from.exit {
                let mut new_block = block_from.clone();
                while let BlockExit::Jump { arg } = new_block.exit.clone() {
                    if *bid_from != arg.bid && indegrees.get(&arg.bid) == Some(&1) {
                        if let Some(block) = old_blocks.get(&arg.bid) {
                            let block_to = block.clone();
                            let bid_to = arg.bid;
                            let args_to = arg.args.clone();
                            let mut replaces = HashMap::new();

                            for (i, (a, p)) in izip!(&args_to, block_to.phinodes.iter()).enumerate()
                            {
                                assert_eq!(&a.dtype(), p.deref());
                                let from = RegisterId::arg(bid_to, i);
                                replaces.insert(from, a.clone());
                                result = true;
                            }
                            let len = new_block.instructions.len();

                            for (i, instr) in block_to.instructions.into_iter().enumerate() {
                                let dtype = instr.dtype();
                                new_block.instructions.push(instr);
                                let from = RegisterId::temp(arg.bid, i);
                                let to = Operand::register(
                                    RegisterId::temp(*bid_from, len + i),
                                    dtype.clone(),
                                );
                                result = true;
                                replaces.insert(from, to);
                            }
                            new_block.exit = block_to.exit.clone();
                            new_block.walk(|operand| replace_operands(operand, &replaces));
                            done_blocks.insert(arg.bid, true);
                        }
                    } else {
                        break;
                    }
                }
                new_blocks.insert(*bid_from, new_block);
                done_blocks.insert(*bid_from, true);
            } else {
                let block = block_from.clone();
                new_blocks.insert(*bid_from, block);
            }
        }

        code.blocks = new_blocks;
        result
    }
}

impl Optimize<FunctionDefinition> for SimplifyCfgEmpty {
    fn optimize(&mut self, code: &mut FunctionDefinition) -> bool {
        let empty_blocks = code
            .blocks
            .iter()
            .filter(|(_, block)| block.phinodes.is_empty() && block.instructions.is_empty())
            .map(|(bid, block)| (*bid, block.clone()))
            .collect::<BTreeMap<_, _>>();

        code.blocks
            .iter_mut()
            .map(|(_, block)| self.simplify_block_exit(&mut block.exit, &empty_blocks))
            .fold(false, |l, r| l || r)
    }
}

impl SimplifyCfgConstProp {
    fn simplify_block_exit(&self, exit: &BlockExit) -> Option<BlockExit> {
        match exit {
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                if arg_then == arg_else {
                    return Some(BlockExit::Jump {
                        arg: arg_then.deref().clone(),
                    });
                }
                if let Some(c) = condition.get_constant() {
                    match c {
                        Constant::Int { value: 0, .. } => {
                            return Some(BlockExit::Jump {
                                arg: arg_else.deref().clone(),
                            })
                        }
                        Constant::Int { value: _, .. } => {
                            return Some(BlockExit::Jump {
                                arg: arg_then.deref().clone(),
                            })
                        }
                        _ => {}
                    }
                }

                None
            }
            _ => None,
        }
    }
}

impl SimplifyCfgEmpty {
    fn simplify_jump_arg(
        &self,
        arg: &mut JumpArg,
        empty_blocks: &BTreeMap<BlockId, Block>,
    ) -> bool {
        let block = some_or!(empty_blocks.get(&arg.bid), return false);

        assert!(arg.args.is_empty());

        if let BlockExit::Jump { arg: a } = &block.exit {
            *arg = a.clone();
            true
        } else {
            false
        }
    }

    fn simplify_block_exit(
        &self,
        exit: &mut BlockExit,
        empty_blocks: &BTreeMap<BlockId, Block>,
    ) -> bool {
        match exit {
            BlockExit::Jump { arg } => {
                let block = some_or!(empty_blocks.get(&arg.bid), return false);
                *exit = block.exit.clone();
                true
            }
            BlockExit::ConditionalJump {
                arg_then, arg_else, ..
            } => {
                let changed1 = self.simplify_jump_arg(arg_then, empty_blocks);
                let changed2 = self.simplify_jump_arg(arg_else, empty_blocks);
                changed1 || changed2
            }
            BlockExit::Return { .. } | BlockExit::Unreachable => false,
        }
    }
}

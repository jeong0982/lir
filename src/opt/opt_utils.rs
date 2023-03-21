use crate::ir::*;
use crate::*;
use core::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Deref;

pub trait Walk {
    fn walk<F>(&mut self, f: F)
    where
        F: FnMut(&mut Operand) -> ();
}

impl Walk for FunctionDefinition {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand) -> (),
    {
        self.blocks
            .iter_mut()
            .for_each(|(_, block)| block.walk(&mut f));
    }
}

impl Walk for BTreeMap<BlockId, Block> {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand) -> (),
    {
        self.iter_mut().for_each(|(_, block)| block.walk(&mut f));
    }
}

impl Walk for Block {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand) -> (),
    {
        self.instructions.iter_mut().for_each(|i| i.walk(&mut f));
        self.exit.walk(&mut f);
    }
}

impl Walk for Instruction {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand) -> (),
    {
        match self {
            Self::Nop => (),
            Self::BinOp { lhs, rhs, .. } => {
                lhs.walk(&mut f);
                rhs.walk(&mut f);
            }
            Self::UnaryOp { operand, .. } => operand.walk(&mut f),
            Self::Save { ptr, value } => {
                ptr.walk(&mut f);
                value.walk(&mut f);
            }
            Self::Lookup { ptr } => ptr.walk(&mut f),
            Self::Call { callee, args, .. } => {
                callee.walk(&mut f);
                args.iter_mut().for_each(|a| a.walk(&mut f));
            }
        }
    }
}

impl Walk for BlockExit {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand) -> (),
    {
        match self {
            Self::Jump { arg } => arg.walk(&mut f),
            Self::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => {
                condition.walk(&mut f);
                arg_then.walk(&mut f);
                arg_else.walk(&mut f);
            }
            Self::Return { value } => value.walk(&mut f),
            Self::Unreachable => (),
        }
    }
}

impl Walk for JumpArg {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand) -> (),
    {
        self.args.iter_mut().for_each(|a| a.walk(&mut f));
    }
}

impl Walk for Operand {
    fn walk<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut Operand) -> (),
    {
        f(self);
    }
}

pub fn replace_operand(operand: &mut Operand, from: &Operand, to: &Operand) -> bool {
    if operand == from {
        *operand = to.clone();
        true
    } else {
        false
    }
}

pub fn replace_operands(operand: &mut Operand, to: &HashMap<RegisterId, Operand>) {
    match operand {
        Operand::Constant(_) => (),
        Operand::Register { rid, .. } => {
            let op_option = to.get(rid);
            if let Some(op) = op_option {
                *operand = op.clone();
            }
        }
    }
}

pub fn replace_register_id(operand: &mut Operand, to: &HashMap<RegisterId, RegisterId>) {
    match operand {
        Operand::Constant(_) => (),
        Operand::Register { rid, dtype } => {
            let rid_option = to.get(rid);
            if let Some(new_rid) = rid_option {
                *operand = Operand::register(new_rid.clone(), dtype.clone());
            }
        }
    }
}

pub fn make_cfg(fdef: &FunctionDefinition) -> BTreeMap<BlockId, Vec<JumpArg>> {
    let mut result = BTreeMap::new();

    for (bid, block) in &fdef.blocks {
        let mut args = Vec::new();
        match &block.exit {
            BlockExit::Jump { arg } => args.push(arg.clone()),
            BlockExit::ConditionalJump {
                arg_then, arg_else, ..
            } => {
                args.push(arg_then.deref().clone());
                args.push(arg_else.deref().clone());
            }
            _ => {}
        }
        result.insert(*bid, args);
    }
    result
}

pub fn reverse_cfg(
    cfg: &BTreeMap<BlockId, Vec<JumpArg>>,
) -> BTreeMap<BlockId, Vec<(BlockId, JumpArg)>> {
    let mut result = BTreeMap::new();

    for (bid, jumps) in cfg {
        for jump in jumps {
            result
                .entry(jump.bid)
                .or_insert_with(Vec::new)
                .push((*bid, jump.clone()));
        }
    }
    result
}

struct PostOrder<'c> {
    visited: HashSet<BlockId>,
    cfg: &'c BTreeMap<BlockId, Vec<JumpArg>>,
    traversed: Vec<BlockId>,
}

impl<'c> PostOrder<'c> {
    fn traverse(&mut self, bid: BlockId) {
        for jump in self.cfg.get(&bid).unwrap() {
            if self.visited.insert(jump.bid) {
                self.traverse(jump.bid);
            }
        }
        self.traversed.push(bid);
    }
}

fn traverse_post_order(bid_init: BlockId, cfg: &BTreeMap<BlockId, Vec<JumpArg>>) -> Vec<BlockId> {
    let mut post_order = PostOrder {
        visited: HashSet::new(),
        cfg,
        traversed: Vec::new(),
    };
    post_order.visited.insert(bid_init);
    post_order.traverse(bid_init);
    post_order.traversed
}

#[derive(Debug)]
pub struct Domtree {
    parent: HashMap<BlockId, BlockId>,
    frontiers: HashMap<BlockId, Vec<BlockId>>,
    reverse_post_order: Vec<BlockId>,
}

impl Domtree {
    pub fn new(
        bid_init: BlockId,
        cfg: &BTreeMap<BlockId, Vec<JumpArg>>,
        reverse_cfg: &BTreeMap<BlockId, Vec<(BlockId, JumpArg)>>,
    ) -> Self {
        let mut reverse_post_order = traverse_post_order(bid_init, cfg);
        reverse_post_order.reverse();

        let inverse_reverse_post_order = reverse_post_order
            .iter()
            .enumerate()
            .map(|(i, bid)| (*bid, i))
            .collect();

        let mut parent = HashMap::<BlockId, BlockId>::new();

        loop {
            let mut changed = false;

            for bid in &reverse_post_order {
                if *bid == bid_init {
                    continue;
                }

                let mut idom = None;
                for (bid_prev, _) in reverse_cfg.get(bid).unwrap() {
                    if *bid_prev == bid_init || parent.get(bid_prev).is_some() {
                        idom = Some(intersect_idom(
                            idom,
                            *bid_prev,
                            &inverse_reverse_post_order,
                            &parent,
                        ));
                    }
                }

                if let Some(idom) = idom {
                    parent
                        .entry(*bid)
                        .and_modify(|v| {
                            if *v != idom {
                                changed = true;
                                *v = idom;
                            }
                        })
                        .or_insert_with(|| {
                            changed = true;
                            idom
                        });
                }
            }
            if !changed {
                break;
            }
        }

        let mut frontiers = HashMap::new();
        for (bid, prevs) in reverse_cfg {
            if prevs.len() <= 1 {
                continue;
            }
            // let idom = *some_or!(parent.get(bid), continue);

            for (bid_prev, _) in prevs {
                let mut runner = *bid_prev;
                while !Self::dominates(&parent, runner, *bid) {
                    frontiers.entry(runner).or_insert_with(Vec::new).push(*bid);
                    // println!("runner: {}, bid: {}, parent: {}", runner, bid, idom);
                    runner = *parent.get(&runner).unwrap();
                }
            }
        }
        Self {
            parent,
            frontiers,
            reverse_post_order,
        }
    }

    pub fn parent(&self, bid: BlockId) -> Option<BlockId> {
        self.parent.get(&bid).cloned()
    }

    pub fn dominates(parent: &HashMap<BlockId, BlockId>, bid1: BlockId, mut bid2: BlockId) -> bool {
        loop {
            bid2 = *some_or!(parent.get(&bid2), return false);
            if bid1 == bid2 {
                return true;
            }
        }
    }

    pub fn reverse_post_order(&self) -> Vec<BlockId> {
        self.reverse_post_order.clone()
    }

    pub fn frontiers(&self, bid: BlockId) -> Option<&Vec<BlockId>> {
        self.frontiers.get(&bid)
    }

    pub fn walk<F>(&self, mut f: F)
    where
        F: FnMut(Option<BlockId>, BlockId),
    {
        for bid in &self.reverse_post_order {
            f(self.parent.get(bid).cloned(), *bid);
        }
    }
}

fn intersect_idom(
    lhs: Option<BlockId>,
    mut rhs: BlockId,
    inverse_reverse_post_order: &HashMap<BlockId, usize>,
    parent: &HashMap<BlockId, BlockId>,
) -> BlockId {
    let mut lhs = some_or!(lhs, return rhs);

    loop {
        if lhs == rhs {
            return lhs;
        }
        let lhs_index = inverse_reverse_post_order.get(&lhs).unwrap();
        let rhs_index = inverse_reverse_post_order.get(&rhs).unwrap();

        match lhs_index.cmp(rhs_index) {
            Ordering::Less => rhs = *parent.get(&rhs).unwrap(),
            Ordering::Greater => lhs = *parent.get(&lhs).unwrap(),
            Ordering::Equal => panic!("intersect_dom: lhs == rhs cannot happen"),
        }
    }
}

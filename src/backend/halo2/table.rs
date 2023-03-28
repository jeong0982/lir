use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, *},
    poly::Rotation,
};

use crate::backend::halo2::utils::Expr;
use crate::impl_expr;

pub trait LookupTable<F: FieldExt> {
    fn columns(&self) -> Vec<Column<Any>>;

    fn advice_columns(&self) -> Vec<Column<Advice>> {
        self.columns()
            .iter()
            .map(|&col| col.try_into())
            .filter_map(|res| res.ok())
            .collect()
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        self.columns()
            .iter()
            .map(|&column| meta.query_any(column, Rotation::cur()))
            .collect()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BinOpTag {
    ADD = 1,
    MUL,
    SUB,
    DIV,
    MOD,
    LT,
    GT,
    LE,
    GE,
    SHL,
    SHR,
    AND,
    XOR,
    OR,
    EQ,
    NOT,
}
impl_expr!(BinOpTag);

#[derive(Clone, Debug)]
pub struct BinaryOperationTable {
    pub tag: Column<Fixed>,
    pub lhs: Column<Fixed>,
    pub rhs: Column<Fixed>,
    pub res: Column<Fixed>,
}

impl BinaryOperationTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.fixed_column(),
            lhs: meta.fixed_column(),
            rhs: meta.fixed_column(),
            res: meta.fixed_column(),
        }
    }

    pub fn load<F: FieldExt>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "binop table",
            |mut region| {
                // TODO
                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug, Copy)]
pub enum UnaryOpTag {
    PLUS = 1,
    MINUS,
    NEG,
}
impl_expr!(UnaryOpTag);

#[derive(Clone, Debug)]
pub struct UnaryOperationTable {
    pub tag: Column<Fixed>,
    pub operand: Column<Fixed>,
    pub res: Column<Fixed>,
}

impl UnaryOperationTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.fixed_column(),
            operand: meta.fixed_column(),
            res: meta.fixed_column(),
        }
    }

    pub fn load<F: FieldExt>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "unaryop table",
            |mut region| {
                // TODO
                Ok(())
            },
        )
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BlockExitTag {
    JUMP = 1,
    CONDJUMP,
    RET,
}
impl_expr!(BlockExitTag);

#[derive(Clone, Debug)]
pub struct BlockExitTable {
    pub tag: Column<Fixed>,
    pub cond: Column<Fixed>,
    pub from: Column<Fixed>,
    pub to: Column<Fixed>,
}

impl BlockExitTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.fixed_column(),
            cond: meta.fixed_column(),
            from: meta.fixed_column(),
            to: meta.fixed_column(),
        }
    }

    pub fn load<F: FieldExt>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "blockexit table",
            |mut region| {
                // TODO
                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug)]
pub struct CallTable {
    pub from: Column<Fixed>,
    pub to: Column<Fixed>,
}

impl CallTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            from: meta.fixed_column(),
            to: meta.fixed_column(),
        }
    }

    pub fn load<F: FieldExt>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "blockexit table",
            |mut region| {
                // TODO
                Ok(())
            },
        )
    }
}

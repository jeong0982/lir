use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, TableColumn, *},
    poly::Rotation,
};

use crate::{backend::halo2::utils::Expr, ExecStep};
use crate::impl_expr;

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
    pub tag: TableColumn,
    pub lhs: TableColumn,
    pub rhs: TableColumn,
    pub res: TableColumn,
}

impl BinaryOperationTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.lookup_table_column(),
            lhs: meta.lookup_table_column(),
            rhs: meta.lookup_table_column(),
            res: meta.lookup_table_column(),
        }
    }

    pub fn load<F: FieldExt>(
        &self,
        layouter: &mut impl Layouter<F>,
        precomputed: Vec<[u8; 4]>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "binop table",
            |mut table| {
                for (offset, v) in precomputed.iter().enumerate() {
                    let tag = v[0] as u64;
                    let lhs = v[1] as u64;
                    let rhs = v[2] as u64;
                    let res = v[3] as u64;
                    table.assign_cell(|| "tag", self.tag, offset, || Value::known(F::from(tag)))?;
                    table.assign_cell(|| "lhs", self.lhs, offset, || Value::known(F::from(lhs)))?;
                    table.assign_cell(|| "rhs", self.rhs, offset, || Value::known(F::from(rhs)))?;
                    table.assign_cell(|| "res", self.res, offset, || Value::known(F::from(res)))?;
                }
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
    pub tag: TableColumn,
    pub operand: TableColumn,
    pub res: TableColumn,
}

impl UnaryOperationTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.lookup_table_column(),
            operand: meta.lookup_table_column(),
            res: meta.lookup_table_column(),
        }
    }

    pub fn load<F: FieldExt>(
        &self,
        layouter: &mut impl Layouter<F>,
        precomputed: Vec<[u8; 3]>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "unaryop table",
            |mut table| {
                for (offset, v) in precomputed.iter().enumerate() {
                    let tag = v[0] as u64;
                    let operand = v[1] as u64;
                    let res = v[2] as u64;
                    table.assign_cell(|| "tag", self.tag, offset, || Value::known(F::from(tag)))?;
                    table.assign_cell(
                        || "operand",
                        self.operand,
                        offset,
                        || Value::known(F::from(operand)),
                    )?;
                    table.assign_cell(|| "res", self.res, offset, || Value::known(F::from(res)))?;
                }
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
    pub tag: TableColumn,
    pub cond: TableColumn,
    pub from: TableColumn,
    pub to: TableColumn,
}

impl BlockExitTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            tag: meta.lookup_table_column(),
            cond: meta.lookup_table_column(),
            from: meta.lookup_table_column(),
            to: meta.lookup_table_column(),
        }
    }

    pub fn load<F: FieldExt>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "blockexit table",
            |mut table| {
                // TODO
                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug)]
pub struct CallTable {
    // instruction number
    pub from: TableColumn,
    // instruction number
    pub to: TableColumn,
}

impl CallTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            from: meta.lookup_table_column(),
            to: meta.lookup_table_column(),
        }
    }

    pub fn load<F: FieldExt>(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "blockexit table",
            |mut table| {
                // TODO
                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug)]
pub struct RegisterTable {
    pub index: Column<Fixed>,
    pub value: Column<Advice>,
}

impl RegisterTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            index: meta.fixed_column(),
            value: meta.advice_column(),
        }
    }

    pub fn load<F: FieldExt>(&self, layouter: &mut impl Layouter<F>, last_step: ExecStep) -> Result<(), Error> {
        layouter.assign_region(
            || "register table",
            |mut region| {
                let mut offset = 0;
                let fixed_col = [self.index];
                for register_pair in last_step.register_table_assignments::<F>().iter() {
                    self.assign(&mut region, offset, register_pair);
                    offset += 1;
                }
                Ok(())
            },
        )
    }

    fn assign<F: FieldExt>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &(Value<F>, Value<F>),
    ) -> Result<(), Error> {
        region.assign_fixed(|| "assign index", self.index, offset, || row.0)?;
        region.assign_advice(|| "assign register value", self.value, offset, || row.1)?;
        Ok(())
    }
}

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::FieldExt,
    plonk::{Circuit, ConstraintSystem, Error},
};
use std::marker::PhantomData;
mod table;
mod utils;
mod witness;

use table::*;

#[derive(Clone, Debug)]
pub struct LookupConfig<F: FieldExt> {
    binop_table: BinaryOperationTable,
    unaryop_table: UnaryOperationTable,
    blockexit_table: BlockExitTable,
    call_table: CallTable,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LookupConfig<F> {
    fn new(meta: &mut ConstraintSystem<F>) -> Self {
        let binop_table = table::BinaryOperationTable::construct(meta);
        let unaryop_table = table::UnaryOperationTable::construct(meta);
        let blockexit_table = table::BlockExitTable::construct(meta);
        let call_table = table::CallTable::construct(meta);
        Self { binop_table, unaryop_table, blockexit_table, call_table, _marker: PhantomData::default() }
    }
}

#[derive(Clone, Debug)]
pub struct LookupCircuit<F: FieldExt> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LookupCircuit<F> {
    pub fn new(
    ) -> Self {
        Self {
            _marker: PhantomData::default(),
        }
    }
}

impl<F: FieldExt> Circuit<F> for LookupCircuit<F> {
    type Config = LookupConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            _marker: PhantomData::default()
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        Self::Config::new(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        Ok(())
    }
}

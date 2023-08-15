use std::marker::PhantomData;

use super::BinaryOperationTable;
use super::RegisterTable;
use super::SubCircuit;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::FieldExt,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
};

fn generate_binop_table() -> Vec<[u8; 4]> {
    let mut all_cases = vec![];
    // TODO: for all cases
    all_cases.push([1, 1, 1, 2]);
    all_cases
}

pub struct BinOpConfig<F: FieldExt> {
    binop_table: BinaryOperationTable,
    register_table: RegisterTable,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BinOpConfig<F> {
    pub fn load_binop_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let precomputed_binop = generate_binop_table();
        self.binop_table.load(layouter, precomputed_binop)?;
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct BinOpCircuit<F: FieldExt> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SubCircuit<F> for BinOpCircuit<F> {
    type Config = BinOpConfig<F>;

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load_binop_table(layouter)?;
        Ok(())
    }
}

impl<F: FieldExt> Circuit<F> for BinOpCircuit<F> {
    type Config = BinOpConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let binop_table = BinaryOperationTable::construct(meta);
        // meta.lookup();
        // let register_table =
    }

    fn synthesize(&self, config: Self::Config, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        // config.register_table.load(&mut layouter, );
        Ok(())
    }
}

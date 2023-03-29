use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::FieldExt,
    plonk::{Circuit, ConstraintSystem, Error},
};
use std::marker::PhantomData;
mod convert;
mod table;
mod utils;
mod vm_circuit;
mod witness;

use table::*;
use utils::SubCircuit;

use crate::ExecTrace;

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

        Self {
            binop_table,
            unaryop_table,
            blockexit_table,
            call_table,
            _marker: PhantomData::default(),
        }
    }
}

fn generate_binop_table() -> Vec<[u8; 4]> {
    let mut all_cases = vec![];
    // TODO: for all cases
    all_cases.push([1, 1, 1, 2]);
    all_cases
}

fn generate_unop_table() -> Vec<[u8; 3]> {
    let mut all_cases = vec![];
    // TODO: for all cases
    all_cases.push([1, 1, 1]);
    all_cases
}

#[derive(Clone, Debug)]
pub struct LookupCircuit<F: FieldExt> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LookupCircuit<F> {
    pub fn new() -> Self {
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
            _marker: PhantomData::default(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        Self::Config::new(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let precomputed_binop = generate_binop_table();
        let precomputed_unop = generate_unop_table();
        config.binop_table.load(&mut layouter, precomputed_binop)?;
        config.unaryop_table.load(&mut layouter, precomputed_unop)?;
        config.blockexit_table.load(&mut layouter)?;
        config.call_table.load(&mut layouter)?;
        Ok(())
    }
}

impl<F: FieldExt> LookupCircuit<F> {
    // pub fn build(trace: ExecTrace) -> (u32, Self, Vec<Vec<F>>) {
    //     let circuit = LookupCircuit::new();
    // }
}

#[cfg(test)]
mod circuit_tests {
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    use crate::ExecTrace;

    // TODO

    // fn test_simple_circuit() {

    //     let prover = MockProver::run(k, &circuit, instance).unwrap();
    //     let res = prover.verify_par();
    //     if let Err(err) = res {
    //         panic!("Verification failed");
    //     }
    // }
}

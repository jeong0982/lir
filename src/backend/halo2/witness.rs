use halo2_proofs::{circuit::Value, halo2curves::FieldExt};
use itertools::Itertools;

use crate::ExecStep;

impl ExecStep {
    pub fn register_table_assignments<F: FieldExt>(&self) -> Vec<[Value<F>; 2]> {
        self.register
            .registers
            .iter()
            .enumerate()
            .map(|(i, v)| {
                [
                    Value::known(F::from(i as u64)),
                    Value::known(F::from(v.get_int().unwrap().0 as u64)),
                ]
            })
            .collect_vec()
    }
}

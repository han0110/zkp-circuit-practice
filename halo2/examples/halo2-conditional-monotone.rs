// Most codes are copied from https://github.com/zcash/orchard/blob/main/src/circuit/gadget/utilities/lookup_range_check.rs

// In this practice I try to check if values in a group are monotone increasing,
// also the gap between two rows should be within a range `R`.
// Naively I create a large enough table to load all possible gap value for
// lookup, which makes the table row very large.

// TODO: Try to split value into chunks and shrink the table row.

use halo2::{
    arithmetic::FieldExt,
    circuit::{layouter::SingleChipLayouter, Layouter},
    dev::{MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Expression, Fixed},
    poly::Rotation,
};
use zkp_example_halo2::lookup_error_at;
use std::{marker::PhantomData, usize};

#[derive(Clone, Debug)]
struct ConditionalMonotoneConfig<F: FieldExt, const R: usize> {
    // TODO: use proper padding instead of an advice selector
    q_enable: Column<Advice>,
    // key groups values which should be monotone increasing
    key: Column<Advice>,
    // auxiliary column for checking if (key - key_prev) is zero,
    // which should be (key - key_prev).invert() || F::zero()
    key_diff_inv: Column<Advice>,
    value: Column<Advice>,
    table: Column<Fixed>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const R: usize> ConditionalMonotoneConfig<F, R> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.advice_column();
        let key = meta.advice_column();
        let key_diff_inv = meta.advice_column();
        let value = meta.advice_column();
        let table = meta.fixed_column();

        let config = Self {
            q_enable,
            key,
            key_diff_inv,
            value,
            table,
            _marker: PhantomData,
        };

        meta.create_gate("advice selector validity", |meta| {
            let q_enable = meta.query_advice(config.q_enable, Rotation::cur());
            let key_cur = meta.query_advice(config.key, Rotation::cur());
            let key_prev = meta.query_advice(config.key, Rotation::prev());
            let key_diff_inv = meta.query_advice(config.key_diff_inv, Rotation::cur());

            let key_diff = key_cur - key_prev;
            let key_diff_is_zero = Expression::Constant(F::one()) - key_diff.clone() * key_diff_inv;

            vec![
                // q_enable ∈ {0, 1}
                q_enable.clone() * (Expression::Constant(F::one()) - q_enable.clone()),
                // key_diff * (1 - key_diff * key_diff_inv) === 0
                q_enable * key_diff * key_diff_is_zero,
            ]
        });

        meta.lookup(|meta| {
            let q_enable = meta.query_advice(config.q_enable, Rotation::cur());
            let key_cur = meta.query_advice(config.key, Rotation::cur());
            let key_prev = meta.query_advice(config.key, Rotation::prev());
            let key_diff_inv = meta.query_advice(config.key_diff_inv, Rotation::cur());
            let val_prev = meta.query_advice(config.value, Rotation::prev());
            let val_cur = meta.query_advice(config.value, Rotation::cur());
            let table = meta.query_fixed(config.table, Rotation::cur());

            let key_diff = key_cur - key_prev;
            let key_diff_is_zero = Expression::Constant(F::one()) - key_diff.clone() * key_diff_inv;
            let qs_lookup = q_enable * key_diff_is_zero;

            vec![(
                qs_lookup.clone() * (val_cur - val_prev)
                    + (Expression::Constant(F::one()) - qs_lookup), // default to 1 when qs_lookup is disabled
                table,
            )]
        });

        config
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "table",
            |mut region| {
                // generate range table [1, R-1]
                for idx in 0..R.next_power_of_two() {
                    let to = if idx > 0 && idx < R {
                        F::from_u64(idx as u64)
                    } else {
                        // padding with 1
                        F::one()
                    };
                    region.assign_fixed(|| "table", self.table, idx, || Ok(to))?;
                }
                Ok(())
            },
        )
    }

    fn witness_check(
        &self,
        mut layouter: impl Layouter<F>,
        values: &Option<Vec<(usize, Vec<usize>)>>,
    ) -> Result<(), Error> {
        let values = values.as_ref().ok_or(Error::SynthesisError)?;
        layouter.assign_region(
            || "witness element",
            |mut region| {
                let mut key_prev = None;
                let mut offset = 0;
                for (key, values) in values.iter() {
                    let key_diff_inv = if let Some(key_prev) = key_prev {
                        F::from_u64((*key - key_prev) as u64)
                            .invert()
                            .unwrap_or(F::zero())
                    } else {
                        F::one()
                    };
                    key_prev = Some(*key);

                    for (inner_idx, value) in values.iter().enumerate() {
                        region.assign_advice(
                            || "key",
                            self.key,
                            offset,
                            || Ok(F::from_u64(*key as u64)),
                        )?;
                        region.assign_advice(
                            || "key_diff_inv",
                            self.key_diff_inv,
                            offset,
                            || {
                                if inner_idx == 0 {
                                    Ok(key_diff_inv)
                                } else {
                                    Ok(F::zero())
                                }
                            },
                        )?;
                        region.assign_advice(
                            || "value",
                            self.value,
                            offset,
                            || Ok(F::from_u64(*value as u64)),
                        )?;
                        if offset > 0 {
                            region.assign_advice(
                                || "q_enable",
                                self.q_enable,
                                offset,
                                || Ok(F::one()),
                            )?;
                        }

                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }
}

struct TestCircuit<F: FieldExt, const R: usize> {
    values: Option<Vec<(usize, Vec<usize>)>>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const R: usize> Circuit<F> for TestCircuit<F, R> {
    type Config = ConditionalMonotoneConfig<F, R>;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ConditionalMonotoneConfig::configure(meta)
    }

    fn synthesize(&self, cs: &mut impl Assignment<F>, config: Self::Config) -> Result<(), Error> {
        let mut layouter = SingleChipLayouter::new(cs)?;

        config.load(&mut layouter)?;

        config.witness_check(layouter, &self.values)?;

        Ok(())
    }
}

fn try_test_circuit<F: FieldExt, const R: usize>(
    values: Vec<(usize, Vec<usize>)>,
) -> Result<(), Vec<VerifyFailure>> {
    let k = usize::BITS - R.leading_zeros();

    let circuit: TestCircuit<Fp, R> = TestCircuit {
        values: Some(values),
        _marker: PhantomData,
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    prover.verify()
}

fn main() {
    assert_eq!(
        try_test_circuit::<Fp, 100>(vec![
            (1, vec![1, 2, 15, 30, 129]),
            (2, vec![101, 102, 115, 130, 229]),
            (3, vec![500, 599, 698, 797, 896]),
        ]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<Fp, 100>(vec![
            (1, vec![1, 2, 15, 30, 129]),
            (2, vec![101, 101, 115, 130, 229]),
            (3, vec![500, 599, 698, 797, 896]),
        ]),
        Err(vec![lookup_error_at!(0, 6)])
    );
    assert_eq!(
        try_test_circuit::<Fp, 100>(vec![
            (1, vec![1, 2, 15, 30, 130]),
            (2, vec![101, 102, 115, 130, 229]),
            (3, vec![500, 599, 698, 797, 896]),
        ]),
        Err(vec![lookup_error_at!(0, 4)])
    );
    assert_eq!(
        try_test_circuit::<Fp, 100>(vec![
            (1, vec![1, 2, 15, 30, 129]),
            (2, vec![101, 102, 115, 130, 229]),
            (3, vec![500, 599, 698, 896, 797]),
        ]),
        Err(vec![lookup_error_at!(0, 13)
            ,
            lookup_error_at!(0, 14)
        ])
    );
}

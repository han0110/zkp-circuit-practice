// Most codes are copied from https://github.com/zcash/orchard/blob/main/src/circuit/gadget/utilities/lookup_range_check.rs

// In this practice I try to check if values in a row are monotone increasing,
// also the gap between two rows should be within a range `R`.
// Naively I create a large enough table to load all possible gap value for
// lookup, which makes the table row very large.

// TODO: Try to split value into chunks and shrink the table row.

use halo2::{
    arithmetic::FieldExt,
    circuit::{layouter::SingleChipLayouter, Layouter},
    dev::{MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{
        Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector,
    },
    poly::Rotation,
};
use std::{marker::PhantomData, usize};
use zkp_example_halo2::lookup_error_at;

#[derive(Clone, Debug)]
struct MonotoneConfig<F: FieldExt, const R: usize> {
    q_lookup: Selector,
    value: Column<Advice>,
    table: Column<Fixed>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const R: usize> MonotoneConfig<F, R> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_lookup = meta.selector();
        let value = meta.advice_column();
        let table = meta.fixed_column();

        let config = Self {
            q_lookup,
            value,
            table,
            _marker: PhantomData,
        };

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(config.q_lookup);
            let mi_prev = meta.query_advice(config.value, Rotation::prev());
            let mi_cur = meta.query_advice(config.value, Rotation::cur());
            let table = meta.query_fixed(config.table, Rotation::cur());
            vec![(
                q_lookup.clone() * (mi_cur - mi_prev) + (Expression::Constant(F::one()) - q_lookup), // default to 1 when q_lookup is disabled
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
        values: &Option<Vec<usize>>,
    ) -> Result<(), Error> {
        let values = values.as_ref().ok_or(Error::SynthesisError)?;
        layouter.assign_region(
            || "Witness element",
            |mut region| {
                for (idx, value) in values.iter().enumerate() {
                    region.assign_advice(
                        || "Witness element",
                        self.value,
                        idx,
                        || Ok(F::from_u64(*value as u64)),
                    )?;
                    // escape first row because it doesn't have Rotation::prev()
                    if idx > 0 {
                        self.q_lookup.enable(&mut region, idx)?;
                    }
                }
                Ok(())
            },
        )
    }
}

struct TestCircuit<F: FieldExt, const R: usize> {
    values: Option<Vec<usize>>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const R: usize> Circuit<F> for TestCircuit<F, R> {
    type Config = MonotoneConfig<F, R>;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MonotoneConfig::configure(meta)
    }

    fn synthesize(&self, cs: &mut impl Assignment<F>, config: Self::Config) -> Result<(), Error> {
        let mut layouter = SingleChipLayouter::new(cs)?;

        config.load(&mut layouter)?;

        config.witness_check(layouter, &self.values)?;

        Ok(())
    }
}

fn try_test_circuit<F: FieldExt, const R: usize>(
    values: Vec<usize>,
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
    assert_eq!(try_test_circuit::<Fp, 100>(vec![1, 2, 15, 30, 129]), Ok(()));
    assert_eq!(
        try_test_circuit::<Fp, 100>(vec![501, 502, 515, 530, 629]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<Fp, 100>(vec![1, 1, 15, 30, 129]),
        Err(vec![lookup_error_at!(0, 1)])
    );
    assert_eq!(
        try_test_circuit::<Fp, 100>(vec![1, 2, 15, 30, 130]),
        Err(vec![lookup_error_at!(0, 4)])
    );
    assert_eq!(
        try_test_circuit::<Fp, 100>(vec![1, 2, 15, 129, 30]),
        Err(vec![lookup_error_at!(0, 3), lookup_error_at!(0, 4)])
    );
}

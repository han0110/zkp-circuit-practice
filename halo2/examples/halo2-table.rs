use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    dev::{MockProver, VerifyFailure},
    pasta::pallas::Base,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Clone)]
struct Config {
    q: Selector,
    advice: Column<Advice>,
    table: [Column<Fixed>; 2],
}

struct TableLookupChip<F> {
    config: Config,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> TableLookupChip<F> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Config {
        let config = Config {
            q: meta.selector(),
            advice: meta.advice_column(),
            table: [0; 2].map(|_| meta.fixed_column()),
        };

        meta.lookup(|meta| {
            let q = meta.query_selector(config.q);
            let pivot = meta.query_fixed(config.table[0], Rotation::cur());
            let value = vec![0, 1, 2, 3, 4]
                .into_iter()
                .map(|rotation| meta.query_fixed(config.table[1], Rotation(rotation)))
                .fold(Expression::Constant(F::zero()), |acc, expr| acc + expr);
            let advice = meta.query_advice(config.advice, Rotation::cur());

            vec![(q.clone(), pivot), (q * advice, value)]
        });

        config
    }

    fn load_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "",
            |mut region| {
                for i in 0..20 {
                    let offset = 5 * i;

                    region.assign_fixed(|| "", self.config.table[0], offset, || Ok(F::one()))?;

                    for j in offset..offset + 5 {
                        region.assign_fixed(
                            || "",
                            self.config.table[1],
                            j,
                            || Ok(F::from_u64(j as u64)),
                        )?;
                    }
                }
                Ok(())
            },
        )
    }

    fn load_witness(&self, layouter: &mut impl Layouter<F>, values: &[F]) -> Result<(), Error> {
        layouter.assign_region(
            || "",
            |mut region| {
                for (idx, value) in values.iter().enumerate() {
                    self.config.q.enable(&mut region, idx)?;
                    region.assign_advice(|| "", self.config.advice, idx, || Ok(*value))?;
                }
                Ok(())
            },
        )
    }

    fn construct(config: Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

#[derive(Default)]
struct TestCircuit<F: FieldExt> {
    witnesses: Vec<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
    type Config = Config;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        TableLookupChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = TableLookupChip::construct(config);

        chip.load_table(&mut layouter)?;
        chip.load_witness(&mut layouter, &self.witnesses[..])?;

        Ok(())
    }
}

fn try_test_circuit(witnesses: Vec<Base>) -> Result<(), Vec<VerifyFailure>> {
    let circuit: TestCircuit<Base> = TestCircuit {
        witnesses,
        _marker: PhantomData,
    };

    let prover = MockProver::run(8, &circuit, vec![]).unwrap();
    prover.verify()
}

fn main() {
    assert_eq!(
        try_test_circuit(vec![Base::from_u64(1 + 2 + 3 + 4)]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![Base::from_u64(5 + 6 + 7 + 8 + 9)]),
        Ok(())
    );
}

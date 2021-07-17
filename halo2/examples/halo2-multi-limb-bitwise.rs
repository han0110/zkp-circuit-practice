use halo2::{
    arithmetic::FieldExt,
    circuit::{layouter::SingleChipLayouter, Layouter, Region},
    dev::{MockProver, VerifyFailure},
    pasta::pallas::Base,
    plonk::{
        Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector,
    },
    poly::Rotation,
};
use std::{array, marker::PhantomData};
use zkp_example_halo2::lookup_error_at;

#[derive(Clone, Debug)]
pub(crate) struct MultiLimbBitwiseConfig {
    pub q_enable: Selector,
    pub values: [Column<Advice>; 4],
    pub tables: [Column<Fixed>; 4],
}

pub(crate) struct MultiLimbBitwiseChip<F> {
    config: MultiLimbBitwiseConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MultiLimbBitwiseChip<F> {
    // Layout of a region (the region `load_witness` will assign)
    // +----------+---------+--------------+--------------+--------------+
    // | q_enable | advice1 |   advice2    |   advice3    |   advice4    |
    // +----------+---------+--------------+--------------+--------------+
    // |        0 | a1      | a2           | a3           | a4           |
    // |        0 | b1      | b2           | b3           | b4           |
    // |        0 | c1      | c2           | c3           | c4           |
    // |        1 | op      | inv0(op - 1) | inv0(op - 2) | inv0(op - 3) |
    // +----------+---------+--------------+--------------+--------------+
    fn configure(meta: &mut ConstraintSystem<F>) -> MultiLimbBitwiseConfig {
        let q_enable = meta.selector();
        let values = [
            meta.advice_column(), // [a1, b1, c1,           op] in a row
            meta.advice_column(), // [a1, b1, c1, inv0(op - 1)] in a row
            meta.advice_column(), // [a1, b1, c1, inv0(op - 2)] in a row
            meta.advice_column(), // [a1, b1, c1, inv0(op - 3)] in a row
        ];
        let tables = [
            meta.fixed_column(), // tag (and: 1, or: 2, xor: 3)
            meta.fixed_column(), // a
            meta.fixed_column(), // b
            meta.fixed_column(), // c
        ];

        let one = Expression::Constant(F::one());

        let is_equal =
            |target_op, op: Expression<F>, op_diff_inv| -> (Expression<F>, Expression<F>) {
                let diff = op - Expression::Constant(F::from_u64(target_op as u64));
                (diff.clone(), one.clone() - diff * op_diff_inv)
            };

        for (target_op, name) in [(1, "and gate"), (2, "or gate"), (3, "xor gate")] {
            meta.create_gate(name, |meta| {
                let q_enable = meta.query_selector(q_enable);
                let op = meta.query_advice(values[0], Rotation::cur());
                let op_diff_inv = meta.query_advice(values[target_op], Rotation::cur());

                // check op_diff_inv is valid
                let (diff, is_equal_expression) =
                    is_equal(target_op, op.clone(), op_diff_inv.clone());
                array::IntoIter::new([diff, op_diff_inv])
                    .map(move |poly| q_enable.clone() * is_equal_expression.clone() * poly)
            });

            for value in values.iter() {
                meta.lookup(|meta| {
                    let q_enable = meta.query_selector(q_enable);
                    let op = meta.query_advice(values[0], Rotation::cur());
                    let op_diff_inv = meta.query_advice(values[target_op], Rotation::cur());
                    let tag = meta.query_fixed(tables[0], Rotation::cur());
                    let ta = meta.query_fixed(tables[1], Rotation::cur());
                    let tb = meta.query_fixed(tables[2], Rotation::cur());
                    let tc = meta.query_fixed(tables[3], Rotation::cur());
                    let a = meta.query_advice(*value, Rotation(-3));
                    let b = meta.query_advice(*value, Rotation(-2));
                    let c = meta.query_advice(*value, Rotation(-1));

                    // use synthetic selector
                    let q_op_enable = q_enable * is_equal(target_op, op, op_diff_inv).1;

                    vec![
                        (
                            q_op_enable.clone()
                                * Expression::Constant(F::from_u64(target_op as u64)),
                            tag,
                        ),
                        (q_op_enable.clone() * a, ta),
                        (q_op_enable.clone() * b, tb),
                        (q_op_enable * c, tc),
                    ]
                });
            }
        }

        MultiLimbBitwiseConfig {
            q_enable,
            values,
            tables,
        }
    }

    fn load_table(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        let tags = [F::from_u64(1), F::from_u64(2), F::from_u64(3)];
        let ops = [
            |a, b| a & b, // and
            |a, b| a | b, // or
            |a, b| a ^ b, // xor
        ];
        let mut offset = offset;

        // add
        for (idx, op) in ops.iter().enumerate() {
            for a in 0..2 {
                for b in 0..2 {
                    region.assign_fixed(
                        || "table tag",
                        self.config.tables[0],
                        offset,
                        || Ok(tags[idx]),
                    )?;
                    region.assign_fixed(
                        || "table a",
                        self.config.tables[1],
                        offset,
                        || Ok(F::from_u64(a)),
                    )?;
                    region.assign_fixed(
                        || "table b",
                        self.config.tables[2],
                        offset,
                        || Ok(F::from_u64(b)),
                    )?;
                    region.assign_fixed(
                        || "table c",
                        self.config.tables[3],
                        offset,
                        || Ok(F::from_u64(op(a, b))),
                    )?;
                    offset += 1;
                }
            }
        }
        Ok(())
    }

    fn load_witness(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        witness: (u64, [(u64, u64, u64); 4]),
    ) -> Result<(), Error> {
        let (op, values) = witness;
        self.config.q_enable.enable(region, offset)?;
        region.assign_advice(
            || "witness op",
            self.config.values[0],
            offset,
            || Ok(F::from_u64(op)),
        )?;
        for target_op in [1, 2, 3] {
            region.assign_advice(
                || "witness op_diff_inv",
                self.config.values[target_op],
                offset,
                || {
                    Ok((F::from_u64(op) - F::from_u64(target_op as u64))
                        .invert()
                        .unwrap_or(F::zero()))
                },
            )?;
        }
        for (idx, (a, b, c)) in values.iter().enumerate() {
            region.assign_advice(
                || "witness a",
                self.config.values[idx],
                offset - 3,
                || Ok(F::from_u64(*a)),
            )?;
            region.assign_advice(
                || "witness b",
                self.config.values[idx],
                offset - 2,
                || Ok(F::from_u64(*b)),
            )?;
            region.assign_advice(
                || "witness c",
                self.config.values[idx],
                offset - 1,
                || Ok(F::from_u64(*c)),
            )?;
        }
        Ok(())
    }

    pub fn construct(config: MultiLimbBitwiseConfig) -> Self {
        MultiLimbBitwiseChip {
            config,
            _marker: PhantomData,
        }
    }
}

struct TestCircuit<F: FieldExt> {
    witnesses: Option<Vec<(u64, [(u64, u64, u64); 4])>>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
    type Config = MultiLimbBitwiseConfig;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MultiLimbBitwiseChip::configure(meta)
    }

    fn synthesize(&self, cs: &mut impl Assignment<F>, config: Self::Config) -> Result<(), Error> {
        let mut layouter = SingleChipLayouter::new(cs)?;
        let chip = MultiLimbBitwiseChip::construct(config.clone());

        let witnesses = self.witnesses.as_ref().ok_or(Error::SynthesisError)?;

        layouter.assign_region(
            || "",
            |mut region| {
                chip.load_table(&mut region, 0)?;

                let mut offset = 4;
                for witness in witnesses {
                    chip.load_witness(&mut region, offset, *witness)?;
                    offset += 4;
                }

                Ok(())
            },
        )
    }
}

fn try_test_circuit(witnesses: Vec<(u64, [(u64, u64, u64); 4])>) -> Result<(), Vec<VerifyFailure>> {
    let circuit: TestCircuit<Base> = TestCircuit {
        witnesses: Some(witnesses),
        _marker: PhantomData,
    };

    let prover = MockProver::run(8, &circuit, vec![]).unwrap();
    prover.verify()
}

fn main() {
    // and
    // success
    assert_eq!(
        try_test_circuit(vec![(1, [(0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 1, 1)])]),
        Ok(())
    );
    // failure
    assert_eq!(
        try_test_circuit(vec![(1, [(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 0)])]),
        Err(vec![
            lookup_error_at!(0, 4),
            lookup_error_at!(1, 4),
            lookup_error_at!(2, 4),
            lookup_error_at!(3, 4)
        ])
    );

    // or
    // success
    assert_eq!(
        try_test_circuit(vec![(2, [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 1)])]),
        Ok(())
    );
    // failure
    assert_eq!(
        try_test_circuit(vec![(2, [(0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 0)])]),
        Err(vec![
            lookup_error_at!(4, 4),
            lookup_error_at!(5, 4),
            lookup_error_at!(6, 4),
            lookup_error_at!(7, 4)
        ])
    );

    // xor
    // success
    assert_eq!(
        try_test_circuit(vec![(3, [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)])]),
        Ok(())
    );
    // failure
    assert_eq!(
        try_test_circuit(vec![(3, [(0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 1)])]),
        Err(vec![
            lookup_error_at!(8, 4),
            lookup_error_at!(9, 4),
            lookup_error_at!(10, 4),
            lookup_error_at!(11, 4)
        ])
    );

    // add + or + xor
    // success
    assert_eq!(
        try_test_circuit(vec![
            (1, [(0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 1, 1)]),
            (2, [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 1)]),
            (3, [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]),
            (3, [(1, 1, 0), (1, 0, 1), (0, 1, 1), (0, 0, 0)]),
            (2, [(1, 1, 1), (1, 0, 1), (0, 1, 1), (0, 0, 0)]),
            (1, [(1, 1, 1), (1, 0, 0), (0, 1, 0), (0, 0, 0)]),
        ]),
        Ok(())
    );
    // failure
    assert_eq!(
        try_test_circuit(vec![
            (1, [(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 0)]),
            (2, [(0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 0)]),
            (3, [(0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 1)]),
            (3, [(1, 1, 1), (1, 0, 0), (0, 1, 0), (0, 0, 1)]),
            (2, [(1, 1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]),
            (1, [(1, 1, 0), (1, 0, 1), (0, 1, 1), (0, 0, 1)]),
        ]),
        Err(vec![
            lookup_error_at!(0, 4),
            lookup_error_at!(0, 24),
            lookup_error_at!(1, 4),
            lookup_error_at!(1, 24),
            lookup_error_at!(2, 4),
            lookup_error_at!(2, 24),
            lookup_error_at!(3, 4),
            lookup_error_at!(3, 24),
            lookup_error_at!(4, 8),
            lookup_error_at!(4, 20),
            lookup_error_at!(5, 8),
            lookup_error_at!(5, 20),
            lookup_error_at!(6, 8),
            lookup_error_at!(6, 20),
            lookup_error_at!(7, 8),
            lookup_error_at!(7, 20),
            lookup_error_at!(8, 12),
            lookup_error_at!(8, 16),
            lookup_error_at!(9, 12),
            lookup_error_at!(9, 16),
            lookup_error_at!(10, 12),
            lookup_error_at!(10, 16),
            lookup_error_at!(11, 12),
            lookup_error_at!(11, 16),
        ])
    );
}

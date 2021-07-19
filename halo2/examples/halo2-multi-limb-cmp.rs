use enum_iterator::IntoEnumIterator;
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
use std::{convert::TryInto, marker::PhantomData, mem::swap};
use zkp_example_halo2::{
    gadget::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    impl_limbs, lookup_error_at,
};

#[derive(Copy, Clone, Debug, IntoEnumIterator)]
enum Comparator {
    LT,
    GT,
    SLT,
    SGT,
}

impl Comparator {
    fn op(&self) -> u64 {
        *self as u64 + 1
    }

    fn tag(&self, is_final_result: bool) -> u64 {
        match self {
            Comparator::LT => {
                if is_final_result {
                    1
                } else {
                    2
                }
            }
            Comparator::SLT => 3,
            _ => unreachable!(),
        }
    }

    fn lookup(&self, mut a: u8, mut b: u8, c_in: u8) -> u8 {
        match c_in {
            0 | 1 => c_in,
            2 => {
                if a == b {
                    2
                } else {
                    if matches!(self, Comparator::GT | Comparator::SGT) {
                        swap(&mut a, &mut b)
                    }
                    match self {
                        Comparator::LT | Comparator::GT => (a < b) as u8,
                        Comparator::SLT | Comparator::SGT => {
                            if a > Limbs::MAX_PER_LIMB / 2 && b <= Limbs::MAX_PER_LIMB / 2 {
                                1
                            } else if b > Limbs::MAX_PER_LIMB / 2 && a <= Limbs::MAX_PER_LIMB / 2 {
                                0
                            } else {
                                (a < b) as u8
                            }
                        }
                    }
                }
            }
            _ => unreachable!(),
        }
    }
}

impl<F: FieldExt> From<Comparator> for Expression<F> {
    fn from(comparator: Comparator) -> Expression<F> {
        Expression::Constant(F::from_u64(comparator.op()))
    }
}

impl_limbs!(Limbs, 5, 2);

#[derive(Clone, Debug)]
pub struct MultiLimbCmpConfig<F> {
    pub q_enable: Selector,
    pub values: [Column<Advice>; 5],
    pub tables: [Column<Fixed>; 5],
    pub is_zeros: [IsZeroConfig<F>; 4],
}

pub struct MultiLimbCmpChip<F> {
    config: MultiLimbCmpConfig<F>,
    is_zero_chips: [IsZeroChip<F>; 4],
}

impl<F: FieldExt> MultiLimbCmpChip<F> {
    // Layout of a region (the region `load_witness` will assign)
    // +----------+---------+--------------+--------------+--------------+--------------+
    // | q_enable | advice1 |   advice2    |   advice3    |   advice4    |   advice5    |
    // +----------+---------+--------------+--------------+--------------+--------------+
    // |        0 | a1      | a2           | a3           | a4           | a5           |
    // |        0 | b1      | b2           | b3           | b4           | b5           |
    // |        0 | c1      | c2           | c3           | c4           | c5           |
    // |        1 | op      | inv0(op - 1) | inv0(op - 2) | inv0(op - 3) | inv0(op - 4) |
    // +----------+---------+--------------+--------------+--------------+--------------+
    fn configure(meta: &mut ConstraintSystem<F>) -> MultiLimbCmpConfig<F> {
        let q_enable = meta.selector();
        let values = [
            meta.advice_column(), // [a1, b1, c1,           op] in a row
            meta.advice_column(), // [a2, b2, c2, inv0(op - 1)] in a row
            meta.advice_column(), // [a3, b3, c3, inv0(op - 2)] in a row
            meta.advice_column(), // [a4, b4, c4, inv0(op - 3)] in a row
            meta.advice_column(), // [a5, b5, c5, inv0(op - 3)] in a row
        ];
        let tables = [
            meta.fixed_column(), // tag
            meta.fixed_column(), // a
            meta.fixed_column(), // b
            meta.fixed_column(), // c_in
            meta.fixed_column(), // c_out
        ];
        let is_zeros: [IsZeroConfig<F>; 4] = Comparator::into_enum_iter()
            .map(|comparator| {
                IsZeroChip::configure(
                    meta,
                    q_enable,
                    |meta| meta.query_advice(values[0], Rotation::cur()) - comparator.into(),
                    values[comparator as usize + 1],
                )
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let mut lookup =
            |range,
             c_in_fixed: Option<Expression<F>>,
             conditions: Vec<(Comparator, Comparator, bool)>| {
                for idx in range {
                    meta.lookup(|meta| {
                        let q_enable = meta.query_selector(q_enable);

                        // table
                        let ttag = meta.query_fixed(tables[0], Rotation::cur());
                        let ta = meta.query_fixed(tables[1], Rotation::cur());
                        let tb = meta.query_fixed(tables[2], Rotation::cur());
                        let tc_in = meta.query_fixed(tables[3], Rotation::cur());
                        let tc_out = meta.query_fixed(tables[4], Rotation::cur());

                        // witness
                        let a = meta.query_advice(values[idx], Rotation(-3));
                        let b = meta.query_advice(values[idx], Rotation(-2));
                        let c_in = c_in_fixed
                            .clone()
                            .unwrap_or_else(|| meta.query_advice(values[idx + 1], Rotation(-1)));
                        let c_out = meta.query_advice(values[idx], Rotation(-1));

                        // synthetic lookup
                        let mut synthetics = vec![Expression::Constant(F::zero()); 5];
                        for (tag_comparator, comparator, swap) in &conditions {
                            let is_zero_expression =
                                is_zeros[*comparator as usize].is_zero_expression.clone();

                            synthetics = synthetics
                                .into_iter()
                                .zip([
                                    // tag
                                    Expression::Constant(F::from_u64(tag_comparator.tag(idx == 0))),
                                    // a (or b if GT | SGT)
                                    if *swap { b.clone() } else { a.clone() },
                                    // b (or a if GT | SGT)
                                    if *swap { a.clone() } else { b.clone() },
                                    // c_in or c_in_fixed for highest column
                                    c_in.clone(),
                                    // c_out
                                    c_out.clone(),
                                ])
                                .map(|(synthetic, poly)| {
                                    synthetic + poly * is_zero_expression.clone()
                                })
                                .collect();
                        }

                        synthetics
                            .into_iter()
                            .zip([ttag, ta, tb, tc_in, tc_out])
                            .map(|(synthetic, table)| (q_enable.clone() * synthetic, table))
                            .collect()
                    });
                }
            };

        lookup(
            0..4,
            None,
            vec![
                (Comparator::LT, Comparator::LT, false),
                (Comparator::LT, Comparator::SLT, false),
                (Comparator::LT, Comparator::GT, true),
                (Comparator::LT, Comparator::SGT, true),
            ],
        );

        lookup(
            4..5,
            Some(Expression::Constant(F::from_u64(2))),
            vec![
                (Comparator::LT, Comparator::LT, false),
                (Comparator::SLT, Comparator::SLT, false),
                (Comparator::LT, Comparator::GT, true),
                (Comparator::SLT, Comparator::SGT, true),
            ],
        );

        MultiLimbCmpConfig {
            q_enable,
            values,
            tables,
            is_zeros,
        }
    }

    fn load_table(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        let mut offset = offset;

        let mut assign_fixed = |tag, a, b, c_in, c_out| -> Result<(), Error> {
            region.assign_fixed(|| "table tag", self.config.tables[0], offset, || Ok(tag))?;
            region.assign_fixed(|| "table a", self.config.tables[1], offset, || Ok(a))?;
            region.assign_fixed(|| "table b", self.config.tables[2], offset, || Ok(b))?;
            region.assign_fixed(|| "table c_in", self.config.tables[3], offset, || Ok(c_in))?;
            region.assign_fixed(
                || "table c_out",
                self.config.tables[4],
                offset,
                || Ok(c_out),
            )?;
            offset += 1;
            Ok(())
        };

        // no op lookup
        assign_fixed(F::zero(), F::zero(), F::zero(), F::zero(), F::zero())?;

        // LT (2 * 3 * 2^B * 2^B rows)
        for is_final_result in [false, true] {
            for a in 0..=Limbs::MAX_PER_LIMB {
                for b in 0..=Limbs::MAX_PER_LIMB {
                    for c_in in [0, 1, 2] {
                        let mut c_out = Comparator::LT.lookup(a, b, c_in);

                        // if is result column but still equal, set c_out to 0
                        if is_final_result && c_in == 2 && c_out == 2 {
                            c_out = 0;
                        }

                        assign_fixed(
                            F::from_u64(Comparator::LT.tag(is_final_result)),
                            F::from_u64(a as u64),
                            F::from_u64(b as u64),
                            F::from_u64(c_in as u64),
                            F::from_u64(c_out as u64),
                        )?;
                    }
                }
            }
        }

        // SLT (2^B * 2^B rows)
        for a in 0..=Limbs::MAX_PER_LIMB {
            for b in 0..=Limbs::MAX_PER_LIMB {
                assign_fixed(
                    F::from_u64(Comparator::SLT.tag(false)),
                    F::from_u64(a as u64),
                    F::from_u64(b as u64),
                    // c_in always be 2 becasue we only enable them in highest limb lookup
                    F::from_u64(2),
                    F::from_u64(Comparator::SLT.lookup(a, b, 2) as u64),
                )?;
            }
        }

        Ok(())
    }

    fn load_witness(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        witness: (Comparator, Limbs, Limbs, Limbs),
    ) -> Result<(), Error> {
        self.config.q_enable.enable(region, offset)?;

        let (comparator, a, b, c) = witness;

        // witness op and op_diff_inverse
        region.assign_advice(
            || "witness op",
            self.config.values[0],
            offset,
            || Ok(F::from_u64(comparator.op())),
        )?;
        for (is_zero_chip, fixed_comparator) in
            self.is_zero_chips.iter().zip(Comparator::into_enum_iter())
        {
            is_zero_chip.is_zero(
                region,
                offset,
                Some(F::from_u64(comparator.op()) - F::from_u64(fixed_comparator.op())),
            )?;
        }

        // witness limbs
        for (idx, ((&a, b), c)) in a.0.iter().zip(b.0).zip(c.0).enumerate() {
            region.assign_advice(
                || "witness a",
                self.config.values[idx],
                offset - 3,
                || Ok(F::from_u64(a as u64)),
            )?;
            region.assign_advice(
                || "witness b",
                self.config.values[idx],
                offset - 2,
                || Ok(F::from_u64(b as u64)),
            )?;
            region.assign_advice(
                || "witness c",
                self.config.values[idx],
                offset - 1,
                || Ok(F::from_u64(c as u64)),
            )?;
        }

        Ok(())
    }

    pub fn construct(config: MultiLimbCmpConfig<F>) -> Self {
        let is_zero_chips = config
            .is_zeros
            .iter()
            .map(|is_zero_config| IsZeroChip::construct(is_zero_config.clone()))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        Self {
            config,
            is_zero_chips,
        }
    }
}

struct TestCircuit<F: FieldExt> {
    witnesses: Option<Vec<(Comparator, Limbs, Limbs, Limbs)>>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
    type Config = MultiLimbCmpConfig<F>;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MultiLimbCmpChip::<F>::configure(meta)
    }

    fn synthesize(&self, cs: &mut impl Assignment<F>, config: Self::Config) -> Result<(), Error> {
        let mut layouter = SingleChipLayouter::new(cs)?;
        let chip = MultiLimbCmpChip::<F>::construct(config.clone());

        let witnesses = self.witnesses.as_ref().ok_or(Error::SynthesisError)?;

        layouter.assign_region(
            || "multi-limb comparator",
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

fn try_test_circuit(
    witnesses: Vec<(Comparator, Limbs, Limbs, Limbs)>,
) -> Result<(), Vec<VerifyFailure>> {
    let circuit: TestCircuit<Base> = TestCircuit {
        witnesses: Some(witnesses),
        _marker: PhantomData,
    };

    let prover =
        MockProver::run(2 * Limbs::NUM_BITS_PER_LIMB as u32 + 3, &circuit, vec![]).unwrap();
    prover.verify()
}

// TODO: add more error cases
fn main() {
    // LT
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::LT,
            Limbs([1, 2, 3, 2, 1]),
            Limbs([1, 2, 2, 2, 1]),
            Limbs([0, 0, 0, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::LT,
            Limbs([1, 2, 1, 2, 1]),
            Limbs([1, 2, 2, 2, 1]),
            Limbs([1, 1, 1, 2, 2])
        )]),
        Ok(())
    );

    // GT
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::GT,
            Limbs([1, 2, 3, 2, 1]),
            Limbs([1, 2, 2, 2, 1]),
            Limbs([1, 1, 1, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::GT,
            Limbs([1, 2, 1, 2, 1]),
            Limbs([1, 2, 2, 2, 1]),
            Limbs([0, 0, 0, 2, 2])
        )]),
        Ok(())
    );

    // SLT
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::SLT,
            Limbs([1, 2, 3, 2, 3]),
            Limbs([1, 2, 2, 2, 3]),
            Limbs([0, 0, 0, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::SLT,
            Limbs([1, 2, 1, 2, 3]),
            Limbs([1, 2, 2, 2, 3]),
            Limbs([1, 1, 1, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::SLT,
            Limbs([1, 2, 3, 2, 3]),
            Limbs([1, 2, 2, 2, 1]),
            Limbs([1, 1, 1, 1, 1])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::SLT,
            Limbs([1, 2, 1, 2, 1]),
            Limbs([1, 2, 2, 2, 3]),
            Limbs([0, 0, 0, 0, 0])
        )]),
        Ok(())
    );

    // SGT
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::SGT,
            Limbs([1, 2, 3, 2, 3]),
            Limbs([1, 2, 2, 2, 3]),
            Limbs([1, 1, 1, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::SGT,
            Limbs([1, 2, 1, 2, 3]),
            Limbs([1, 2, 2, 2, 3]),
            Limbs([0, 0, 0, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::SGT,
            Limbs([1, 2, 3, 2, 3]),
            Limbs([1, 2, 2, 2, 1]),
            Limbs([0, 0, 0, 0, 0])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Comparator::SGT,
            Limbs([1, 2, 1, 2, 1]),
            Limbs([1, 2, 2, 2, 3]),
            Limbs([1, 1, 1, 1, 1])
        )]),
        Ok(())
    );

    // zero case
    for comparator in Comparator::into_enum_iter() {
        assert_eq!(
            try_test_circuit(vec![(
                comparator,
                Limbs([0, 0, 0, 0, 0]),
                Limbs([0, 0, 0, 0, 0]),
                Limbs([0, 2, 2, 2, 2])
            )]),
            Ok(())
        );
        assert_eq!(
            try_test_circuit(vec![(
                comparator,
                Limbs([0, 0, 0, 0, 0]),
                Limbs([0, 0, 0, 0, 0]),
                Limbs([1, 2, 2, 2, 2])
            )]),
            Err(vec![lookup_error_at!(0, 4)])
        );
        assert_eq!(
            try_test_circuit(vec![(
                comparator,
                Limbs([0, 0, 0, 0, 0]),
                Limbs([0, 0, 0, 0, 0]),
                Limbs([2, 2, 2, 2, 2])
            )]),
            Err(vec![lookup_error_at!(0, 4)])
        );
    }
}

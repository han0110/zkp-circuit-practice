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
use std::{array, convert::TryInto, marker::PhantomData};
use zkp_example_halo2::{
    gadget::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    lookup_error_at,
};

#[derive(Copy, Clone, Debug)]
enum Comparator {
    LT,
    GT,
    SLT,
    SGT,
}

impl Comparator {
    fn values() -> [Self; 4] {
        [
            Comparator::LT,
            Comparator::GT,
            Comparator::SLT,
            Comparator::SGT,
        ]
    }

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

    fn lookup<const B: usize>(&self, a: u8, b: u8, c_in: u8) -> u8 {
        match c_in {
            0 | 1 => c_in,
            2 => {
                if a == b {
                    2
                } else {
                    match self {
                        Comparator::LT => (a < b) as u8,
                        Comparator::GT => (a > b) as u8,
                        Comparator::SLT => {
                            if a >= (1 << B - 1) && b < (1 << B - 1) {
                                1
                            } else if b >= (1 << B - 1) && a < (1 << B - 1) {
                                0
                            } else {
                                (a < b) as u8
                            }
                        }
                        Comparator::SGT => {
                            if a >= (1 << B - 1) && b < (1 << B - 1) {
                                0
                            } else if b >= (1 << B - 1) && a < (1 << B - 1) {
                                1
                            } else {
                                (a > b) as u8
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

#[derive(Default, Debug)]
struct Limbs<const B: usize>([u8; 5]);

impl<const B: usize> Limbs<B> {
    fn cmp(&self, rhs: &Self, comparator: Comparator) -> Self {
        let mut results = Limbs::default();

        results.0[4] = comparator.lookup::<B>(self.0[4], rhs.0[4], 2);
        for i in [3, 2, 1, 0] {
            results.0[i] = comparator.lookup::<B>(self.0[i], rhs.0[i], results.0[i + 1]);
        }

        results
    }
}

impl<const B: usize> From<u64> for Limbs<B> {
    fn from(n: u64) -> Self {
        assert!(n < 1 << 5 * B);

        Self([
            (n & ((1 << B) - 1)) as u8,
            (n >> B & ((1 << B) - 1)) as u8,
            (n >> 2 * B & ((1 << B) - 1)) as u8,
            (n >> 3 * B & ((1 << B) - 1)) as u8,
            (n >> 4 * B & ((1 << B) - 1)) as u8,
        ])
    }
}

#[derive(Clone, Debug)]
pub struct MultiLimbCmpConfig<F> {
    pub q_enable: Selector,
    pub values: [Column<Advice>; 5],
    pub tables: [Column<Fixed>; 5],
    pub is_zeros: [IsZeroConfig<F>; 4],
}

pub struct MultiLimbCmpChip<F, const B: usize> {
    config: MultiLimbCmpConfig<F>,
    is_zero_chips: [IsZeroChip<F>; 4],
}

impl<F: FieldExt, const B: usize> MultiLimbCmpChip<F, B> {
    const MAX_UNSIGNED: u8 = (1 << B) - 1;

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
        let is_zeros: [IsZeroConfig<F>; 4] = Comparator::values()
            .iter()
            .map(|&comparator| {
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
             fixed_c_in: Option<Expression<F>>,
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
                        let c_in = fixed_c_in
                            .clone()
                            .unwrap_or_else(|| meta.query_advice(values[idx + 1], Rotation(-1)));
                        let c_out = meta.query_advice(values[idx], Rotation(-1));

                        // synthetic selector
                        let zero = Expression::Constant(F::zero());
                        let (tag, a, b, c_in, c_out) = conditions.iter().fold(
                            (
                                zero.clone(),
                                zero.clone(),
                                zero.clone(),
                                zero.clone(),
                                zero.clone(),
                            ),
                            |accum, (tag_comparator, comparator, swap)| {
                                let is_zero_expression =
                                    is_zeros[*comparator as usize].is_zero_expression.clone();
                                let tag =
                                    Expression::Constant(F::from_u64(tag_comparator.tag(idx == 0)));

                                (
                                    accum.0 + tag * is_zero_expression.clone(),
                                    accum.1
                                        + if *swap { b.clone() } else { a.clone() }
                                            * is_zero_expression.clone(),
                                    accum.2
                                        + if *swap { a.clone() } else { b.clone() }
                                            * is_zero_expression.clone(),
                                    accum.3 + c_in.clone() * is_zero_expression.clone(),
                                    accum.4 + c_out.clone() * is_zero_expression,
                                )
                            },
                        );

                        array::IntoIter::new([
                            (tag, ttag),
                            (a, ta),
                            (b, tb),
                            (c_in, tc_in),
                            (c_out, tc_out),
                        ])
                        .map(move |(poly, table)| (q_enable.clone() * poly, table))
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
            for a in 0..=Self::MAX_UNSIGNED {
                for b in 0..=Self::MAX_UNSIGNED {
                    for c_in in [0, 1, 2] {
                        let mut c_out = Comparator::LT.lookup::<B>(a, b, c_in);

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
        for a in 0..=Self::MAX_UNSIGNED {
            for b in 0..=Self::MAX_UNSIGNED {
                assign_fixed(
                    F::from_u64(Comparator::SLT.tag(false)),
                    F::from_u64(a as u64),
                    F::from_u64(b as u64),
                    // c_in always be 2 becasue we only enable them in highest limb lookup
                    F::from_u64(2),
                    F::from_u64(Comparator::SLT.lookup::<B>(a, b, 2) as u64),
                )?;
            }
        }

        Ok(())
    }

    fn load_witness(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        witness: (Comparator, [u8; 5], [u8; 5], Option<[u8; 5]>),
    ) -> Result<(), Error> {
        self.config.q_enable.enable(region, offset)?;

        let (comparator, a, b, c) = witness;
        let a: Limbs<B> = Limbs(a);
        let b: Limbs<B> = Limbs(b);
        let c = c
            .map(|c| Limbs::<B>(c))
            .unwrap_or_else(|| a.cmp(&b, comparator));

        // witness op and op_diff_inverse
        region.assign_advice(
            || "witness op",
            self.config.values[0],
            offset,
            || Ok(F::from_u64(comparator.op())),
        )?;
        for (is_zero_chip, fixed_comparator) in self.is_zero_chips.iter().zip(Comparator::values())
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
struct TestCircuit<F: FieldExt, const B: usize> {
    witnesses: Option<Vec<(Comparator, [u8; 5], [u8; 5], Option<[u8; 5]>)>>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const B: usize> Circuit<F> for TestCircuit<F, B> {
    type Config = MultiLimbCmpConfig<F>;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MultiLimbCmpChip::<F, B>::configure(meta)
    }

    fn synthesize(&self, cs: &mut impl Assignment<F>, config: Self::Config) -> Result<(), Error> {
        let mut layouter = SingleChipLayouter::new(cs)?;
        let chip = MultiLimbCmpChip::<F, B>::construct(config.clone());

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

fn try_test_circuit<const B: usize>(
    witnesses: Vec<(Comparator, [u8; 5], [u8; 5], Option<[u8; 5]>)>,
) -> Result<(), Vec<VerifyFailure>> {
    let circuit: TestCircuit<Base, B> = TestCircuit {
        witnesses: Some(witnesses),
        _marker: PhantomData,
    };

    let prover = MockProver::run(2 * B as u32 + 3, &circuit, vec![]).unwrap();
    prover.verify()
}

// TODO: add more error cases
fn main() {
    // LT
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::LT,
            [1, 2, 3, 2, 1],
            [1, 2, 2, 2, 1],
            Some([0, 0, 0, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::LT,
            [1, 2, 1, 2, 1],
            [1, 2, 2, 2, 1],
            Some([1, 1, 1, 2, 2])
        )]),
        Ok(())
    );

    // GT
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::GT,
            [1, 2, 3, 2, 1],
            [1, 2, 2, 2, 1],
            Some([1, 1, 1, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::GT,
            [1, 2, 1, 2, 1],
            [1, 2, 2, 2, 1],
            Some([0, 0, 0, 2, 2])
        )]),
        Ok(())
    );

    // SLT
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::SLT,
            [1, 2, 3, 2, 3],
            [1, 2, 2, 2, 3],
            Some([0, 0, 0, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::SLT,
            [1, 2, 1, 2, 3],
            [1, 2, 2, 2, 3],
            Some([1, 1, 1, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::SLT,
            [1, 2, 3, 2, 3],
            [1, 2, 2, 2, 1],
            Some([1, 1, 1, 1, 1])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::SLT,
            [1, 2, 1, 2, 1],
            [1, 2, 2, 2, 3],
            Some([0, 0, 0, 0, 0])
        )]),
        Ok(())
    );

    // SGT
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::SGT,
            [1, 2, 3, 2, 3],
            [1, 2, 2, 2, 3],
            Some([1, 1, 1, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::SGT,
            [1, 2, 1, 2, 3],
            [1, 2, 2, 2, 3],
            Some([0, 0, 0, 2, 2])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::SGT,
            [1, 2, 3, 2, 3],
            [1, 2, 2, 2, 1],
            Some([0, 0, 0, 0, 0])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit::<2>(vec![(
            Comparator::SGT,
            [1, 2, 1, 2, 1],
            [1, 2, 2, 2, 3],
            Some([1, 1, 1, 1, 1])
        )]),
        Ok(())
    );

    // zero case
    for comparator in Comparator::values() {
        assert_eq!(
            try_test_circuit::<2>(vec![(
                comparator,
                [0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0],
                Some([0, 2, 2, 2, 2])
            )]),
            Ok(())
        );
        assert_eq!(
            try_test_circuit::<2>(vec![(
                comparator,
                [0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0],
                Some([1, 2, 2, 2, 2])
            )]),
            Err(vec![lookup_error_at!(0, 4)])
        );
        assert_eq!(
            try_test_circuit::<2>(vec![(
                comparator,
                [0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0],
                Some([2, 2, 2, 2, 2])
            )]),
            Err(vec![lookup_error_at!(0, 4)])
        );
    }
}

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
use std::{convert::TryInto, marker::PhantomData};
use zkp_example_halo2::{
    const_expr,
    gadget::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    impl_limbs, lookup_error_at,
};

#[derive(Copy, Clone, Debug, IntoEnumIterator)]
enum Operator {
    ADD,
    SUB,
}

impl Operator {
    fn op(&self) -> u64 {
        *self as u64 + 1
    }
}

impl<F: FieldExt> From<Operator> for Expression<F> {
    fn from(operator: Operator) -> Expression<F> {
        const_expr!(operator.op())
    }
}

#[derive(Clone, Debug)]
pub struct MultiLimbAddConfig<F> {
    pub q_enable: Selector,
    pub values: [Column<Advice>; Limbs::NUM_LIMBS],
    pub tables: [Column<Fixed>; 5],
    pub is_zeros: [IsZeroConfig<F>; Operator::VARIANT_COUNT],
}

pub struct MultiLimbAddChip<F> {
    config: MultiLimbAddConfig<F>,
    is_zero_chips: [IsZeroChip<F>; Operator::VARIANT_COUNT],
}

impl<F: FieldExt> MultiLimbAddChip<F> {
    // Layout of a region (the region `load_witness` will assign)
    // +----------+---------+--------------+--------------+--------------+--------------+
    // | q_enable | advice1 | advice2      | advice3      | ...          | adviceN      |
    // +----------+---------+--------------+--------------+--------------+--------------+
    // |        0 | a1      | a2           | a3           | ...          | aN           |
    // |        0 | b1      | b2           | b3           | ...          | bN           |
    // |        0 | c1      | c2           | c3           | ...          | cN           |
    // |        0 | carry1  | carry2       | carry3       | ...          | carryN       |
    // |        1 | op      | inv0(op - 1) | inv0(op - 2) | ...          | 0            |
    // +----------+---------+--------------+--------------+--------------+--------------+
    fn configure(meta: &mut ConstraintSystem<F>) -> MultiLimbAddConfig<F> {
        let q_enable = meta.selector();
        let values: [Column<Advice>; Limbs::NUM_LIMBS] = (0..Limbs::NUM_LIMBS)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let tables = [
            meta.fixed_column(), // a
            meta.fixed_column(), // b
            meta.fixed_column(), // c
            meta.fixed_column(), // c_in
            meta.fixed_column(), // c_out
        ];
        let is_zeros: [IsZeroConfig<F>; Operator::VARIANT_COUNT] = Operator::into_enum_iter()
            .map(|operator| {
                IsZeroChip::configure(
                    meta,
                    q_enable,
                    |meta| meta.query_advice(values[0], Rotation::cur()) - operator.into(),
                    values[operator as usize + 1],
                )
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        for idx in 0..values.len() {
            meta.lookup(|meta| {
                let q_enable = meta.query_selector(q_enable);

                // table
                let ta = meta.query_fixed(tables[0], Rotation::cur());
                let tb = meta.query_fixed(tables[1], Rotation::cur());
                let tc = meta.query_fixed(tables[2], Rotation::cur());
                let tcarry_in = meta.query_fixed(tables[3], Rotation::cur());
                let tcarry_out = meta.query_fixed(tables[4], Rotation::cur());

                // witness
                let a = meta.query_advice(values[idx], Rotation(-4));
                let b = meta.query_advice(values[idx], Rotation(-3));
                let c = meta.query_advice(values[idx], Rotation(-2));
                let carry_in = if idx == values.len() - 1 {
                    const_expr!(0)
                } else {
                    meta.query_advice(values[idx + 1], Rotation(-1))
                };
                let carry_out = meta.query_advice(values[idx], Rotation(-1));

                vec![
                    // ADD
                    vec![
                        a.clone(),
                        b.clone(),
                        c.clone(),
                        carry_in.clone(),
                        carry_out.clone(),
                    ],
                    // SUB (check if b + c === a)
                    vec![b, c, a, carry_in, carry_out],
                ]
                .into_iter()
                .zip(&is_zeros)
                .fold(vec![const_expr!(0); 5], |synthetics, (polys, is_zero)| {
                    synthetics
                        .into_iter()
                        .zip(polys)
                        .map(|(synthetic, poly)| {
                            synthetic + is_zero.is_zero_expression.clone() * poly
                        })
                        .collect::<Vec<_>>()
                })
                .into_iter()
                .zip([ta, tb, tc, tcarry_in, tcarry_out])
                .map(|(poly, table)| (q_enable.clone() * poly, table))
                .collect()
            });
        }

        MultiLimbAddConfig {
            q_enable,
            values,
            tables,
            is_zeros,
        }
    }

    fn load_table(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        let mut offset = offset;

        let mut assign_fixed = |a, b, c, carry_in, carry_out| -> Result<(), Error> {
            let tables = self.config.tables;
            region.assign_fixed(|| "table a", tables[0], offset, || Ok(a))?;
            region.assign_fixed(|| "table b", tables[1], offset, || Ok(b))?;
            region.assign_fixed(|| "table c", tables[2], offset, || Ok(c))?;
            region.assign_fixed(|| "table carry_in", tables[3], offset, || Ok(carry_in))?;
            region.assign_fixed(|| "table carry_out", tables[4], offset, || Ok(carry_out))?;
            offset += 1;
            Ok(())
        };

        // no op lookup
        assign_fixed(F::zero(), F::zero(), F::zero(), F::zero(), F::zero())?;

        for a in 0..=Limbs::MAX_PER_LIMB {
            for b in 0..=Limbs::MAX_PER_LIMB {
                for carry_in in [0, 1] {
                    let mut carry_out = carry_in;
                    let c = Limbs::adc_limb(a, b, &mut carry_out);

                    assign_fixed(
                        F::from_u64(a as u64),
                        F::from_u64(b as u64),
                        F::from_u64(c as u64),
                        F::from_u64(carry_in as u64),
                        F::from_u64(carry_out as u64),
                    )?;
                }
            }
        }

        Ok(())
    }

    fn load_witness(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        witness: (Operator, Limbs, Limbs, Limbs, Limbs),
    ) -> Result<(), Error> {
        self.config.q_enable.enable(region, offset)?;

        let (operator, a, b, c, carry) = witness;

        // witness op and op_diff_inverse
        region.assign_advice(
            || "witness op",
            self.config.values[0],
            offset,
            || Ok(F::from_u64(operator.op())),
        )?;
        for (is_zero_chip, fixed_comparator) in
            self.is_zero_chips.iter().zip(Operator::into_enum_iter())
        {
            is_zero_chip.is_zero(
                region,
                offset,
                Some(F::from_u64(operator.op()) - F::from_u64(fixed_comparator.op())),
            )?;
        }

        // witness limbs
        for (idx, (((&a, b), c), carry)) in a.0.iter().zip(b.0).zip(c.0).zip(carry.0).enumerate() {
            region.assign_advice(
                || "witness a",
                self.config.values[idx],
                offset - 4,
                || Ok(F::from_u64(a as u64)),
            )?;
            region.assign_advice(
                || "witness b",
                self.config.values[idx],
                offset - 3,
                || Ok(F::from_u64(b as u64)),
            )?;
            region.assign_advice(
                || "witness c",
                self.config.values[idx],
                offset - 2,
                || Ok(F::from_u64(c as u64)),
            )?;
            region.assign_advice(
                || "witness carry",
                self.config.values[idx],
                offset - 1,
                || Ok(F::from_u64(carry as u64)),
            )?;
        }

        Ok(())
    }

    pub fn construct(config: MultiLimbAddConfig<F>) -> Self {
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
    witnesses: Option<Vec<(Operator, Limbs, Limbs, Limbs, Limbs)>>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
    type Config = MultiLimbAddConfig<F>;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MultiLimbAddChip::<F>::configure(meta)
    }

    fn synthesize(&self, cs: &mut impl Assignment<F>, config: Self::Config) -> Result<(), Error> {
        let mut layouter = SingleChipLayouter::new(cs)?;
        let chip = MultiLimbAddChip::<F>::construct(config.clone());

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
    witnesses: Vec<(Operator, Limbs, Limbs, Limbs, Limbs)>,
) -> Result<(), Vec<VerifyFailure>> {
    let circuit: TestCircuit<Base> = TestCircuit {
        witnesses: Some(witnesses),
        _marker: PhantomData,
    };

    let prover =
        MockProver::run(2 * Limbs::NUM_BITS_PER_LIMB as u32 + 2, &circuit, vec![]).unwrap();
    prover.verify()
}

impl_limbs!(Limbs, 8, 2);

fn main() {
    // add
    // ok
    assert_eq!(
        try_test_circuit(vec![(
            Operator::ADD,
            Limbs([0, 1, 2, 3, 0, 1, 2, 3]),
            Limbs([3, 2, 1, 0, 3, 2, 1, 0]),
            Limbs([3, 3, 3, 3, 3, 3, 3, 3]),
            Limbs([0, 0, 0, 0, 0, 0, 0, 0])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Operator::ADD,
            Limbs([2, 2, 2, 2, 2, 2, 2, 2]),
            Limbs([2, 2, 2, 2, 2, 2, 2, 2]),
            Limbs([1, 1, 1, 1, 1, 1, 1, 0]),
            Limbs([1, 1, 1, 1, 1, 1, 1, 1])
        )]),
        Ok(())
    );
    // error
    assert_eq!(
        try_test_circuit(vec![(
            Operator::ADD,
            Limbs([0, 1, 2, 3, 0, 1, 2, 3]),
            Limbs([3, 2, 1, 0, 3, 2, 1, 0]),
            Limbs([3, 3, 3, 3, 3, 3, 3, 3]),
            Limbs([1, 1, 1, 1, 1, 1, 1, 1])
        )]),
        Err(vec![
            lookup_error_at!(0, 4),
            lookup_error_at!(1, 4),
            lookup_error_at!(2, 4),
            lookup_error_at!(3, 4),
            lookup_error_at!(4, 4),
            lookup_error_at!(5, 4),
            lookup_error_at!(6, 4),
            lookup_error_at!(7, 4),
        ])
    );
    assert_eq!(
        try_test_circuit(vec![(
            Operator::ADD,
            Limbs([2, 2, 2, 2, 2, 2, 2, 2]),
            Limbs([2, 2, 2, 2, 2, 2, 2, 2]),
            Limbs([1, 1, 1, 1, 1, 1, 1, 0]),
            Limbs([0, 0, 0, 0, 0, 0, 0, 0])
        )]),
        Err(vec![
            lookup_error_at!(0, 4),
            lookup_error_at!(1, 4),
            lookup_error_at!(2, 4),
            lookup_error_at!(3, 4),
            lookup_error_at!(4, 4),
            lookup_error_at!(5, 4),
            lookup_error_at!(6, 4),
            lookup_error_at!(7, 4),
        ])
    );

    // sub
    // ok
    assert_eq!(
        try_test_circuit(vec![(
            Operator::SUB,
            Limbs([3, 3, 3, 3, 3, 3, 3, 3]),
            Limbs([0, 1, 2, 3, 0, 1, 2, 3]),
            Limbs([3, 2, 1, 0, 3, 2, 1, 0]),
            Limbs([0, 0, 0, 0, 0, 0, 0, 0])
        )]),
        Ok(())
    );
    assert_eq!(
        try_test_circuit(vec![(
            Operator::SUB,
            Limbs([1, 1, 1, 1, 1, 1, 1, 0]),
            Limbs([2, 2, 2, 2, 2, 2, 2, 2]),
            Limbs([2, 2, 2, 2, 2, 2, 2, 2]),
            Limbs([1, 1, 1, 1, 1, 1, 1, 1])
        )]),
        Ok(())
    );
    // error
    assert_eq!(
        try_test_circuit(vec![(
            Operator::SUB,
            Limbs([3, 3, 3, 3, 3, 3, 3, 3]),
            Limbs([0, 1, 2, 3, 0, 1, 2, 3]),
            Limbs([3, 2, 1, 0, 3, 2, 1, 0]),
            Limbs([1, 1, 1, 1, 1, 1, 1, 1])
        )]),
        Err(vec![
            lookup_error_at!(0, 4),
            lookup_error_at!(1, 4),
            lookup_error_at!(2, 4),
            lookup_error_at!(3, 4),
            lookup_error_at!(4, 4),
            lookup_error_at!(5, 4),
            lookup_error_at!(6, 4),
            lookup_error_at!(7, 4),
        ])
    );
    assert_eq!(
        try_test_circuit(vec![(
            Operator::SUB,
            Limbs([1, 1, 1, 1, 1, 1, 1, 0]),
            Limbs([2, 2, 2, 2, 2, 2, 2, 2]),
            Limbs([2, 2, 2, 2, 2, 2, 2, 2]),
            Limbs([0, 0, 0, 0, 0, 0, 0, 0])
        )]),
        Err(vec![
            lookup_error_at!(0, 4),
            lookup_error_at!(1, 4),
            lookup_error_at!(2, 4),
            lookup_error_at!(3, 4),
            lookup_error_at!(4, 4),
            lookup_error_at!(5, 4),
            lookup_error_at!(6, 4),
            lookup_error_at!(7, 4),
        ])
    );
}

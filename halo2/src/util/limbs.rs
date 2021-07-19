#[macro_export]
macro_rules! impl_limbs {
    ($name:ident, $num_limbs:expr, $num_bits_per_limb:expr) => {
        #[derive(Clone, Copy, Debug, Default, PartialEq, PartialOrd)]
        struct $name([u8; $num_limbs]);

        impl Limbs {
            const NUM_LIMBS: usize = $num_limbs;

            const NUM_BITS_PER_LIMB: usize = $num_bits_per_limb;

            const MAX_PER_LIMB: u8 = (1 << $num_bits_per_limb) - 1;

            const MAX_IN_U64: u64 = (1u64 << Self::NUM_LIMBS * Self::NUM_BITS_PER_LIMB) - 1;

            const MAX: Self = Self([Self::MAX_PER_LIMB; Self::NUM_LIMBS]);

            fn from_u64(mut n: u64) -> Self {
                assert!(n <= Self::MAX_IN_U64);

                let mut limbs = Self::default();
                for limb in limbs.0.iter_mut() {
                    *limb = (n as u8) & Self::MAX_PER_LIMB;
                    n >>= Self::NUM_BITS_PER_LIMB;
                }

                limbs
            }

            fn to_u64(&self) -> u64 {
                let mut n = 0;

                for (lsh, limb) in self.0.iter().enumerate() {
                    n += (*limb as u64) << lsh * Self::NUM_BITS_PER_LIMB;
                }

                n
            }

            fn adc_limb(a: u8, b: u8, carry: &mut u8) -> u8 {
                let mut c = a + b + *carry;

                if c > Self::MAX_PER_LIMB {
                    c -= Self::MAX_PER_LIMB + 1;
                    *carry = 1
                } else {
                    *carry = 0
                }

                c
            }

            fn sbb_limb(a: u8, b: u8, borrow: &mut u8) -> u8 {
                let mut c = a + Self::MAX_PER_LIMB + 1 - b - *borrow;

                if c > Self::MAX_PER_LIMB {
                    c -= Self::MAX_PER_LIMB + 1;
                    *borrow = 0
                } else {
                    *borrow = 1
                }

                c
            }

            fn adc(&self, rhs: Self, mut carry: u8) -> (Self, Self) {
                let (mut result, mut carries) = (Self::default(), Self::default());

                for (idx, (a, b)) in self.0.iter().zip(rhs.0).enumerate() {
                    result.0[idx] = Self::adc_limb(*a, b, &mut carry);
                    carries.0[idx] = carry;
                }

                (result, carries)
            }

            fn sbb(&self, rhs: Self) -> (Self, Self) {
                let (mut result, mut borrows) = (Self::default(), Self::default());

                let mut borrow = 0;
                for (idx, (a, b)) in self.0.iter().zip(rhs.0).enumerate() {
                    result.0[idx] = Self::sbb_limb(*a, b, &mut borrow);
                    borrows.0[idx] = borrow;
                }

                (result, borrows)
            }
        }

        impl From<u64> for Limbs {
            fn from(n: u64) -> Self {
                Limbs::from_u64(n)
            }
        }

        impl std::ops::Add for Limbs {
            type Output = Self;

            fn add(self, rhs: Self) -> Self {
                self.adc(rhs, 0).0
            }
        }

        impl std::ops::Sub for Limbs {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self {
                let (result, borrows) = self.sbb(rhs);
                if borrows.0[Self::NUM_LIMBS - 1] == 1 {
                    result.adc(Self::MAX, 1).0
                } else {
                    result
                }
            }
        }
    };
    ($name:ident, $num_limbs:expr) => {
        impl_limbs!($name, $num_limbs, 8)
    };
}

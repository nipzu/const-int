use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr, ShrAssign};

use super::{ConstUint, ConstDigit};

impl<const DIGS: usize> ConstUint<DIGS> {
    pub const fn count_ones(self) -> u32 {
        let mut count = 0;
        let mut i = 0;
        while i < DIGS {
            count += self.digits[i].count_ones();
            i += 1;
        }
        count
    }

    pub const fn count_zeros(self) -> u32 {
        let mut count = 0;
        let mut i = 0;
        while i < DIGS {
            count += self.digits[i].count_zeros();
            i += 1;
        }
        count
    }
}

impl<const DIGS: usize> const Not for ConstUint<DIGS> {
    type Output = Self;
    fn not(mut self) -> Self::Output {
        let mut i = 0;
        while i < DIGS {
            self.digits[i] = !self.digits[i];
            i += 1;
        }
        self
    }
}

impl<const SELF_DIGS: usize, const RHS_DIGS: usize> const ShlAssign<ConstUint::<RHS_DIGS>> for ConstUint<SELF_DIGS> {
    fn shl_assign(&mut self, _rhs: ConstUint::<RHS_DIGS>) {
        // if rhs >= DIGS * ConstDigit::BITS {
        //     panic!("Integer overflow");
        // }
        todo!()
    }
}

macro_rules! impl_bit_operation {
    (
        $OpAssignTrait:ty, $OpTrait:ty,
        $OpAssignTraitFn:ident, $OpTraitFn:ident,
        $OpAssign:tt
    ) => {
        impl <const DIGS: usize> const $OpAssignTrait for ConstUint<DIGS> {
            fn $OpAssignTraitFn(&mut self, rhs: Self) {
                let mut i = 0;
                while i < DIGS {
                    self.digits[i] $OpAssign rhs.digits[i];
                    i += 1;
                }
            }
        }

        impl <const DIGS: usize> const $OpTrait for ConstUint<DIGS> {
            type Output = Self;
            fn $OpTraitFn(mut self, rhs: Self) -> Self::Output {
                self $OpAssign rhs;
                self
            }
        }
    };
}

impl_bit_operation!(BitXorAssign, BitXor, bitxor_assign, bitxor, ^=);
impl_bit_operation!(BitOrAssign, BitOr, bitor_assign, bitor, |=);
impl_bit_operation!(BitAndAssign, BitAnd, bitand_assign, bitand, &=);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_and() {
        const A: ConstUint<2> = ConstUint::from_digits([0b01010101, 0b10011001]);
        const B: ConstUint<2> = ConstUint::from_digits([0b11110000, 0b11001100]);

        const C: ConstUint<2> = A & B;

        assert_eq!(C, ConstUint::from_digits([0b01010000, 0b10001000]));
    }

    #[test]
    fn test_or() {
        const A: ConstUint<2> = ConstUint::from_digits([0b01010101, 0b10011001]);
        const B: ConstUint<2> = ConstUint::from_digits([0b11110000, 0b11001100]);

        const C: ConstUint<2> = A | B;

        assert_eq!(C, ConstUint::from_digits([0b11110101, 0b11011101]));
    }

    #[test]
    fn test_xor() {
        const A: ConstUint<2> = ConstUint::from_digits([0b01010101, 0b10011001]);
        const B: ConstUint<2> = ConstUint::from_digits([0b11110000, 0b11001100]);

        const C: ConstUint<2> = A ^ B;

        assert_eq!(C, ConstUint::from_digits([0b10100101, 0b01010101]));
    }
}

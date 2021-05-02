use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

use super::{ConstDigit, ConstUint};

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

    pub const fn rotate_left(self, n: u32) -> Self {
        let mut result = Self::zero();

        let digits_to_rotate = (n as usize / ConstDigit::BITS as usize) % DIGS;
        let bits_to_rotate = n % ConstDigit::BITS;

        let mut i = 0;
        while i < DIGS {
            result.digits[i] =
                self.digits[(i + DIGS - digits_to_rotate) % DIGS as usize] << bits_to_rotate;
            if bits_to_rotate != 0 {
                result.digits[i] |= self.digits
                    [(i + 2 * DIGS - digits_to_rotate - 1) % DIGS as usize]
                    >> (ConstDigit::BITS - bits_to_rotate);
            }
            i += 1;
        }

        result
    }

    pub const fn rotate_right(self, n: u32) -> Self {
        let mut result = Self::zero();

        let digits_to_rotate = (n as usize / ConstDigit::BITS as usize) % DIGS;
        let bits_to_rotate = n % ConstDigit::BITS;

        let mut i = 0;
        while i < DIGS {
            result.digits[i] =
                self.digits[(i + digits_to_rotate) % DIGS as usize] >> bits_to_rotate;
            if bits_to_rotate != 0 {
                result.digits[i] |= self.digits[(i + digits_to_rotate + 1) % DIGS as usize]
                    << (ConstDigit::BITS - bits_to_rotate);
            }
            i += 1;
        }

        result
    }

    pub const fn is_power_of_two(self) -> bool {
        self.leading_zeros() + self.trailing_zeros() == Self::BITS - 1
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

impl<const DIGS: usize> const Shl<u32> for ConstUint<DIGS> {
    type Output = Self;
    fn shl(mut self, rhs: u32) -> Self::Output {
        self <<= rhs;
        self
    }
}

impl<const DIGS: usize> const ShlAssign<u32> for ConstUint<DIGS> {
    #[track_caller]
    fn shl_assign(&mut self, rhs: u32) {
        if rhs >= Self::BITS {
            panic!("Integer overflow");
        }

        let digits_to_shift = (rhs / ConstDigit::BITS) as usize;
        let bits_to_shift = rhs % ConstDigit::BITS;

        let mut i = DIGS;
        if digits_to_shift != 0 {
            while i > digits_to_shift {
                self.digits[i - 1] = self.digits[i - 1 - digits_to_shift];
                i -= 1;
            }
            while i > 0 {
                self.digits[i - 1] = 0;
                i -= 1;
            }
        }

        if bits_to_shift == 0 {
            return;
        }

        let overflowing_bits_mask = (!0) << (ConstDigit::BITS - bits_to_shift);
        let mut overflowing_bits = 0;
        i = digits_to_shift;
        while i < DIGS {
            let new_overflowing_bits =
                (self.digits[i] & overflowing_bits_mask) >> (ConstDigit::BITS - bits_to_shift);
            self.digits[i] <<= bits_to_shift;
            self.digits[i] |= overflowing_bits;
            overflowing_bits = new_overflowing_bits;
            i += 1;
        }
    }
}

impl<const DIGS: usize> const ShrAssign<u32> for ConstUint<DIGS> {
    #[track_caller]
    fn shr_assign(&mut self, rhs: u32) {
        if rhs >= Self::BITS {
            panic!("Integer overflow");
        }

        let digits_to_shift = (rhs / ConstDigit::BITS) as usize;
        let bits_to_shift = rhs % ConstDigit::BITS;

        let mut i = 0;
        if digits_to_shift != 0 {
            while i < DIGS - digits_to_shift {
                self.digits[i] = self.digits[i + digits_to_shift];
                i += 1;
            }
            while i < DIGS {
                self.digits[i] = 0;
                i += 1;
            }
        }

        if bits_to_shift == 0 {
            return;
        }

        let overflowing_bits_mask = (!0) >> (ConstDigit::BITS - bits_to_shift);
        let mut overflowing_bits = 0;
        i = DIGS - digits_to_shift;
        while i > 0 {
            let new_overflowing_bits =
                (self.digits[i - 1] & overflowing_bits_mask) << (ConstDigit::BITS - bits_to_shift);
            self.digits[i - 1] >>= bits_to_shift;
            self.digits[i - 1] |= overflowing_bits;
            overflowing_bits = new_overflowing_bits;
            i -= 1;
        }
    }
}

impl<const DIGS: usize> const Shr<u32> for ConstUint<DIGS> {
    type Output = Self;
    fn shr(mut self, rhs: u32) -> Self::Output {
        self >>= rhs;
        self
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

    #[test]
    fn test_shl_assign() {
        const A: ConstUint<2> = ConstUint::from_digits([12157665459056928801, 298023223876953125]);
        for k in 0..128 {
            let mut b = A;
            b <<= k;
            assert_eq!(
                b,
                A.overflowing_mul(ConstUint::from_digits([
                    2u128.pow(k) as u64,
                    (2u128.pow(k) / 2u128.pow(64)) as u64
                ]))
                .0
            );
        }
    }

    #[test]
    fn test_shr_assign() {
        const A: ConstUint<2> = ConstUint::from_digits([12157665459056928801, 298023223876953125]);
        for k in 0..128 {
            let mut b = A;
            b >>= k;
            let c = 5497558138880000012157665459056928801u128 / 2u128.pow(k);
            assert_eq!(
                b,
                ConstUint::from_digits([c as u64, (c / 2u128.pow(64)) as u64])
            );
        }
    }

    #[test]
    fn test_rotate_right() {
        let a = ConstUint::from_digits([0b00110110, 0b11010001]);
        assert_eq!(
            a.rotate_right(67),
            ConstUint::from_digits([(1 << 63) | (1 << 62) | 0b11010, (1 << 61) | 0b0110])
        );

        let rots = [64, 324, 452, 23423, 4433, 23, 0, 1];
        let n = 0x422ca8b0a00a425a8b8b452291fe821u128;

        for r in &rots {
            assert_eq!(
                ConstUint::<2>::from(n.rotate_right(*r)),
                ConstUint::<2>::from(n).rotate_right(*r)
            )
        }
    }

    #[test]
    fn test_rotate_left() {
        let a = ConstUint::from_digits([(1 << 63) | (1 << 62) | 0b11010, (1 << 61) | 0b0110]);
        assert_eq!(
            a.rotate_left(67),
            ConstUint::from_digits([0b00110110, 0b11010001])
        );

        let rots = [64, 324, 452, 23423, 4433, 23, 0, 1];
        let n = 0x422ca8b0a00a425a8b8b452291fe821u128;

        for r in &rots {
            assert_eq!(
                ConstUint::<2>::from(n.rotate_left(*r)),
                ConstUint::<2>::from(n).rotate_left(*r)
            )
        }
    }
}

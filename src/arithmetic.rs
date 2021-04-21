use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

use super::{ConstDigit, ConstDoubleDigit, ConstUint};

impl<const DIGS: usize> ConstUint<DIGS> {
    #[must_use = "if ignoring overflow is desired, `wrapping_add_assign` should be used instead"]
    pub const fn overflowing_add_assign(&mut self, rhs: Self) -> bool {
        let mut i = 0;
        let mut carry = false;
        while i < DIGS {
            if carry && self.digits[i] == ConstDigit::MAX {
                self.digits[i] = rhs.digits[i];
                carry = true;
            } else {
                if carry {
                    self.digits[i] += 1;
                }
                (self.digits[i], carry) = self.digits[i].overflowing_add(rhs.digits[i]);
            }
            i += 1;
        }

        carry
    }

    pub const fn saturating_add_assign(&mut self, rhs: Self) {
        if self.overflowing_add_assign(rhs) {
            *self = Self::MAX;
        }
    }

    pub const fn wrapping_add_assign(&mut self, rhs: Self) {
        let _ = self.overflowing_add_assign(rhs);
    }

    pub const fn overflowing_add(mut self, rhs: Self) -> (Self, bool) {
        let did_overflow = self.overflowing_add_assign(rhs);
        (self, did_overflow)
    }

    pub const fn saturating_add(mut self, rhs: Self) -> Self {
        self.saturating_add_assign(rhs);
        self
    }

    pub const fn wrapping_add(mut self, rhs: Self) -> Self {
        self.wrapping_add_assign(rhs);
        self
    }

    pub const fn checked_add(mut self, rhs: Self) -> Option<Self> {
        if self.overflowing_add_assign(rhs) {
            None
        } else {
            Some(self)
        }
    }

    #[must_use = "if ignoring overflow is desired, `wrapping_sub_assign` should be used instead"]
    pub const fn overflowing_sub_assign(&mut self, rhs: Self) -> bool {
        let mut i = 0;
        let mut carry = false;
        while i < DIGS {
            if carry && self.digits[i] == ConstDigit::MIN {
                self.digits[i] = ConstDigit::MAX - rhs.digits[i];
                carry = true;
            } else {
                if carry {
                    self.digits[i] -= 1;
                }
                (self.digits[i], carry) = self.digits[i].overflowing_sub(rhs.digits[i]);
            }
            i += 1;
        }

        carry
    }

    pub const fn saturating_sub_assign(&mut self, rhs: Self) {
        if self.overflowing_sub_assign(rhs) {
            *self = Self::MIN;
        }
    }

    pub const fn wrapping_sub_assign(&mut self, rhs: Self) {
        let _ = self.overflowing_sub_assign(rhs);
    }

    pub const fn overflowing_sub(mut self, rhs: Self) -> (Self, bool) {
        let did_overflow = self.overflowing_sub_assign(rhs);
        (self, did_overflow)
    }

    pub const fn saturating_sub(mut self, rhs: Self) -> Self {
        self.saturating_sub_assign(rhs);
        self
    }

    pub const fn wrapping_sub(mut self, rhs: Self) -> Self {
        self.wrapping_sub_assign(rhs);
        self
    }

    pub const fn checked_sub(mut self, rhs: Self) -> Option<Self> {
        if self.overflowing_sub_assign(rhs) {
            None
        } else {
            Some(self)
        }
    }

    const fn len_digits(self) -> usize {
        let mut i = DIGS;

        while i > 0 {
            if self.digits[i - 1] != 0 {
                break;
            }
            i -= 1;
        }

        i
    }
}

/// computes self += a * b
// const fn multiply_and_add(dest: &mut [ConstDigit], a: ConstDigit, b: ConstDigit) {
//     // TODO this hella shit
//     let multiplied = a as ConstDoubleDigit * b as ConstDoubleDigit;
//     let (mut high, low) = (
//         (multiplied >> ConstDigit::BITS) as ConstDigit,
//         multiplied as ConstDigit,
//     );
//     let mut add_carry = false;
//     if low != 0 {
//         (dest[0], add_carry) = dest[0].overflowing_add(low);
//     }
//     if add_carry {
//         high += 1;
//     }
//     if high != 0 {
//         (dest[1], add_carry) = dest[1].overflowing_add(high);
//     }
//     let mut j = 2;
//     while add_carry {
//         (dest[j], add_carry) = dest[j].overflowing_add(1);
//         j += 1;
//     }
// }

impl<const DIGS: usize> const Add for ConstUint<DIGS> {
    type Output = Self;
    #[track_caller]
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const DIGS: usize> const AddAssign for ConstUint<DIGS> {
    #[track_caller]
    fn add_assign(&mut self, rhs: Self) {
        if self.overflowing_add_assign(rhs) {
            panic!("Integer overflow");
        }
    }
}

impl<const DIGS: usize> const Sub for ConstUint<DIGS> {
    type Output = Self;
    #[track_caller]
    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<const DIGS: usize> const SubAssign for ConstUint<DIGS> {
    #[track_caller]
    fn sub_assign(&mut self, rhs: Self) {
        if self.overflowing_sub_assign(rhs) {
            panic!("Integer overflow");
        }
    }
}

impl<const DIGS: usize> const Mul for ConstUint<DIGS> {
    type Output = Self;
    #[track_caller]
    fn mul(self, rhs: Self) -> Self::Output {
        let mut result = Self::zero();

        let self_len = self.len_digits();
        let rhs_len = rhs.len_digits();

        if self_len == 0 || rhs_len == 0 {
            return Self::zero();
        }

        if self_len + rhs_len - 1 > DIGS {
            panic!("Integer overflow");
        }

        if self_len + rhs_len - 1 == DIGS {
            // maybe overflow
        }

        if self_len + rhs_len - 1 < DIGS {
            // no overflow
        }

        let mut i = 0;
        while i < self_len {
            let mut j = 0;
            while j < rhs_len {
                let multiplied =
                    self.digits[i] as ConstDoubleDigit * rhs.digits[j] as ConstDoubleDigit;
                let (mut high, low) = (
                    (multiplied >> ConstDigit::BITS) as ConstDigit,
                    multiplied as ConstDigit,
                );
                let mut add_carry = false;
                if low != 0 {
                    (result.digits[i+j], add_carry) = result.digits[i+j].overflowing_add(low);
                }
                if add_carry {
                    high += 1;
                }
                if high != 0 {
                    if i + j + 1 == DIGS {
                        panic!("Integer overflow");
                    }
                    (result.digits[i+j+1], add_carry) = result.digits[i+j+1].overflowing_add(high);
                }
                let mut k = 2;
                while add_carry {
                    if i + j + k == DIGS {
                        panic!("Integer overflow");
                    }
                    (result.digits[i+j+k], add_carry) = result.digits[i+j+k].overflowing_add(1);
                    k += 1;
                }

                j += 1;
            }
            i += 1;
        }

        result
    }
}

impl <const DIGS: usize> const MulAssign for ConstUint<DIGS> {
    #[track_caller]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let mut n = ConstUint::<3>::zero();
        n += ConstUint::one();
        assert_eq!(n, ConstUint::one());

        let mut k = ConstUint::from_digits([ConstDigit::MAX, 2]);
        k += ConstUint::from_digits([30, 17]);
        assert_eq!(k, ConstUint::from_digits([29, 20]));

        const M: ConstUint<2> = ConstUint::from_digits([15, 9]) + ConstUint::from_digits([14, 11]);

        assert_eq!(M, k);
    }

    #[test]
    #[should_panic]
    fn test_add_overflow() {
        let mut k = ConstUint::<2>::from_digits([3223272056857775808, 9223871036854775808]);
        k += ConstUint::<2>::from_digits([1436853775203, 10023372036854775808]);
    }

    #[test]
    fn test_sub() {
        let mut n = ConstUint::<3>::from_digits([100, 50, 1]);
        n -= ConstUint::one();
        assert_eq!(n, ConstUint::from_digits([99, 50, 1]));
        assert_eq!(n - n, ConstUint::zero());

        let mut k = ConstUint::from_digits([13, 3]);
        k -= ConstUint::from_digits([30, 1]);
        assert_eq!(k, ConstUint::from_digits([ConstDigit::MAX - 16, 1]));
    }

    #[test]
    #[should_panic]
    fn test_sub_overflow() {
        let mut k = ConstUint::<2>::from_digits([1436853775203, 42]);
        k -= ConstUint::<2>::from_digits([3223272056857775808, 42]);
    }

    // #[test]
    // fn test_multiple_and_add() {
    //     const A: ConstDigit = 1537228672809129301;
    //     const B: ConstDigit = 13;

    //     const C: ConstUint<2> = {
    //         let mut dest = ConstUint::<2>::zero();
    //         multiply_and_add(&mut dest.digits, A, B);
    //         dest
    //     };

    //     multiply_and_add(&mut [], 0, 10);

    //     assert_eq!(C, ConstUint::from_digits([1537228672809129297, 1]))
    // }

    #[test]
    fn test_multiply() {
        const A: ConstUint<2> = ConstUint::from_digits([847288609443, 0]);
        const B: ConstUint<2> = ConstUint::from_digits([95367431640625, 1]);

        assert_eq!(A * B, ConstUint::from_digits([8182083744359279411, 847292989822]));
    }
}

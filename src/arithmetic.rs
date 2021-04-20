use core::ops::{Add, AddAssign, Sub, SubAssign};

use super::{ConstDigit, ConstUint};

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

        if carry {
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
        let mut i = 0;
        let mut carry = false;
        while i < DIGS {
            // TODO u64::MIN or 0? difficult choice lol
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

        if carry {
            panic!("Integer overflow");
        }
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
}

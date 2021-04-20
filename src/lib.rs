#![feature(const_panic)]

// TODO clippy::pedantic
// also when to use inline(always)

// TODO should this be a struct or something?
type ConstDigit = u64;

// TODO maybe manually implement
#[derive(Clone, PartialEq, Eq)]
pub struct ConstUint<const DIGS: usize> {
    digits: [ConstDigit; DIGS],
}

impl<const DIGS: usize> ConstUint<DIGS> {
    pub const MAX: Self = Self::from_digits([ConstDigit::MAX; DIGS]);
    pub const MIN: Self = Self::zero();
    // TODO idk deal with this (too large + usize being u32)
    // pub const BITS: u32 = if BITS * ConstDigit::BITS;

    #[inline(always)]
    pub const fn from_digits(digits: [ConstDigit; DIGS]) -> Self {
        Self { digits }
    }

    #[inline(always)]
    pub const fn zero() -> Self {
        Self::from_digits([0; DIGS])
    }

    /// Constructs a new `ConstUint` with value 1. 
    /// # Panics
    /// This function will panic if and only if the number of digits is 0.
    #[track_caller]
    #[inline(always)]
    pub const fn one() -> Self {
        if DIGS == 0 {
            panic!("Integer overflow");
        }
        let mut digits = [0; DIGS];
        digits[0] = 1;
        Self::from_digits(digits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_zero() {
        let _ = ConstUint::<0>::zero();
        let _ = ConstUint::<1>::zero();
        let _ = ConstUint::<2>::zero();
        let _ = ConstUint::<3>::zero();

        const _: ConstUint::<0> = ConstUint::zero();
        const _: ConstUint::<1> = ConstUint::zero();
        const _: ConstUint::<2> = ConstUint::zero();
        const _: ConstUint::<3> = ConstUint::zero();
    }

    #[test]
    fn test_one() {
        let _ = ConstUint::<1>::one();
        let _ = ConstUint::<2>::one();
        let _ = ConstUint::<3>::one();
        
        const _: ConstUint::<1> = ConstUint::one();
        const _: ConstUint::<2> = ConstUint::one();
        const _: ConstUint::<3> = ConstUint::one();
    }

    #[test]
    #[should_panic]
    fn test_one_overflow() {
        let _ = ConstUint::<0>::one();
    }

    // #[test]
    // #[should_fail]
    // fn test_const_one_overflow() {
    //     const _: ConstUint<0> = ConstUint::one();
    // }

    #[test]
    fn test_size_of() {
        use std::mem::size_of;
        assert_eq!(size_of::<ConstUint<0>>(), 0 * size_of::<ConstDigit>());
        assert_eq!(size_of::<ConstUint<1>>(), 1 * size_of::<ConstDigit>());
        assert_eq!(size_of::<ConstUint<2>>(), 2 * size_of::<ConstDigit>());
        assert_eq!(size_of::<ConstUint<3>>(), 3 * size_of::<ConstDigit>());
    }

    // #[test]
    // fn test_too_big() {
    //     let _ = ConstUint::<{u32::MAX as usize + 2}>::BITS;
    // }
}

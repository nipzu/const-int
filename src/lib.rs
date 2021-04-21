// TODO remove this
#![allow(incomplete_features)]
#![feature(const_panic)]
#![feature(const_mut_refs)]
#![feature(const_generics)]
#![feature(const_evaluatable_checked)]
#![feature(const_trait_impl)]
#![feature(destructuring_assignment)]
#![no_std]

use core::fmt;

mod arithmetic;
mod bits;
mod conversion;

// TODO clippy::pedantic
// also when to use inline(always)

// TODO should this be a struct or something?
type ConstDigit = u64;
type _ConstDoubleDigit = u128;

// TODO what all should be included?

/// An unsigned integer with 192 bits.
pub type U192 = ConstUint<3>;
/// An unsigned integer with 256 bits.
pub type U256 = ConstUint<4>;
/// An unsigned integer with 320 bits.
pub type U320 = ConstUint<5>;
/// An unsigned integer with 384 bits.
pub type U384 = ConstUint<6>;
/// An unsigned integer with 448 bits.
pub type U448 = ConstUint<7>;
/// An unsigned integer with 512 bits.
pub type U512 = ConstUint<8>;
/// An unsigned integer with 1024 bits.
pub type U1024 = ConstUint<16>;
/// An unsigned integer with 2048 bits.
pub type U2048 = ConstUint<32>;
/// An unsigned integer with 4096 bits.
pub type U4096 = ConstUint<64>;
/// An unsigned integer with 8192 bits.
pub type U8192 = ConstUint<128>;

// TODO do we really want copy?
// TODO is Hash const?
#[allow(clippy::derive_hash_xor_eq)]
#[derive(Eq, Clone, Copy, Hash)]
pub struct ConstUint<const DIGS: usize> {
    digits: [ConstDigit; DIGS],
}

// TODO clippy complains about this being implemented while Hash is derived,
// but it seems that this has to be manually implemented to have it be const.
impl<const DIGS: usize> const PartialEq for ConstUint<DIGS> {
    fn eq(&self, other: &Self) -> bool {
        // TODO slice comparisons are not const yet
        let mut i = 0;
        while i < DIGS {
            if self.digits[i] != other.digits[i] {
                return false;
            }
            i += 1;
        }
        true
    }
}

impl<const DIGS: usize> ConstUint<DIGS> {
    pub const MAX: Self = Self::from_digits([ConstDigit::MAX; DIGS]);
    pub const MIN: Self = Self::zero();
    // TODO idk deal with this (too large + usize being u32)
    // pub const BITS: u32 = if BITS * ConstDigit::BITS;
    // TODO don't use too much of the stack
    pub const MAX_DECIMAL_DIGITS: usize = DIGS * ConstDigit::BITS as usize / 3;

    #[inline(always)]
    const fn from_digits(digits: [ConstDigit; DIGS]) -> Self {
        Self { digits }
    }

    /// Constructs a new `ConstUint` with value 0.
    #[inline(always)]
    pub const fn zero() -> Self {
        Self::from_digits([0; DIGS])
    }

    /// Constructs a new `ConstUint` with value 1.
    /// # Panics
    /// This function will panic if and only if the number of digits is 0, that is `DIGS == 0`.
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

    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        self == Self::zero()
    }
}

impl<const DIGS: usize> fmt::Display for ConstUint<DIGS>
where
    // TODO this seems hacky but rust kinda requires it so whatever
    [(); Self::MAX_DECIMAL_DIGITS]: ,
{
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO what about format arguments
        // TODO can this be const, probably not

        // let mut num_decimal_digits = 0;
        // let mut str_buffer = [0; Self::MAX_DECIMAL_DIGITS];
        // let mut n = self.clone();
        // while !n.is_zero() {
        //     str_buffer[num_decimal_digits] = b'0' + n % 10;
        //     n /= 10;
        //     num_decimal_digits += 1;
        // }
        // SAFETY: TODO
        // let fmt_str = unsafe { core::str::from_utf8_unchecked(&str_buffer[..num_decimal_digits]) };

        // f.pad_integral(true, "", fmt_str)
        todo!()
    }
}

impl<const DIGS: usize> fmt::Debug for ConstUint<DIGS>
where
    [(); Self::MAX_DECIMAL_DIGITS]: ,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<const DIGS: usize> const Default for ConstUint<DIGS> {
    fn default() -> Self {
        Self::zero()
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

        const _: ConstUint<0> = ConstUint::zero();
        const _: ConstUint<1> = ConstUint::zero();
        const _: ConstUint<2> = ConstUint::zero();
        const _: ConstUint<3> = ConstUint::zero();
    }

    #[test]
    fn test_one() {
        let _ = ConstUint::<1>::one();
        let _ = ConstUint::<2>::one();
        let _ = ConstUint::<3>::one();

        const _: ConstUint<1> = ConstUint::one();
        const _: ConstUint<2> = ConstUint::one();
        const _: ConstUint<3> = ConstUint::one();
    }

    #[test]
    #[should_panic]
    fn test_one_overflow() {
        let _ = ConstUint::<0>::one();
    }

    #[test]
    fn test_eq() {
        const T: bool = ConstUint::<3>::zero() == ConstUint::<3>::zero();
        const F: bool = ConstUint::<3>::zero() == ConstUint::<3>::one();
        assert!(T);
        assert!(!F);
    }

    // #[test]
    // #[should_fail]
    // fn test_const_one_overflow() {
    //     const _: ConstUint<0> = ConstUint::one();
    // }

    #[test]
    fn test_size_of() {
        use core::mem::size_of;
        assert_eq!(size_of::<ConstUint<0>>(), 0 * size_of::<ConstDigit>());
        assert_eq!(size_of::<ConstUint<1>>(), 1 * size_of::<ConstDigit>());
        assert_eq!(size_of::<ConstUint<2>>(), 2 * size_of::<ConstDigit>());
        assert_eq!(size_of::<ConstUint<3>>(), 3 * size_of::<ConstDigit>());

        assert_eq!(8 * size_of::<U192>(), 192);
        assert_eq!(8 * size_of::<U256>(), 256);
        assert_eq!(8 * size_of::<U320>(), 320);
        assert_eq!(8 * size_of::<U384>(), 384);
        assert_eq!(8 * size_of::<U448>(), 448);
        assert_eq!(8 * size_of::<U512>(), 512);
        assert_eq!(8 * size_of::<U1024>(), 1024);
        assert_eq!(8 * size_of::<U2048>(), 2048);
        assert_eq!(8 * size_of::<U4096>(), 4096);
        assert_eq!(8 * size_of::<U8192>(), 8192);
    }

    // #[test]
    // fn test_too_big() {
    //     let _ = ConstUint::<{u32::MAX as usize + 2}>::BITS;
    // }
}

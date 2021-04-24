use core::fmt;

use super::{ConstDigit, ConstUint};

impl<const DIGS: usize> ConstUint<DIGS> {
    // TODO don't use too much of the stack, make sure digit is 64 bits
    const MAX_DECIMAL_DIGITS: usize = if ConstDigit::BITS == 64 {
        // 20 == ceil( log_10(2^64) )
        DIGS * 20
    } else {
        panic!("Internal error: digits should be 64 bits");
    };

    const MAX_HEX_DIGITS: usize = if ConstDigit::BITS == 64 {
        DIGS * 16
    } else {
        panic!("Internal error: digits should be 64 bits");
    };

    const MAX_OCTAL_DIGITS: usize = if ConstDigit::BITS == 64 {
        DIGS * 22
    } else {
        panic!("Internal error: digits should be 64 bits");
    };

    const MAX_BINARY_DIGITS: usize = if ConstDigit::BITS == 64 {
        DIGS * 64
    } else {
        panic!("Internal error: digits should be 64 bits");
    };

    // TODO naming on this
    // maybe use truncating_cast_into
    pub const fn cast_into<const DEST_DIGS: usize>(self) -> ConstUint<DEST_DIGS>
    where
        [(); DEST_DIGS - DIGS]: ,
    {
        self.truncating_cast_into()
    }

    pub const fn cast_from<const SOURCE_DIGS: usize>(value: ConstUint<SOURCE_DIGS>) -> Self
    where
        [(); DIGS - SOURCE_DIGS]: ,
    {
        Self::truncating_cast_from(value)
    }

    pub const fn truncating_cast_into<const DEST_DIGS: usize>(self) -> ConstUint<DEST_DIGS> {
        let mut result = ConstUint::<DEST_DIGS>::zero();
        // TODO holy hell This is hacky
        let mut i = 0;
        let smaller_digs = if DIGS > DEST_DIGS {
            DEST_DIGS
        } else {
            DIGS
        };

        while i < smaller_digs {
            result.digits[i] = self.digits[i];
            i += 1;
        }
        result
    }

    pub const fn truncating_cast_from<const SOURCE_DIGS: usize>(
        value: ConstUint<SOURCE_DIGS>,
    ) -> Self {
        let mut result = Self::zero();
        // TODO holy hell This is hacky
        let mut i = 0;
        let smaller_digs = if DIGS > SOURCE_DIGS {
            SOURCE_DIGS
        } else {
            DIGS
        };

        while i < smaller_digs {
            result.digits[i] = value.digits[i];
            i += 1;
        }
        result
    }

    pub fn try_cast_into<const DEST_DIGS: usize>(self) -> Option<ConstUint<DEST_DIGS>> {
        let mut result = ConstUint::<DEST_DIGS>::zero();
        let mut i = 0;
        while i < DIGS {
            if self.digits[i] != 0 {
                if i < DEST_DIGS {
                    result.digits[i] = self.digits[i];
                } else {
                    return None;
                }
            }
            i += 1;
        }
        Some(result)
    }

    pub fn try_cast_from<const SOURCE_DIGS: usize>(value: ConstUint<SOURCE_DIGS>) -> Option<Self> {
        let mut result = Self::zero();
        let mut i = 0;
        while i < SOURCE_DIGS {
            if value.digits[i] != 0 {
                if i < DIGS {
                    result.digits[i] = value.digits[i];
                } else {
                    return None;
                }
            }
            i += 1;
        }
        Some(result)
    }

    pub fn saturating_cast_into<const DEST_DIGS: usize>(self) -> ConstUint<DEST_DIGS> {
        if let Some(result) = self.try_cast_into() {
            result
        } else {
            ConstUint::<DEST_DIGS>::MAX
        }
    }

    pub fn saturating_cast_from<const SOURCE_DIGS: usize>(value: ConstUint<SOURCE_DIGS>) -> Self {
        if let Some(result) = Self::try_cast_from(value) {
            result
        } else {
            Self::MAX
        }
    }
}

impl<const DIGS: usize> fmt::Display for ConstUint<DIGS>
where
    // TODO this seems hacky but rust kinda requires it so whatever
    [(); Self::MAX_DECIMAL_DIGITS]: ,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if DIGS == 0 || self.is_zero() {
            return f.pad_integral(true, "", "0");
        }

        // TODO what about format arguments
        // TODO can this be const, probably not

        let mut num_decimal_digits = 0;
        let mut str_buffer = [b'0'; Self::MAX_DECIMAL_DIGITS];

        // inverse of 5 modulo 2^BITS
        let mut inverse_of_five = ConstUint::from_digits([0xCCCC_CCCC_CCCC_CCCC_u64; DIGS]);
        inverse_of_five.digits[0] += 1;
        let mut n = *self;
        while !n.is_zero() {
            let rem_by_2 = (n.digits[0] % 2) as usize;
            let mut rem_by_5 = 0;
            let mut i = 0;
            while i < DIGS {
                // if this overflows then you're probably doing something very wrong
                rem_by_5 += (n.digits[i] % 5) as usize;
                i += 1;
            }
            rem_by_5 %= 5;
            str_buffer[num_decimal_digits] = b'0' + ((6 * rem_by_5 + 5 * rem_by_2) % 10) as u8;
            n.digits[0] -= ((6 * rem_by_5 + 5 * rem_by_2) % 10) as ConstDigit;
            n >>= 1;
            n.wrapping_mul_assign(inverse_of_five);
            num_decimal_digits += 1;
        }

        str_buffer[..num_decimal_digits].reverse();

        // SAFETY: str_buffer only includes values in the range b'0'..=b'9' and is thus safe to convert to utf-8
        let fmt_str = unsafe { core::str::from_utf8_unchecked(&str_buffer[..num_decimal_digits]) };

        f.pad_integral(true, "", fmt_str)
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

impl<const DIGS: usize> fmt::LowerHex for ConstUint<DIGS>
where
    [(); Self::MAX_HEX_DIGITS]: ,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if DIGS == 0 || self.is_zero() {
            return f.pad_integral(true, "0x", "0");
        }

        const HEX_DIGITS: [u8; 16] = [
            b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd',
            b'e', b'f',
        ];

        let mut num_hex_digits = 0;
        let mut str_buffer = [b'0'; Self::MAX_HEX_DIGITS];
        let mut n = *self;
        while !n.is_zero() {
            str_buffer[num_hex_digits] = HEX_DIGITS[(n.digits[0] % 16) as usize];
            n >>= 4;
            num_hex_digits += 1;
        }

        str_buffer[..num_hex_digits].reverse();

        // SAFETY: str_buffer only includes values in the range b'0'..=b'9' or b'a'..=b'f' and is thus safe to convert to utf-8
        let fmt_str = unsafe { core::str::from_utf8_unchecked(&str_buffer[..num_hex_digits]) };

        f.pad_integral(true, "0x", fmt_str)
    }
}

impl<const DIGS: usize> fmt::UpperHex for ConstUint<DIGS>
where
    [(); Self::MAX_HEX_DIGITS]: ,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if DIGS == 0 || self.is_zero() {
            return f.pad_integral(true, "0x", "0");
        }

        const HEX_DIGITS: [u8; 16] = [
            b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'A', b'B', b'C', b'D',
            b'E', b'F',
        ];

        let mut num_hex_digits = 0;
        let mut str_buffer = [b'0'; Self::MAX_HEX_DIGITS];
        let mut n = *self;
        while !n.is_zero() {
            str_buffer[num_hex_digits] = HEX_DIGITS[(n.digits[0] % 16) as usize];
            n >>= 4;
            num_hex_digits += 1;
        }

        str_buffer[..num_hex_digits].reverse();

        // SAFETY: str_buffer only includes values in the range b'0'..=b'9' or b'A'..=b'F' and is thus safe to convert to utf-8
        let fmt_str = unsafe { core::str::from_utf8_unchecked(&str_buffer[..num_hex_digits]) };

        f.pad_integral(true, "0x", fmt_str)
    }
}

impl<const DIGS: usize> fmt::Octal for ConstUint<DIGS>
where
    [(); Self::MAX_OCTAL_DIGITS]: ,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if DIGS == 0 || self.is_zero() {
            return f.pad_integral(true, "0o", "0");
        }

        let mut num_octal_digits = 0;
        let mut str_buffer = [b'0'; Self::MAX_OCTAL_DIGITS];
        let mut n = *self;
        while !n.is_zero() {
            str_buffer[num_octal_digits] = b'0' + (n.digits[0] % 8) as u8;
            n >>= 3;
            num_octal_digits += 1;
        }

        str_buffer[..num_octal_digits].reverse();

        // SAFETY: str_buffer only includes values in the range b'0'..=b'7' and is thus safe to convert to utf-8
        let fmt_str = unsafe { core::str::from_utf8_unchecked(&str_buffer[..num_octal_digits]) };

        f.pad_integral(true, "0o", fmt_str)
    }
}

impl<const DIGS: usize> fmt::Binary for ConstUint<DIGS>
where
    [(); Self::MAX_BINARY_DIGITS]: ,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if DIGS == 0 || self.is_zero() {
            return f.pad_integral(true, "0b", "0");
        }

        let mut num_binary_digits = 0;
        let mut str_buffer = [b'0'; Self::MAX_BINARY_DIGITS];
        let mut n = *self;
        while !n.is_zero() {
            str_buffer[num_binary_digits] = b'0' + (n.digits[0] % 2) as u8;
            n >>= 1;
            num_binary_digits += 1;
        }

        str_buffer[..num_binary_digits].reverse();

        // SAFETY: str_buffer only includes values in the range b'0'..=b'7' and is thus safe to convert to utf-8
        let fmt_str = unsafe { core::str::from_utf8_unchecked(&str_buffer[..num_binary_digits]) };

        f.pad_integral(true, "0b", fmt_str)
    }
}

macro_rules! impl_from_uint {
    ($t:ty) => {
        impl<const DIGS: usize> const From<$t> for ConstUint<DIGS>
        where
            [(); DIGS - 1]: ,
        {
            fn from(value: $t) -> Self {
                let mut result = Self::zero();
                // TODO make sure $t is not bigger than ConstDigit
                result.digits[0] = value as ConstDigit;
                result
            }
        }
    };
}

impl_from_uint!(u8);
impl_from_uint!(u16);
impl_from_uint!(u32);
impl_from_uint!(u64);

impl<const DIGS: usize> const From<u128> for ConstUint<DIGS>
where
    [(); DIGS - 2]: ,
{
    fn from(value: u128) -> Self {
        let mut result = Self::zero();
        // TODO make sure ConstDigit is 64 bits
        result.digits[0] = value as ConstDigit;
        result.digits[1] = (value >> ConstDigit::BITS) as ConstDigit;
        result
    }
}

// impl<const DIGS: usize, const VALUE_DIGS: usize> const From<ConstUint<VALUE_DIGS>> for ConstUint<DIGS> where [(); DIGS - VALUE_DIGS]: {
//     fn from(value: ConstUint<VALUE_DIGS>) -> Self {
//         let mut result = Self::zero();
//         result.digits[0..VALUE_DIGS] = value.digits;
//         result
//     }
// }

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    #[test]
    fn test_display() {
        const A: ConstUint<2> = ConstUint::from_digits([12157665459056928801, 298023223876953125]);

        assert_eq!(
            std::format!("{}", A),
            "5497558138880000012157665459056928801"
        );

        assert_eq!(std::format!("{}", ConstUint::<2>::zero()), "0");
    }

    #[test]
    fn test_debug() {
        const A: ConstUint<2> = ConstUint::from_digits([12157665459056928801, 298023223876953125]);

        assert_eq!(
            std::format!("{:?}", A),
            "5497558138880000012157665459056928801"
        );

        assert_eq!(std::format!("{:?}", ConstUint::<2>::zero()), "0");
    }

    #[test]
    fn test_upper_hex() {
        const A: ConstUint<2> = ConstUint::from_digits([12157665459056928801, 298023223876953125]);

        assert_eq!(std::format!("{:X}", A), "422CA8B0A00A425A8B8B452291FE821");

        assert_eq!(
            std::format!("{:#X}", A),
            "0x422CA8B0A00A425A8B8B452291FE821"
        );

        assert_eq!(std::format!("{:X}", ConstUint::<2>::zero()), "0");

        assert_eq!(std::format!("{:#X}", ConstUint::<2>::zero()), "0x0");
    }

    #[test]
    fn test_lower_hex() {
        const A: ConstUint<2> = ConstUint::from_digits([12157665459056928801, 298023223876953125]);

        assert_eq!(std::format!("{:x}", A), "422ca8b0a00a425a8b8b452291fe821");

        assert_eq!(
            std::format!("{:#x}", A),
            "0x422ca8b0a00a425a8b8b452291fe821"
        );

        assert_eq!(std::format!("{:x}", ConstUint::<2>::zero()), "0");

        assert_eq!(std::format!("{:#x}", ConstUint::<2>::zero()), "0x0");
    }

    #[test]
    fn test_octal() {
        const A: ConstUint<2> = ConstUint::from_digits([12157665459056928801, 298023223876953125]);

        assert_eq!(
            std::format!("{:o}", A),
            "41054521302400244113242705505105107764041"
        );

        assert_eq!(
            std::format!("{:#o}", A),
            "0o41054521302400244113242705505105107764041"
        );

        assert_eq!(std::format!("{:o}", ConstUint::<2>::zero()), "0");

        assert_eq!(std::format!("{:#o}", ConstUint::<2>::zero()), "0o0");
    }

    #[test]
    fn test_binary() {
        const A: ConstUint<2> = ConstUint::from_digits([12157665459056928801, 298023223876953125]);

        assert_eq!(
            std::format!("{:b}", A),
            "100001000101100101010001011000010100000000010100100001001011010100010111000101101000101001000101001000111111110100000100001"
        );

        assert_eq!(
            std::format!("{:#b}", A),
            "0b100001000101100101010001011000010100000000010100100001001011010100010111000101101000101001000101001000111111110100000100001"
        );

        assert_eq!(std::format!("{:b}", ConstUint::<2>::zero()), "0");

        assert_eq!(std::format!("{:#b}", ConstUint::<2>::zero()), "0b0");
    }

    #[test]
    fn test_from_uint() {
        const A: ConstUint<2> = ConstUint::from(123u8);
        assert_eq!(A, ConstUint::from_digits([123, 0]));

        const B: ConstUint<2> = ConstUint::from(123u16);
        assert_eq!(B, ConstUint::from_digits([123, 0]));

        const C: ConstUint<2> = ConstUint::from(123u32);
        assert_eq!(C, ConstUint::from_digits([123, 0]));

        const D: ConstUint<2> = ConstUint::from(123u64);
        assert_eq!(D, ConstUint::from_digits([123, 0]));

        const E: ConstUint<2> = ConstUint::from(123u64);
        assert_eq!(E, ConstUint::from_digits([123, 0]));
    }
}

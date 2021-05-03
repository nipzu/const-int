use core::fmt;

#[derive(Debug, PartialEq)]
pub struct ParseConstIntError {
    kind: ConstIntErrorKind,
}

impl ParseConstIntError {
    pub(crate) const fn empty() -> Self {
        ParseConstIntError {
            kind: ConstIntErrorKind::Empty,
        }
    }

    pub(crate) const fn invalid_digit() -> Self {
        ParseConstIntError {
            kind: ConstIntErrorKind::InvalidDigit,
        }
    }

    pub(crate) const fn overflow() -> Self {
        ParseConstIntError {
            kind: ConstIntErrorKind::Overflow,
        }
    }
}

#[derive(Debug, PartialEq)]
#[non_exhaustive]
pub enum ConstIntErrorKind {
    Empty,
    InvalidDigit,
    Overflow,
}

impl fmt::Display for ParseConstIntError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self.kind {
            ConstIntErrorKind::Empty => "cannot parse integer from empty string",
            ConstIntErrorKind::InvalidDigit => "invalid digit found in string",
            ConstIntErrorKind::Overflow => "number does not fit in target type",
        };

        write!(f, "{}", message)
    }
}

// TODO this needs std
// impl Error for ParseConstIntError {

// }
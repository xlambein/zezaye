use std::{
    convert::{TryFrom, TryInto},
    error::Error,
    fmt,
    ops::{Range, RangeFrom, RangeTo},
};

use intbits::*;

const fn msbits(length: usize, bits: &[u8]) -> u64 {
    let mut acc = 0;
    let mut k = 1;

    let mut i = 0;
    while i < bits.len() {
        if bits[i] == b'1' {
            acc += 1 << length - k;
            k += 1;
        } else if bits[i] == b'0' {
            k += 1;
        }

        i += 1;
    }
    acc
}

//                                    Sign |      Exponent | Quiet | Tag | Payload (48 bits)
const QNAN: u64 = msbits(64, b"          1 | 111_1111_1111 |     1 | 000");
const SNAN_HEADER: u64 = msbits(64, b"   1 | 111_1111_1111 |     0 | 000");

#[derive(Debug, Clone)]
pub enum ParseError {
    TagParseError(u64),
    ImmTagParseError(u64),
}

impl Error for ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::TagParseError(tag) => write!(f, "invalid tag {:#03b}", *tag),
            ParseError::ImmTagParseError(tag) => {
                write!(f, "invalid immediate tag {:#016b}", *tag)
            }
        }
    }
}

#[repr(u64)]
enum Tag {
    Immediate = 0,
    Pair,
    Vector,
    String,
    Symbol,
    Closure,
    // Two more available
}

impl TryFrom<u64> for Tag {
    type Error = ParseError;

    fn try_from(x: u64) -> Result<Self, Self::Error> {
        match x {
            x if x == Tag::Immediate as u64 => Ok(Tag::Immediate),
            x if x == Tag::Pair as u64 => Ok(Tag::Pair),
            x if x == Tag::Vector as u64 => Ok(Tag::Vector),
            x if x == Tag::String as u64 => Ok(Tag::String),
            x if x == Tag::Symbol as u64 => Ok(Tag::Symbol),
            x if x == Tag::Closure as u64 => Ok(Tag::Closure),
            _ => Err(ParseError::TagParseError(x)),
        }
    }
}

#[repr(u64)]
enum ImmTag {
    Int = 1, // Start at one to avoid empty mantissa
    Char,
    Bool,
    Nil,
}

impl TryFrom<u64> for ImmTag {
    type Error = ParseError;

    fn try_from(x: u64) -> Result<Self, Self::Error> {
        match x {
            x if x == ImmTag::Int as u64 => Ok(ImmTag::Int),
            x if x == ImmTag::Char as u64 => Ok(ImmTag::Char),
            x if x == ImmTag::Bool as u64 => Ok(ImmTag::Bool),
            x if x == ImmTag::Nil as u64 => Ok(ImmTag::Nil),
            _ => Err(ParseError::ImmTagParseError(x)),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    Float(f64),
    Int(i32),
    Char(u8),
    Bool(bool),
    Nil,
    Pair(Box<Object>, Box<Object>),
    Symbol(String),
}

const HEADER: RangeFrom<usize> = 51..;
const TAG: Range<usize> = 48..51;
const PAYLOAD: RangeTo<usize> = ..48;
const IMM_TAG: Range<usize> = 32..48;

impl Object {
    pub fn to_word(&self) -> u64 {
        match self {
            Object::Float(f) => {
                if f.is_nan() {
                    QNAN
                } else {
                    f.to_bits()
                }
            }
            Object::Int(i) => {
                SNAN_HEADER
                    .with_bits(TAG, Tag::Immediate as u64)
                    .with_bits(IMM_TAG, ImmTag::Int as u64)
                    | *i as u32 as u64
            }
            Object::Char(c) => {
                SNAN_HEADER
                    .with_bits(TAG, Tag::Immediate as u64)
                    .with_bits(IMM_TAG, ImmTag::Char as u64)
                    | *c as u64
            }
            Object::Bool(b) => SNAN_HEADER
                .with_bits(TAG, Tag::Immediate as u64)
                .with_bits(IMM_TAG, ImmTag::Bool as u64)
                .with_bit(0, *b),
            Object::Nil => SNAN_HEADER
                .with_bits(TAG, Tag::Immediate as u64)
                .with_bits(IMM_TAG, ImmTag::Nil as u64),
            Object::Pair(_, _) => todo!(),
            Object::Symbol(_) => todo!(),
        }
    }

    pub fn parse_word(word: u64) -> Result<Self, ParseError> {
        let header = word.bits(HEADER);
        let tag = word.bits(TAG).try_into()?;
        let payload = word.bits(PAYLOAD);

        // Non-float
        if header == 0b1_111_1111_1111_0 {
            match tag {
                Tag::Immediate => match payload.bits(IMM_TAG).try_into()? {
                    ImmTag::Int => Ok(Object::Int(payload as u32 as i32)),
                    ImmTag::Char => Ok(Object::Char(payload as u8)),
                    ImmTag::Bool => Ok(Object::Bool(payload.bit(0))),
                    ImmTag::Nil => Ok(Object::Nil),
                },
                Tag::Pair => todo!(),
                Tag::Vector => todo!(),
                Tag::String => todo!(),
                Tag::Symbol => todo!(),
                Tag::Closure => todo!(),
            }
        } else {
            Ok(Object::Float(f64::from_bits(word)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_mask() {
        assert_eq!(msbits(10, b"1010     0 01"), 0b1010_0_01_000);
        assert_eq!(msbits(12, b"1100_01 11   "), 0b1100_01_11_0000);
    }

    macro_rules! assert_obj_is_nan {
        ($obj:expr) => {
            assert!(f64::from_bits($obj.to_word()).is_nan());
        };
    }

    #[test]
    fn test_object_to_word() {
        // Float
        assert_eq!(f64::from_bits(Object::Float(3.14).to_word()), 3.14);
        assert_eq!(f64::from_bits(Object::Float(-2e5).to_word()), -2e5);
        assert_obj_is_nan!(Object::Float(f64::NAN));

        // Int
        assert_obj_is_nan!(Object::Int(314));
        assert_eq!(Object::Int(314).to_word() as u32, 314);
        assert_eq!(Object::Int(-10).to_word() as u32 as i32, -10);

        // Char
        assert_obj_is_nan!(Object::Char(b'x'));
        assert_eq!(Object::Char(b'x').to_word() as u8, b'x');
        assert_eq!(Object::Char(0).to_word() as u8, 0);

        // Bool
        assert_obj_is_nan!(Object::Bool(true));
        assert_eq!(Object::Bool(false).to_word().bit(0), false);
        assert_eq!(Object::Bool(true).to_word().bit(0), true);

        // Nil
        assert_obj_is_nan!(Object::Nil);
    }

    macro_rules! assert_parse_word_identity {
        ($obj:expr) => {
            assert_eq!(Object::parse_word(($obj).to_word())?, $obj);
        };
    }

    #[test]
    fn test_object_parse_word() -> Result<(), ParseError> {
        // Float
        assert_parse_word_identity!(Object::Float(3.14));
        assert_parse_word_identity!(Object::Float(-2e5));
        if let Ok(Object::Float(f)) = Object::parse_word(Object::Float(f64::NAN).to_word()) {
            assert!(f.is_nan());
        } else {
            assert!(false, "NaN did not parse to Object::Float");
        }

        // Int
        assert_parse_word_identity!(Object::Int(314));
        assert_parse_word_identity!(Object::Int(-10));
        assert_parse_word_identity!(Object::Int(0));

        // Char
        assert_parse_word_identity!(Object::Char(b'x'));
        assert_parse_word_identity!(Object::Char(0));

        // Bool
        assert_parse_word_identity!(Object::Bool(false));
        assert_parse_word_identity!(Object::Bool(true));

        // Nil
        assert_parse_word_identity!(Object::Nil);

        Ok(())
    }
}

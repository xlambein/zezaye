use std::{iter::Peekable, num, str::Chars};
use thiserror::Error;

use crate::object::Object;

#[derive(Error, Debug, PartialEq)]
pub enum ReaderError {
    #[error("unexpected EOI")]
    UnexpectedEoi,
    #[error("unexpected character '{0}' while reading symbol")]
    UnexpectedCharInSymbol(char),
    #[error("int parsing error")]
    ParseIntError(#[from] num::ParseIntError),
    #[error("float parsing error")]
    ParseFloatError(#[from] num::ParseFloatError),
    #[error("undefined hash literal #{0}")]
    ParseHashLiteralError(String),
    #[error(r"unsupported character literal #\{0}")]
    UnsupportedCharacterLiteral(char),
}

type Result<T> = std::result::Result<T, ReaderError>;

pub struct Reader<'a> {
    src: Peekable<Chars<'a>>,
}

impl<'a> Reader<'a> {
    pub fn from_chars(src: Chars<'a>) -> Self {
        Self {
            src: src.peekable(),
        }
    }

    pub fn from_str(src: &'a str) -> Self {
        Self::from_chars(src.chars())
    }

    fn next(&mut self) -> Option<char> {
        self.src.next()
    }

    fn try_next(&mut self) -> Result<char> {
        self.next().ok_or(ReaderError::UnexpectedEoi)
    }

    fn peek(&mut self) -> Option<char> {
        self.src.peek().cloned()
    }

    fn try_peek(&mut self) -> Result<char> {
        self.peek().ok_or(ReaderError::UnexpectedEoi)
    }

    fn skip_whitespaces(&mut self) {
        while let Some(_) = self.src.next_if(char::is_ascii_whitespace) {}
    }

    pub fn read(&mut self) -> Result<Vec<Object>> {
        let mut exprs = vec![];
        while let Some(_) = self.peek() {
            exprs.push(self.read_expr()?);
            self.skip_whitespaces();
        }
        Ok(exprs)
    }

    pub fn read_expr(&mut self) -> Result<Object> {
        self.skip_whitespaces();
        let c = self.try_next()?;

        if c == '(' {
            self.read_list()
        } else if c == '-' || c == '+' {
            if self.peek().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                self.read_number(c.to_string())
            } else {
                self.read_symbol(c.to_string())
            }
        } else if c.is_ascii_digit() {
            self.read_number(c.to_string())
        } else if c == '#' {
            if self.peek().map(|c| c == '\\').unwrap_or(false) {
                self.next().unwrap();
                self.read_char_literal()
            } else {
                self.read_hash_literal()
            }
        } else {
            // TODO restrict characters
            self.read_symbol(c.to_string())
        }
    }

    fn read_list(&mut self) -> Result<Object> {
        self.skip_whitespaces();
        if self.try_peek()? == ')' {
            self.next().unwrap();
            return Ok(Object::Nil);
        }
        Ok(Object::Pair(box self.read_expr()?, box self.read_list()?))
    }

    fn read_number(&mut self, mut acc: String) -> Result<Object> {
        let mut float = false;
        while let Some(c) = self.peek() {
            if c.is_ascii_whitespace() || c == ')' {
                break;
            } else if c == '.' || c == 'e' || c == 'E' {
                float = true;
            }
            // We accept any character, and let Rust's int/float parser report errors
            acc.push(c);
            self.next().unwrap();
        }
        if float {
            Ok(Object::Float(acc.parse()?))
        } else {
            Ok(Object::Int(acc.parse()?))
        }
    }

    fn read_symbol(&mut self, mut acc: String) -> Result<Object> {
        while let Some(c) = self.peek() {
            if c.is_ascii_whitespace() || c == ')' {
                break;
            } else if c.is_alphanumeric() || c.is_ascii_punctuation() {
                acc.push(c);
                self.next().unwrap();
            } else {
                return Err(ReaderError::UnexpectedCharInSymbol(c));
            }
        }
        Ok(Object::Symbol(acc))
    }

    fn read_char_literal(&mut self) -> Result<Object> {
        let c = self.try_next()?;
        if c.is_ascii() {
            Ok(Object::Char(c as u8))
        } else {
            Err(ReaderError::UnsupportedCharacterLiteral(c))
        }
    }

    fn read_hash_literal(&mut self) -> Result<Object> {
        let mut acc = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_whitespace() || c == ')' {
                break;
            }
            acc.push(c);
            self.next().unwrap();
        }
        match acc.as_str() {
            "f" => Ok(Object::Bool(false)),
            "t" => Ok(Object::Bool(true)),
            _ => Err(ReaderError::ParseHashLiteralError(acc)),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_read_expr_symbol() -> Result<()> {
        assert_eq!(
            Reader::from_str("hello-world").read_expr()?,
            Object::Symbol("hello-world".to_owned())
        );
        assert_eq!(
            Reader::from_str("a1234)").read_expr()?,
            Object::Symbol("a1234".to_owned())
        );
        assert_eq!(
            Reader::from_str("  -ish  ").read_expr()?,
            Object::Symbol("-ish".to_owned())
        );
        assert_eq!(
            Reader::from_str("+").read_expr()?,
            Object::Symbol("+".to_owned())
        );
        assert_eq!(
            Reader::from_str("リスプ\n").read_expr()?,
            Object::Symbol("リスプ".to_owned())
        );
        Ok(())
    }

    #[test]
    fn test_read_expr_number() -> Result<()> {
        // Successful
        assert_eq!(Reader::from_str("1234").read_expr()?, Object::Int(1234));
        assert_eq!(Reader::from_str("-12)").read_expr()?, Object::Int(-12));
        assert_eq!(Reader::from_str("  +500  ").read_expr()?, Object::Int(500));
        assert_eq!(
            Reader::from_str("123.45").read_expr()?,
            Object::Float(123.45)
        );
        assert_eq!(Reader::from_str("-3.14").read_expr()?, Object::Float(-3.14));
        assert_eq!(Reader::from_str("2.1e3").read_expr()?, Object::Float(2.1e3));
        assert_eq!(Reader::from_str("27E-1").read_expr()?, Object::Float(27E-1));

        // Failed
        assert_eq!(
            Reader::from_str("123abc").read_expr(),
            Err(ReaderError::ParseIntError(
                "123abc".parse::<i32>().unwrap_err()
            ))
        );
        assert_eq!(
            Reader::from_str("12.34.56").read_expr(),
            Err(ReaderError::ParseFloatError(
                "12.34.56".parse::<f64>().unwrap_err()
            ))
        );
        assert_eq!(
            Reader::from_str("12e34e56").read_expr(),
            Err(ReaderError::ParseFloatError(
                "12e34e56".parse::<f64>().unwrap_err()
            ))
        );
        Ok(())
    }

    #[test]
    fn test_read_expr_bool() -> Result<()> {
        // Success
        assert_eq!(Reader::from_str(" \n#f ").read_expr()?, Object::Bool(false));
        assert_eq!(Reader::from_str("#t)").read_expr()?, Object::Bool(true));

        // Failure
        assert_eq!(
            Reader::from_str("#false").read_expr(),
            Err(ReaderError::ParseHashLiteralError("false".to_owned()))
        );
        Ok(())
    }

    #[test]
    fn test_read_expr_char() -> Result<()> {
        // Success
        assert_eq!(Reader::from_str(r"#\a").read_expr()?, Object::Char(b'a'));
        assert_eq!(Reader::from_str(r"#\ ").read_expr()?, Object::Char(b' '));
        assert_eq!(Reader::from_str(r"#\\").read_expr()?, Object::Char(b'\\'));

        // Failure
        // TODO these should no longer fail when non-ASCII character literals are handled
        assert_eq!(
            Reader::from_str(r"#\é").read_expr(),
            Err(ReaderError::UnsupportedCharacterLiteral('é'))
        );
        assert_eq!(
            Reader::from_str(r"#\🙄").read_expr(),
            Err(ReaderError::UnsupportedCharacterLiteral('🙄'))
        );
        Ok(())
    }

    #[test]
    fn test_read_expr_list() -> Result<()> {
        assert_eq!(
            Reader::from_str("(+ 12 34)").read_expr()?,
            Object::Pair(
                box Object::Symbol("+".to_owned()),
                box Object::Pair(
                    box Object::Int(12),
                    box Object::Pair(box Object::Int(34), box Object::Nil)
                )
            )
        );
        assert_eq!(
            Reader::from_str("( foo bar )").read_expr()?,
            Object::Pair(
                box Object::Symbol("foo".to_owned()),
                box Object::Pair(box Object::Symbol("bar".to_owned()), box Object::Nil)
            )
        );
        assert_eq!(
            Reader::from_str("((λ x x) y)").read_expr()?,
            Object::Pair(
                box Object::Pair(
                    box Object::Symbol("λ".to_owned()),
                    box Object::Pair(
                        box Object::Symbol("x".to_owned()),
                        box Object::Pair(box Object::Symbol("x".to_owned()), box Object::Nil)
                    )
                ),
                box Object::Pair(box Object::Symbol("y".to_owned()), box Object::Nil)
            )
        );
        Ok(())
    }
}

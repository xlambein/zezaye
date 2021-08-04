use std::{iter::Peekable, num, str::Chars};
use thiserror::Error;

use crate::object::Object;

#[derive(Error, Debug, PartialEq)]
pub enum ReaderError {
    #[error("unexpected EOI")]
    UnexpectedEoi,
    #[error("unexpected character '{0}' while reading number")]
    UnexpectedCharInNumber(char),
    #[error("unexpected character '{0}' while reading symbol")]
    UnexpectedCharInSymbol(char),
    #[error("int parsing error")]
    ParseIntError(#[from] num::ParseIntError),
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
            self.skip_whitespaces();
            exprs.push(self.read_expr()?);
        }
        Ok(exprs)
    }

    fn read_list(&mut self) -> Result<Object> {
        self.skip_whitespaces();
        if self.try_peek()? == ')' {
            self.next().unwrap();
            return Ok(Object::Nil);
        }
        Ok(Object::Pair(box self.read_expr()?, box self.read_list()?))
    }

    pub fn read_expr(&mut self) -> Result<Object> {
        // We assume `c` isn't a whitespace
        let c = self.try_next()?;

        if c == '(' {
            self.read_list()
        } else if c == '-' || c == '+' {
            if self.try_peek()?.is_ascii_digit() {
                self.read_number(c.to_string())
            } else {
                self.read_symbol(c.to_string())
            }
        } else if c.is_ascii_digit() {
            self.read_number(c.to_string())
        } else {
            // TODO restrict characters
            self.read_symbol(c.to_string())
        }
    }

    fn read_number(&mut self, mut acc: String) -> Result<Object> {
        while let Some(c) = self.peek() {
            if c.is_ascii_whitespace() || c == ')' {
                break;
            } else if c.is_ascii_digit() {
                acc.push(c);
                self.next().unwrap();
            } else {
                return Err(ReaderError::UnexpectedCharInNumber(c));
            }
        }
        Ok(Object::Int(acc.parse()?))
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
            Reader::from_str("-ish  ").read_expr()?,
            Object::Symbol("-ish".to_owned())
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
        assert_eq!(Reader::from_str("+500  ").read_expr()?, Object::Int(500));

        // Failed
        assert_eq!(
            Reader::from_str("123abc").read_expr(),
            Err(ReaderError::UnexpectedCharInNumber('a'))
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

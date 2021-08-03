use crate::object::Object;
use crate::program_buffer::{ByteRegister, Indirect, ProgramBuffer, Register, Setcc};

const WORD_SIZE: i64 = 8;

pub struct Compiler<'buffer> {
    buffer: &'buffer mut ProgramBuffer,
}

impl<'buffer> Compiler<'buffer> {
    pub fn new(buffer: &'buffer mut ProgramBuffer) -> Self {
        Self { buffer }
    }

    fn compare_imm_header(&mut self, target: Object) {
        self.buffer
            .shr_reg_imm8(Register::Rax, 32)
            .cmp_reg_imm32(Register::Rax, (target.to_word() >> 32) as u32)
            .mov_reg_imm64(Register::Rax, Object::Bool(false).to_word())
            .setcc_imm8(Setcc::Equal, ByteRegister::Al);
    }

    fn args(&mut self, args: &Object, stack_index: i64) -> i64 {
        if let Object::Pair(box car, box cdr) = args {
            match cdr {
                Object::Nil => {
                    self.expr(car, stack_index);
                    stack_index
                }
                Object::Pair(_, _) => {
                    let stack_index = self.args(cdr, stack_index);
                    self.buffer.store_reg_indirect(
                        Indirect(Register::Rbp, stack_index as i8),
                        Register::Rax,
                    );
                    // TODO handle stack index bigger than a byte
                    let stack_index = stack_index - WORD_SIZE;
                    self.expr(car, stack_index);
                    stack_index
                }
                _ => panic!("expected pair or nil"),
            }
        } else {
            panic!("expected pair");
        }
    }

    fn call(&mut self, name: &str, args: &Object, stack_index: i64) {
        // TODO check arity before making call
        self.args(args, stack_index);
        match name {
            "add1" => {
                self.buffer.add_reg_imm32(Register::Rax, 1);
            }
            "sub1" => {
                self.buffer.sub_reg_imm32(Register::Rax, 1);
            }
            "int?" => {
                self.compare_imm_header(Object::Int(0));
            }
            "char?" => {
                self.compare_imm_header(Object::Char(0));
            }
            "bool?" => {
                self.compare_imm_header(Object::Bool(false));
            }
            "nil?" => {
                self.compare_imm_header(Object::Nil);
            }
            "+" => {
                // Erase the upper bits of RAX
                self.buffer.store_reg_reg_32(Register::Rax, Register::Rax);
                // Add RAX to the second arg
                self.buffer
                    .add_reg_indirect(Register::Rax, Indirect(Register::Rbp, stack_index as i8));
            }
            _ => {
                panic!("undefined function '{}'", name);
            }
        }
    }

    fn expr(&mut self, obj: &Object, stack_index: i64) {
        match obj {
            Object::Pair(box car, box cdr) => {
                if let Object::Symbol(s) = car {
                    self.call(s, cdr, stack_index);
                } else {
                    panic!("expected symbol in function call name");
                }
            }
            _ => {
                self.buffer.mov_reg_imm64(Register::Rax, obj.to_word());
            }
        }
    }

    pub fn function(&mut self, obj: &Object) {
        self.buffer.prologue();
        self.expr(obj, -8);
        self.buffer.epilogue();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use color_eyre::Result;

    #[test]
    fn test_compile_positive_integer() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&Object::Int(1234));
        // assert_eq!(
        //     buffer.as_slice(),
        //     // rex movabs rax $imm; ret
        //     &[0x48, 0xb8, 210, 4, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff, 0xc3]
        // );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_negative_integer() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&Object::Int(-1234));
        // assert_eq!(
        //     buffer.as_slice(),
        //     // rex mov rax $imm; ret
        //     &[0x48, 0xb8, 0x2e, 0xfb, 0xff, 0xff, 0x01, 0x00, 0xf0, 0xff, 0xc3]
        // );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Int(-1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_char() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&Object::Char(b'x'));
        // assert_eq!(
        //     buffer.as_slice(),
        //     // rex mov rax $imm; ret
        //     &[0x48, 0xb8, b'x', 0x00, 0x00, 0x00, 0x02, 0x00, 0xf0, 0xff, 0xc3]
        // );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Char(b'x')
            );
        }
        Ok(())
    }

    fn unary_call(name: impl Into<String>, arg: Object) -> Object {
        Object::Pair(
            box Object::Symbol(name.into()),
            box Object::Pair(box arg, box Object::Nil),
        )
    }

    fn binary_call(name: impl Into<String>, arg0: Object, arg1: Object) -> Object {
        Object::Pair(
            box Object::Symbol(name.into()),
            box Object::Pair(box arg0, box Object::Pair(box arg1, box Object::Nil)),
        )
    }

    #[test]
    fn test_compile_add1() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("add1", Object::Int(41)));
        #[rustfmt::skip]
        assert_eq!(
            buffer.as_slice(),
            &[
                // Prologue
                0x55, 0x48, 0x89, 0xE5,
                // rex mov rax $imm
                0x48, 0xb8, 41, 0x00, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff,
                // rex add rax $1
                0x48, 0x81, 0xc0, 1, 0x00, 0x00, 0x00,
                // Epilogue
                0x48, 0x89, 0xEC, 0x5D, 0xc3,
            ]
        );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Int(42)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_add1_nested() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer)
            .function(&unary_call("add1", unary_call("add1", Object::Int(1232))));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_sub1() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("sub1", Object::Int(1235)));
        #[rustfmt::skip]
        assert_eq!(
            buffer.as_slice(),
            &[
                // Prologue
                0x55, 0x48, 0x89, 0xE5,
                // rex mov rax $imm
                0x48, 0xb8, 0xd3, 0x04, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff,
                // rex sub rax $1; ret
                0x48, 0x81, 0xe8, 1, 0x00, 0x00, 0x00,
                // Epilogue
                0x48, 0x89, 0xEC, 0x5D, 0xc3,
            ]
        );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_int_true() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("int?", Object::Int(10)));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Bool(true)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_int_false() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("int?", Object::Bool(true)));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Bool(false)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_nil_true() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("nil?", Object::Nil));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Bool(true)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_nil_false() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("nil?", Object::Int(1)));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Bool(false)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_plus() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&binary_call("+", Object::Int(1), Object::Int(2)));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Int(3)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_plus_nested() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&binary_call(
            "+",
            binary_call("+", Object::Int(1), Object::Int(2)),
            binary_call("+", Object::Int(3), Object::Int(4)),
        ));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Int(10)
            );
        }
        Ok(())
    }
}

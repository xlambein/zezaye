#![feature(box_syntax, box_patterns, allocator_api, nonnull_slice_from_raw_parts)]

use color_eyre::Result;

mod object;
mod program_buffer;

use object::Object;

use program_buffer::{ByteRegister, Indirect, ProgramBuffer, Register, Setcc};

const WORD_SIZE: i64 = 8;

fn compile_compare_imm_header(buffer: &mut ProgramBuffer, target: Object) {
    buffer
        .shr_reg_imm8(Register::Rax, 32)
        .cmp_reg_imm32(Register::Rax, (target.to_word() >> 32) as u32)
        .mov_reg_imm64(Register::Rax, Object::Bool(false).to_word())
        .setcc_imm8(Setcc::Equal, ByteRegister::Al);
}

fn compile_args(buffer: &mut ProgramBuffer, args: &Object, stack_index: i64) -> i64 {
    if let Object::Pair(box car, box cdr) = args {
        match cdr {
            Object::Nil => {
                compile_expr(buffer, car, stack_index);
                stack_index
            }
            Object::Pair(_, _) => {
                let stack_index = compile_args(buffer, cdr, stack_index);
                buffer
                    .store_reg_indirect(Indirect(Register::Rbp, stack_index as i8), Register::Rax);
                // TODO handle stack index bigger than a byte
                let stack_index = stack_index - WORD_SIZE;
                compile_expr(buffer, car, stack_index);
                stack_index
            }
            _ => panic!("expected pair or nil"),
        }
    } else {
        panic!("expected pair");
    }
}

fn compile_call(buffer: &mut ProgramBuffer, name: &str, args: &Object, stack_index: i64) {
    // TODO check arity before making call
    compile_args(buffer, args, stack_index);
    match name {
        "add1" => {
            buffer.add_reg_imm32(Register::Rax, 1);
        }
        "sub1" => {
            buffer.sub_reg_imm32(Register::Rax, 1);
        }
        "int?" => {
            compile_compare_imm_header(buffer, Object::Int(0));
        }
        "char?" => {
            compile_compare_imm_header(buffer, Object::Char(0));
        }
        "bool?" => {
            compile_compare_imm_header(buffer, Object::Bool(false));
        }
        "nil?" => {
            compile_compare_imm_header(buffer, Object::Nil);
        }
        "+" => {
            // Erase the upper bits of RAX
            buffer.store_reg_reg_32(Register::Rax, Register::Rax);
            // Add RAX to the second arg
            buffer.add_reg_indirect(Register::Rax, Indirect(Register::Rbp, stack_index as i8));
        }
        _ => {
            panic!("undefined function '{}'", name);
        }
    }
}

fn compile_expr(buffer: &mut ProgramBuffer, obj: &Object, stack_index: i64) {
    match obj {
        Object::Pair(box car, box cdr) => {
            if let Object::Symbol(s) = car {
                compile_call(buffer, s, cdr, stack_index);
            } else {
                panic!("expected symbol in function call name");
            }
        }
        _ => {
            buffer.mov_reg_imm64(Register::Rax, obj.to_word());
        }
    }
}

fn compile_function(buffer: &mut ProgramBuffer, obj: &Object) {
    buffer.prologue();
    compile_expr(buffer, obj, -8);
    buffer.epilogue();
}

fn main() -> Result<()> {
    color_eyre::install()?;

    let mut buffer = ProgramBuffer::new();
    compile_function(&mut buffer, &Object::Int(1234));

    unsafe {
        dbg!(buffer.make_executable().execute::<i32>());
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_positive_integer() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        compile_function(&mut buffer, &Object::Int(1234));
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
        compile_function(&mut buffer, &Object::Int(-1234));
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
        compile_function(&mut buffer, &Object::Char(b'x'));
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
        compile_function(&mut buffer, &unary_call("add1", Object::Int(41)));
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
        compile_function(
            &mut buffer,
            &unary_call("add1", unary_call("add1", Object::Int(1232))),
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
    fn test_compile_sub1() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        compile_function(&mut buffer, &unary_call("sub1", Object::Int(1235)));
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
        compile_function(&mut buffer, &unary_call("int?", Object::Int(10)));
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
        compile_function(&mut buffer, &unary_call("int?", Object::Bool(true)));
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
        compile_function(&mut buffer, &unary_call("nil?", Object::Nil));
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
        compile_function(&mut buffer, &unary_call("nil?", Object::Int(1)));
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
        compile_function(
            &mut buffer,
            &binary_call("+", Object::Int(1), Object::Int(2)),
        );
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
        compile_function(
            &mut buffer,
            &binary_call(
                "+",
                binary_call("+", Object::Int(1), Object::Int(2)),
                binary_call("+", Object::Int(3), Object::Int(4)),
            ),
        );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Object::Int(10)
            );
        }
        Ok(())
    }
}

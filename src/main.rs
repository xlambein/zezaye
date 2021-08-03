#![feature(box_syntax, box_patterns)]

use color_eyre::Result;
use std::{ffi::c_void, ptr};

use nix::{
    libc::memcpy,
    sys::mman::{mmap, mprotect, munmap, MapFlags, ProtFlags},
};

mod object;

use object::Object;

#[repr(u8)]
enum Register {
    Rax = 0,
    Rcx,
    Rdx,
    Rbx,
    Rsp,
    Rbp,
    Rsi,
    Rdi,
}

#[repr(u8)]
enum ByteRegister {
    Al = 0,
    Cl,
    Dl,
    Bl,
    Ah,
    Ch,
    Dh,
    Bh,
}

#[repr(u8)]
enum Setcc {
    Equal = 0x04,
}

struct Indirect(Register, i8);

const REX_PREFIX: u8 = 0x48;

const WORD_SIZE: i64 = 8;

fn emit_mov_reg_imm32(buffer: &mut Vec<u8>, dst: Register, src: i32) {
    buffer.push(REX_PREFIX);
    buffer.push(0xc7);
    buffer.push(0xc0 + dst as u8);
    buffer.extend(src.to_le_bytes());
}

fn emit_mov_reg_imm64(buffer: &mut Vec<u8>, dst: Register, src: u64) {
    buffer.push(REX_PREFIX);
    buffer.push(0xb8 + dst as u8);
    buffer.extend(src.to_le_bytes());
}

fn emit_add_reg_imm32(buffer: &mut Vec<u8>, dst: Register, src: i32) {
    // TODO check for overflow
    buffer.push(REX_PREFIX);
    buffer.push(0x81);
    buffer.push(0xc0 + dst as u8);
    buffer.extend(src.to_le_bytes());
}

fn emit_sub_reg_imm32(buffer: &mut Vec<u8>, dst: Register, src: i32) {
    // TODO check for overflow
    buffer.push(REX_PREFIX);
    buffer.push(0x81);
    buffer.push(0xe8 + dst as u8);
    buffer.extend(src.to_le_bytes());
}

fn emit_shr_reg_imm8(buffer: &mut Vec<u8>, dst: Register, src: u8) {
    buffer.push(REX_PREFIX);
    buffer.push(0xc1);
    buffer.push(0xe8 + dst as u8);
    buffer.push(src);
}

fn emit_cmp_reg_imm32(buffer: &mut Vec<u8>, dst: Register, src: u32) {
    if let Register::Rax = dst {
        // Eax optimization
        buffer.push(0x3d);
    } else {
        buffer.push(0x81);
        buffer.push(0xf8 + dst as u8);
    }
    buffer.extend(src.to_le_bytes());
}

fn emit_setcc_imm8(buffer: &mut Vec<u8>, cond: Setcc, dst: ByteRegister) {
    // https://www.felixcloutier.com/x86/setcc
    buffer.push(0x0f);
    buffer.push(0x90 + cond as u8);
    buffer.push(0xc0 + dst as u8);
}

fn emit_store_reg_indirect(buffer: &mut Vec<u8>, dst: Indirect, src: Register) {
    buffer.push(REX_PREFIX);
    buffer.push(0x89);
    buffer.push(0x40 + (src as u8) * 8 + dst.0 as u8);
    buffer.push(dst.1 as u8);
}

fn emit_add_reg_indirect(buffer: &mut Vec<u8>, dst: Register, src: Indirect) {
    // TODO check for overflow
    buffer.push(REX_PREFIX);
    buffer.push(0x03);
    buffer.push(0x40 + (dst as u8) * 8 + src.0 as u8);
    buffer.push(src.1 as u8);
}

fn emit_store_reg_reg_32(buffer: &mut Vec<u8>, dst: Register, src: Register) {
    buffer.push(0x89);
    buffer.push(0xc0 + (src as u8) * 8 + dst as u8);
}

fn emit_ret(buffer: &mut Vec<u8>) {
    buffer.push(0xc3);
}

fn compile_compare_imm_header(buffer: &mut Vec<u8>, target: Object) {
    emit_shr_reg_imm8(buffer, Register::Rax, 32);
    emit_cmp_reg_imm32(buffer, Register::Rax, (target.to_word() >> 32) as u32);
    emit_mov_reg_imm64(buffer, Register::Rax, Object::Bool(false).to_word());
    emit_setcc_imm8(buffer, Setcc::Equal, ByteRegister::Al);
}

fn compile_args(buffer: &mut Vec<u8>, args: &Object, stack_index: i64) -> i64 {
    if let Object::Pair(box car, box cdr) = args {
        match cdr {
            Object::Nil => {
                compile_expr(buffer, car, stack_index);
                stack_index
            }
            Object::Pair(_, _) => {
                let stack_index = compile_args(buffer, cdr, stack_index);
                emit_store_reg_indirect(
                    buffer,
                    Indirect(Register::Rbp, stack_index as i8),
                    Register::Rax,
                );
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

fn compile_call(buffer: &mut Vec<u8>, name: &str, args: &Object, stack_index: i64) {
    // TODO check arity before making call
    compile_args(buffer, args, stack_index);
    match name {
        "add1" => {
            emit_add_reg_imm32(buffer, Register::Rax, 1);
        }
        "sub1" => {
            emit_sub_reg_imm32(buffer, Register::Rax, 1);
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
            emit_store_reg_reg_32(buffer, Register::Rax, Register::Rax);
            // Add RAX to the second arg
            emit_add_reg_indirect(
                buffer,
                Register::Rax,
                Indirect(Register::Rbp, stack_index as i8),
            );
        }
        _ => {
            panic!("undefined function '{}'", name);
        }
    }
}

fn compile_expr(buffer: &mut Vec<u8>, obj: &Object, stack_index: i64) {
    match obj {
        Object::Pair(box car, box cdr) => {
            if let Object::Symbol(s) = car {
                compile_call(buffer, s, cdr, stack_index);
            } else {
                panic!("expected symbol in function call name");
            }
        }
        _ => {
            emit_mov_reg_imm64(buffer, Register::Rax, obj.to_word());
        }
    }
}

fn compile_prologue(buffer: &mut Vec<u8>) {
    // push rbp
    buffer.push(0x55);
    // mov rbp, rsp
    buffer.extend([0x48, 0x89, 0xE5]);
}

fn compile_epilogue(buffer: &mut Vec<u8>) {
    // mov rsp, rbp
    buffer.extend([0x48, 0x89, 0xEC]);
    // pop rbp
    buffer.push(0x5D);
}

fn compile_function(buffer: &mut Vec<u8>, obj: &Object) {
    compile_prologue(buffer);
    compile_expr(buffer, obj, -8);
    compile_epilogue(buffer);
    emit_ret(buffer);
}

unsafe fn run_x86_64<T>(program: &[u8]) -> Result<T> {
    let mem = mmap(
        ptr::null_mut(),
        program.len(),
        ProtFlags::PROT_READ | ProtFlags::PROT_WRITE,
        MapFlags::MAP_ANONYMOUS | MapFlags::MAP_PRIVATE,
        -1,
        0,
    )?;
    memcpy(mem, program.as_ptr() as *const c_void, program.len());
    mprotect(mem, program.len(), ProtFlags::PROT_EXEC)?;

    let fun: unsafe extern "C" fn() -> T = std::mem::transmute(mem);
    let result = (fun)();

    munmap(mem, program.len())?;

    Ok(result)
}

fn main() -> Result<()> {
    color_eyre::install()?;

    let mut buffer = vec![];
    compile_function(&mut buffer, &Object::Int(1234));

    unsafe {
        dbg!(run_x86_64::<u64>(&buffer)?);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_emit_store_reg_indirect() {
        let mut buffer = vec![];
        emit_store_reg_indirect(&mut buffer, Indirect(Register::Rbp, -8), Register::Rax);
        assert_eq!(buffer.as_slice(), &[0x48, 0x89, 0x45, 0xF8]);

        let mut buffer = vec![];
        emit_store_reg_indirect(&mut buffer, Indirect(Register::Rax, 16), Register::Rbx);
        assert_eq!(buffer.as_slice(), &[0x48, 0x89, 0x58, 0x10]);
    }

    #[test]
    fn test_compile_positive_integer() -> Result<()> {
        let mut buffer = vec![];
        compile_function(&mut buffer, &Object::Int(1234));
        assert_eq!(
            buffer.as_slice(),
            // rex movabs rax $imm; ret
            &[0x48, 0xb8, 210, 4, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff, 0xc3]
        );
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_negative_integer() -> Result<()> {
        let mut buffer = vec![];
        compile_function(&mut buffer, &Object::Int(-1234));
        assert_eq!(
            buffer.as_slice(),
            // rex mov rax $imm; ret
            &[0x48, 0xb8, 0x2e, 0xfb, 0xff, 0xff, 0x01, 0x00, 0xf0, 0xff, 0xc3]
        );
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Int(-1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_char() -> Result<()> {
        let mut buffer = vec![];
        compile_function(&mut buffer, &Object::Char(b'x'));
        assert_eq!(
            buffer.as_slice(),
            // rex mov rax $imm; ret
            &[0x48, 0xb8, b'x', 0x00, 0x00, 0x00, 0x02, 0x00, 0xf0, 0xff, 0xc3]
        );
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
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
        let mut buffer = vec![];
        compile_function(&mut buffer, &unary_call("add1", Object::Int(41)));
        assert_eq!(
            buffer.as_slice(),
            &[
                // rex mov rax $imm
                0x48, 0xb8, 41, 0x00, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff,
                // rex add rax $1; ret
                0x48, 0x81, 0xc0, 1, 0x00, 0x00, 0x00, 0xc3
            ]
        );
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Int(42)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_add1_nested() -> Result<()> {
        let mut buffer = vec![];
        compile_function(
            &mut buffer,
            &unary_call("add1", unary_call("add1", Object::Int(1232))),
        );
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_sub1() -> Result<()> {
        let mut buffer = vec![];
        compile_function(&mut buffer, &unary_call("sub1", Object::Int(1235)));
        assert_eq!(
            buffer.as_slice(),
            &[
                // rex mov rax $imm
                0x48, 0xb8, 0xd3, 0x04, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff,
                // rex sub rax $1; ret
                0x48, 0x81, 0xe8, 1, 0x00, 0x00, 0x00, 0xc3
            ]
        );
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_int_true() -> Result<()> {
        let mut buffer = vec![];
        compile_function(&mut buffer, &unary_call("int?", Object::Int(10)));
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Bool(true)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_int_false() -> Result<()> {
        let mut buffer = vec![];
        compile_function(&mut buffer, &unary_call("int?", Object::Bool(true)));
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Bool(false)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_nil_true() -> Result<()> {
        let mut buffer = vec![];
        compile_function(&mut buffer, &unary_call("nil?", Object::Nil));
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Bool(true)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_nil_false() -> Result<()> {
        let mut buffer = vec![];
        compile_function(&mut buffer, &unary_call("nil?", Object::Int(1)));
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Bool(false)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_args() -> Result<()> {
        let mut buffer = vec![];
        compile_function(
            &mut buffer,
            &binary_call("+", Object::Int(1), Object::Int(2)),
        );
        println!(
            "{:?}",
            buffer
                .iter()
                .map(|x| format!("{:02x} ", x))
                .collect::<Vec<_>>()
                .concat()
        );
        Ok(())
    }

    #[test]
    fn test_compile_plus() -> Result<()> {
        let mut buffer = vec![];
        compile_function(
            &mut buffer,
            &binary_call("+", Object::Int(1), Object::Int(2)),
        );
        unsafe {
            assert_eq!(
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Int(3)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_plus_nested() -> Result<()> {
        let mut buffer = vec![];
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
                Object::parse_word(run_x86_64::<u64>(&buffer)?)?,
                Object::Int(10)
            );
        }
        Ok(())
    }
}

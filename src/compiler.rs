use Object::{Bool, Char, Int, Nil, Pair, Symbol};
use Register::*;

use crate::object::{Object, PAYLOAD_MASK};
use crate::program_buffer::{Cond, Immediate32, Ind, ProgramBuffer, Register};

mod env {
    use std::rc::Rc;

    enum EnvItem {
        Binding {
            ident: String,
            location: i32,
            prev: Rc<EnvItem>,
        },
        Nothing,
    }

    impl EnvItem {
        fn find(&self, name: &str) -> Option<i32> {
            match self {
                EnvItem::Binding {
                    ident, location, ..
                } if ident == name => Some(*location),
                EnvItem::Binding { prev, .. } => prev.find(name),
                EnvItem::Nothing => None,
            }
        }
    }

    #[derive(Clone)]
    pub struct Env(Rc<EnvItem>);

    impl Env {
        pub fn new() -> Self {
            Env(Rc::new(EnvItem::Nothing))
        }

        pub fn bind(&self, ident: impl Into<String>, location: i32) -> Self {
            Env(Rc::new(EnvItem::Binding {
                ident: ident.into(),
                location,
                prev: self.0.clone(),
            }))
        }

        pub fn find(&self, name: &str) -> Option<i32> {
            self.0.find(name)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_env() {
            // Unbound identifier
            let env = Env::new();
            assert_eq!(env.find("foo"), None);

            // Bound identifier
            let env2 = env.bind("foo", -8);
            assert_eq!(env2.find("foo"), Some(-8));
            // Original doesn't change
            assert_eq!(env.find("foo"), None);

            // Two bound identifiers
            let env3 = env2.bind("bar", -16);
            assert_eq!(env3.find("foo"), Some(-8));
            assert_eq!(env3.find("bar"), Some(-16));
            // Original doesn't change
            assert_eq!(env2.find("foo"), Some(-8));
            assert_eq!(env2.find("bar"), None);

            // Rebinding an identifier
            let env4 = env2.bind("foo", -16);
            assert_eq!(env4.find("foo"), Some(-16));
            // Original doesn't change
            assert_eq!(env2.find("foo"), Some(-8));
        }
    }
}

use env::Env;

#[repr(u32)]
#[non_exhaustive]
enum Syscall {
    Read = 0,
    Write = 1,
}

impl Immediate32 for Syscall {
    fn to_le_bytes(self) -> [u8; 4] {
        (self as u32).to_le_bytes()
    }
}

const WORD_SIZE: usize = 8;

pub struct Compiler<'buffer> {
    buffer: &'buffer mut ProgramBuffer,
}

impl<'buffer> Compiler<'buffer> {
    pub fn new(buffer: &'buffer mut ProgramBuffer) -> Self {
        Self { buffer }
    }

    fn compare_imm_header(&mut self, target: Object) {
        self.buffer
            // Compare the header
            .shr_q_imm(AX, 32i8)
            .cmp_d_imm(AX, (target.to_word() >> 32) as u32)
            // Set Bool header
            .mov_q_imm64(AX, Bool(false).to_word())
            // Set the lower bit of AX if the CMP produced equality
            .setcc(Cond::Equal, AX);
    }

    fn args(&mut self, args: &Object, stack_index: i32, env: &Env) -> i32 {
        if let Pair(box car, box cdr) = args {
            match cdr {
                Nil => {
                    self.expr(car, stack_index, env);
                    stack_index
                }
                Pair(_, _) => {
                    let stack_index = self.args(cdr, stack_index, env);
                    self.buffer.mov_q(Ind(BP, stack_index), AX);
                    // TODO handle stack index bigger than a byte
                    let stack_index = stack_index - WORD_SIZE as i32;
                    self.expr(car, stack_index, env);
                    stack_index
                }
                _ => panic!("expected pair or nil"),
            }
        } else {
            panic!("expected pair");
        }
    }

    fn let_bindings(
        &mut self,
        bindings: &Object,
        stack_index: i32,
        env: &Env,
        new_env: Env,
    ) -> (Env, i32) {
        if let Pair(box Pair(box Symbol(ident), box Pair(box expr, box Nil)), bindings) = bindings {
            // Compile expr and store result on stack
            self.expr(expr, stack_index, env);
            self.buffer.mov_q(Ind(BP, stack_index), AX);

            // Store new binding
            let new_env = new_env.bind(ident, stack_index);

            // Compile rest
            self.let_bindings(bindings, stack_index - WORD_SIZE as i32, env, new_env)
        } else if let Nil = bindings {
            (new_env, stack_index)
        } else {
            panic!("malformed 'let' bindings");
        }
    }

    fn cond(&mut self, args: &Object, stack_index: i32, env: &Env) {
        if let Pair(box Pair(box cond, box Pair(box expr, box Nil)), box rest) = args {
            if let Object::Bool(true) = cond {
                // Small optimization: if one arm has a 'true' literal as a condition,
                // we can safely skip the remaining
                self.expr(expr, stack_index, env);
            } else {
                // TODO this whole nested compilation to avoid labels is complicated.
                //  Using "smart" labels that patch the buffer a-posteriori, we might
                //  make the code a bit simpler (and compilation faster).
                //  However, we would lose the ability to use short (byte) jumps.

                // Generate remaining arms of the cond
                let mut rest_buf = ProgramBuffer::new();
                Compiler::new(&mut rest_buf).cond(rest, stack_index, env);

                // Generate body of the current arm
                let mut body_buf = ProgramBuffer::new();
                Compiler::new(&mut body_buf).expr(expr, stack_index, env);

                // Add a jump over the other arms at the end of the body
                body_buf.jmp_rel(rest_buf.as_slice().len() as i32);

                // Compile the condition
                self.expr(cond, stack_index, env);

                // Jump over the body if the condition is false
                self.buffer
                    .mov_q_imm64(DI, Object::Bool(false).to_word())
                    .cmp_q(AX, DI)
                    .jcc(Cond::Equal, body_buf.as_slice().len() as i32);

                // Append body
                self.buffer.concatenate(&body_buf);

                // Append the other arms
                self.buffer.concatenate(&rest_buf);
            }
        } else if let Nil = args {
            // Produce Nil as a default result for the cond
            // Not the best idea?  Might be better to enforce an `else`
            self.buffer.mov_q_imm64(AX, Object::Nil.to_word());
        } else {
            panic!("malformed 'cond' expression");
        }
    }

    fn call(&mut self, name: &str, args: &Object, stack_index: i32, env: &Env) {
        if name == "let" {
            // (let ((ident expr)...) expr)
            if let Pair(box bindings, box Pair(box expr, box Nil)) = args {
                let (env, stack_index) = self.let_bindings(bindings, stack_index, env, env.clone());
                self.expr(expr, stack_index, &env);
            } else {
                panic!("malformed 'let'");
            }
            return;
        } else if name == "cond" {
            // (cond (expr expr)...)
            self.cond(args, stack_index, env);
            return;
        } else if name == "println" {
            // TODO this should be a macro in the future
            self.call("print", args, stack_index, env);
            self.call(
                "putchar",
                &Pair(box Object::Char(b'\n'), box Nil),
                stack_index,
                env,
            );
            return;
        }

        // TODO check arity before making call
        self.args(args, stack_index, env);
        match name {
            "add1" => {
                self.buffer.add_q_imm(AX, 1);
            }
            "sub1" => {
                self.buffer.sub_q_imm(AX, 1);
            }
            "int?" => {
                self.compare_imm_header(Int(0));
            }
            "char?" => {
                self.compare_imm_header(Char(0));
            }
            "bool?" => {
                self.compare_imm_header(Bool(false));
            }
            "nil?" => {
                self.compare_imm_header(Nil);
            }
            "+" => {
                // TODO type checking
                self.buffer
                    // Erase the upper bits of RAX
                    .mov_d(AX, AX)
                    // Add RAX to the second arg
                    .add_q(AX, Ind(BP, stack_index));
            }
            "cons" => {
                // TODO this could be optimized if we didn't pre-process the arguments
                self.buffer
                    // car
                    .mov_q(Ind(SI, 0), AX)
                    // cdr
                    .mov_q(AX, Ind(BP, stack_index))
                    .mov_q(Ind(SI, WORD_SIZE as i32), AX)
                    // Return cons cell
                    // TODO this is not a smart way to get the Pair header :D
                    .mov_q_imm64(AX, Object::Pair(box Nil, box Nil).to_word())
                    .add_q(AX, SI)
                    // Bump RSI
                    .add_q_imm(SI, 2 * WORD_SIZE as i32);
            }
            "car" => {
                // TODO type check
                self.buffer
                    // Mask away the header
                    .mov_q_imm64(DI, PAYLOAD_MASK)
                    .and_q(AX, DI)
                    // Return the address in RAX
                    .mov_q(AX, Ind(AX, 0));
            }
            "cdr" => {
                // TODO type check
                self.buffer
                    // Mask away the header
                    .mov_q_imm64(DI, PAYLOAD_MASK)
                    .and_q(AX, DI)
                    // Return the address in RAX+8
                    .mov_q(AX, Ind(AX, WORD_SIZE as i32));
            }
            "putchar" => {
                self.buffer
                    // Save RSI
                    .mov_q(Ind(BP, stack_index), SI)
                    // Store word to write on stack
                    .mov_q(Ind(BP, stack_index - WORD_SIZE as i32), AX)
                    // Syscall number: write
                    .mov_q_imm(AX, Syscall::Write)
                    // Return address: we don't care
                    .mov_q_imm(CX, 0)
                    // Arg 0: stdout
                    .mov_q_imm(DI, 1)
                    // Arg 1: address of the word on the stack
                    .mov_q(SI, BP)
                    .add_q_imm(SI, stack_index - WORD_SIZE as i32)
                    // Arg 2: length of the data (a single byte)
                    .mov_q_imm(DX, 1)
                    .syscall()
                    // Restore RSI
                    .mov_q(SI, Ind(BP, stack_index))
                    // Return nil
                    .mov_q_imm64(AX, Object::Nil.to_word());
            }
            "string-length" => {
                self.buffer
                    // Mask away the header
                    .mov_q_imm64(DI, PAYLOAD_MASK)
                    .and_q(AX, DI)
                    // Fetch the contents of [RAX]
                    .mov_q(AX, Ind(AX, 0))
                    // Add the Int header
                    .mov_q_imm64(DI, Object::Int(0).to_word())
                    .or_q(AX, DI);
            }
            "string-ref" => {
                self.buffer
                    // Retrieve the offset (second arg) without the int header
                    .mov_d(DI, Ind(BP, stack_index))
                    // Add the byte offset (second arg) to the address
                    // TODO this could be done instead with [Rax+Rdi+8] addressing
                    .add_q(AX, DI)
                    // Mask away the header
                    .mov_q_imm64(DI, PAYLOAD_MASK)
                    .and_q(AX, DI)
                    // Fetch the contents of [RAX+8] into the low byte of RAX
                    .movzx_q(AX, Ind(AX, WORD_SIZE as i32))
                    // Add the Char header
                    .mov_q_imm64(DI, Object::Char(0).to_word())
                    .or_q(AX, DI);
            }
            "print" => {
                self.buffer
                    // Save RSI
                    .mov_q(Ind(BP, stack_index), SI)
                    // Mask away the header
                    .mov_q_imm64(DI, PAYLOAD_MASK)
                    .and_q(AX, DI)
                    // Arg 0: stdout
                    .mov_d_imm(DI, 1)
                    // Arg 1: address of the word on the stack
                    .mov_q(SI, AX)
                    .add_q_imm(SI, WORD_SIZE as i32)
                    // Arg 2: length of the data
                    .mov_d(DX, Ind(AX, 0))
                    // Syscall number: write
                    .mov_d_imm(AX, Syscall::Write)
                    // Return address: we don't care
                    .mov_d_imm(CX, 0)
                    .syscall()
                    // Restore RSI
                    .mov_q(SI, Ind(BP, stack_index))
                    // Return nil
                    .mov_q_imm64(AX, Object::Nil.to_word());
            }
            _ => {
                panic!("undefined function '{}'", name);
            }
        }
    }

    fn expr(&mut self, obj: &Object, stack_index: i32, env: &Env) {
        match obj {
            Pair(box car, box cdr) => {
                if let Symbol(s) = car {
                    self.call(s, cdr, stack_index, env);
                } else {
                    panic!("expected symbol in function call name");
                }
            }
            Symbol(s) => {
                if let Some(loc) = env.find(s) {
                    // Load local into RAX
                    self.buffer.mov_q(AX, Ind(BP, loc));
                } else {
                    panic!("unbound symbol '{}'", s);
                }
            }
            Object::String(s) => {
                // length
                self.buffer.mov_d_imm(Ind(SI, 0), s.len() as u32);
                // characters
                // TODO do this per-double word
                for (i, b) in s.as_bytes().iter().enumerate() {
                    self.buffer.mov_bl_imm(Ind(SI, (WORD_SIZE + i) as i32), *b);
                }
                // Return string
                // TODO this is not a smart way to get the String header
                self.buffer
                    .mov_q_imm64(AX, Object::String("".to_owned()).to_word())
                    .add_q(AX, SI);

                // Bump RSI (word-aligned)
                self.buffer
                    .add_q_imm(SI, ((1 + s.len() / WORD_SIZE) * WORD_SIZE) as i32);
            }
            _ => {
                self.buffer.mov_q_imm64(AX, obj.to_word());
            }
        }
    }

    pub fn function(&mut self, obj: &Object) {
        self.buffer.prologue();
        self.buffer.mov_q(SI, DI);
        self.expr(obj, -8, &Env::new());
        self.buffer.epilogue();
    }
}

#[cfg(test)]
mod tests {
    use std::{convert::TryInto, io::Read};

    use color_eyre::Result;
    use gag::BufferRedirect;

    use super::*;
    use crate::object::Object::{Bool, Char, Int, Nil, Symbol};
    use crate::reader::Reader;

    fn compile_expr(source: &str) -> ProgramBuffer {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&Reader::from_str(source).read_expr().unwrap());
        buffer
    }

    #[test]
    fn test_compile_positive_integer() -> Result<()> {
        let buffer = compile_expr("1234");
        assert_eq!(
            // Skip prelude and epilogue
            &buffer.as_slice()[7..17],
            // rex movabs rax $imm
            &[0x48, 0xb8, 210, 4, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff]
        );
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(1234)
        );
        Ok(())
    }

    #[test]
    fn test_compile_negative_integer() -> Result<()> {
        let buffer = compile_expr("-1234");
        assert_eq!(
            // Skip prelude and epilogue
            &buffer.as_slice()[7..17],
            // rex mov rax $imm
            &[0x48, 0xb8, 0x2e, 0xfb, 0xff, 0xff, 0x01, 0x00, 0xf0, 0xff]
        );
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(-1234)
        );
        Ok(())
    }

    #[test]
    fn test_compile_char() -> Result<()> {
        let buffer = compile_expr(r"#\x");
        assert_eq!(
            &buffer.as_slice()[7..17],
            // rex mov rax $imm
            &[0x48, 0xb8, b'x', 0x00, 0x00, 0x00, 0x02, 0x00, 0xf0, 0xff]
        );
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Char(b'x')
        );
        Ok(())
    }

    #[test]
    fn test_compile_nil() -> Result<()> {
        let buffer = compile_expr("()");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Nil
        );
        Ok(())
    }

    #[test]
    fn test_compile_identifier() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).expr(&Symbol("x".to_owned()), -16, &Env::new().bind("x", -8));
        assert_eq!(
            buffer.as_slice(),
            // rex movabs rax $imm
            &[0x48, 0x8b, 0x45, 0xf8]
        );
        Ok(())
    }

    #[test]
    fn test_compile_add1() -> Result<()> {
        let buffer = compile_expr("(add1 41)");
        #[rustfmt::skip]
        assert_eq!(
            buffer.as_slice(),
            &[
                // Prologue
                0x55, 0x48, 0x89, 0xE5,
                // Setup heap pointer
                0x48, 0x89, 0xFE,
                // rex mov rax $imm
                0x48, 0xb8, 41, 0x00, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff,
                // rex add rax $1
                0x48, 0x81, 0xc0, 1, 0x00, 0x00, 0x00,
                // Epilogue
                0x48, 0x89, 0xEC, 0x5D, 0xc3,
            ]
        );
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(42)
        );
        Ok(())
    }

    #[test]
    fn test_compile_add1_nested() -> Result<()> {
        let buffer = compile_expr("(add1 (add1 1232))");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(1234)
        );
        Ok(())
    }

    #[test]
    fn test_compile_sub1() -> Result<()> {
        let buffer = compile_expr("(sub1 1235)");
        #[rustfmt::skip]
        assert_eq!(
            buffer.as_slice(),
            &[
                // Prologue
                0x55, 0x48, 0x89, 0xE5,
                // Setup heap pointer
                0x48, 0x89, 0xFE,
                // rex mov rax $imm
                0x48, 0xb8, 0xd3, 0x04, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff,
                // rex sub rax $1; ret
                0x48, 0x81, 0xe8, 1, 0x00, 0x00, 0x00,
                // Epilogue
                0x48, 0x89, 0xEC, 0x5D, 0xc3,
            ]
        );
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(1234)
        );
        Ok(())
    }

    #[test]
    fn test_compile_is_int_true() -> Result<()> {
        let buffer = compile_expr("(int? 10)");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Bool(true)
        );
        Ok(())
    }

    #[test]
    fn test_compile_is_int_false() -> Result<()> {
        let buffer = compile_expr("(int? #t)");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Bool(false)
        );
        Ok(())
    }

    #[test]
    fn test_compile_is_nil_true() -> Result<()> {
        let buffer = compile_expr("(nil? ())");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Bool(true)
        );
        Ok(())
    }

    #[test]
    fn test_compile_is_nil_false() -> Result<()> {
        let buffer = compile_expr("(nil? 1)");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Bool(false)
        );
        Ok(())
    }

    #[test]
    fn test_compile_plus() -> Result<()> {
        let buffer = compile_expr("(+ 1 2)");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(3)
        );
        Ok(())
    }

    #[test]
    fn test_compile_plus_nested() -> Result<()> {
        let buffer = compile_expr("(+ (+ 1 2) (+ 3 4))");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(10)
        );
        Ok(())
    }

    #[test]
    fn test_compile_let() -> Result<()> {
        let buffer = compile_expr("(let ((x 10) (y 4)) (+ x y))");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(14)
        );
        Ok(())
    }

    #[test]
    #[should_panic(expected = "unbound symbol 'x'")]
    fn test_compile_let_parallel_fails() {
        // TODO replace panic with result
        compile_expr("(let ((x 10) (y x)) (+ x y))");
    }

    #[test]
    fn test_compile_nested_let() -> Result<()> {
        let buffer = compile_expr("(let ((x 1)) (let ((y 5)) (+ x y)))");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(6)
        );
        Ok(())
    }

    #[test]
    fn test_compile_nested_let_shadowing() -> Result<()> {
        let buffer = compile_expr("(let ((x 1)) (let ((x 5)) (+ x 6)))");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(11)
        );
        Ok(())
    }

    #[test]
    fn test_compile_cond_first() -> Result<()> {
        let buffer = compile_expr(r"(cond (#t 1) (#f #\a))");
        #[rustfmt::skip]
        assert_eq!(
            buffer.as_slice(),
            &[
                // Prologue
                0x55, 0x48, 0x89, 0xE5,
                // Setup heap pointer
                0x48, 0x89, 0xFE,
                // We entirely skip the conditional
                // rex mov rax $repr(1)
                0x48, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff,
                // Epilogue
                0x48, 0x89, 0xEC, 0x5D, 0xc3,
            ]
        );
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(1)
        );
        Ok(())
    }

    #[test]
    fn test_compile_cond_second() -> Result<()> {
        let buffer = compile_expr(r"(cond (#f 1) (#t #\a))");
        #[rustfmt::skip]
        assert_eq!(
            buffer.as_slice(),
            &[
                // Prologue
                0x55, 0x48, 0x89, 0xE5,
                // Setup heap pointer
                0x48, 0x89, 0xFE,

                // First arm
                // rex mov rax $repr(#f)
                0x48, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0xf0, 0xff,
                // rex mov rbi $repr(#f)
                0x48, 0xbf, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0xf0, 0xff,
                // rex cmp rax,rdi
                0x48, 0x39, 0xf8,
                // je +12 (jump over body)
                0x74, 12,
                // rex mov rax $repr(1)
                0x48, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff,
                // jmp +10 (jump over rest)
                0xeb, 10,

                // Second arm (skipped conditional)
                // rex mov rax $repr(#\a)
                0x48, 0xb8, b'a', 0x00, 0x00, 0x00, 0x02, 0x00, 0xf0, 0xff,

                // Epilogue
                0x48, 0x89, 0xEC, 0x5D, 0xc3,
            ]
        );
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Char(b'a')
        );
        Ok(())
    }

    #[test]
    fn test_compile_cond_default() -> Result<()> {
        let buffer = compile_expr(r"(cond (#f 1) (#f #\a))");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Nil
        );
        Ok(())
    }

    #[test]
    fn test_compile_cond_in_let() -> Result<()> {
        #[rustfmt::skip]
        let buffer = compile_expr(r"
            (let ((x ()))
             (cond
              ((int? x) 1)
              ((nil? x) 2)
              (#t 3)))
        ");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(2)
        );
        Ok(())
    }

    #[test]
    fn test_compile_cond_not_bool() -> Result<()> {
        let buffer = compile_expr(r"(cond ((+ 1 2) 1) (#t 2))");
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Int(1)
        );
        Ok(())
    }

    #[test]
    fn test_compile_cons() -> Result<()> {
        let buffer = compile_expr(r"(cons 123 #\x)");
        let mut heap = [0; 2 * WORD_SIZE as usize];
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Pair(box Nil, box Nil)
        );
        let objects: Vec<Object> = heap
            .chunks(WORD_SIZE as usize)
            .flat_map(|c| c.try_into())
            .map(u64::from_le_bytes)
            .flat_map(Object::parse_word)
            .collect();
        assert_eq!(objects[0], Int(123));
        assert_eq!(objects[1], Char(b'x'));
        Ok(())
    }

    #[test]
    fn test_compile_nested_cons() -> Result<()> {
        let buffer = compile_expr(r"(cons 123 (cons 456 ()))");
        let mut heap = [0; 4 * WORD_SIZE as usize];
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Pair(box Nil, box Nil)
        );
        let objects: Vec<Object> = heap
            .chunks(WORD_SIZE as usize)
            .flat_map(|c| c.try_into())
            .map(u64::from_le_bytes)
            .flat_map(Object::parse_word)
            .collect();
        assert_eq!(objects[0], Int(456));
        assert_eq!(objects[1], Nil);
        assert_eq!(objects[2], Int(123));
        assert_eq!(objects[3], Pair(box Nil, box Nil));
        Ok(())
    }

    #[test]
    fn test_compile_car() -> Result<()> {
        let buffer = compile_expr(r"(car (cons 123 #\x))");
        let mut heap = [0; 2 * WORD_SIZE as usize];
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Int(123)
        );
        Ok(())
    }

    #[test]
    fn test_compile_cdr() -> Result<()> {
        let buffer = compile_expr(r"(cdr (cons 123 #\x))");
        let mut heap = [0; 2 * WORD_SIZE as usize];
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Char(b'x')
        );
        Ok(())
    }

    #[test]
    fn test_compile_car_cdr() -> Result<()> {
        let buffer = compile_expr(r"(car (cdr (cons 123 (cons 456 ()))))");
        let mut heap = [0; 4 * WORD_SIZE as usize];
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Int(456)
        );
        Ok(())
    }

    #[test]
    #[ignore = "cargo test capture prevents testing stdout properly"]
    fn test_compile_putchar() -> Result<()> {
        let buffer = compile_expr(r"(putchar #\x)");
        let mut redirect = BufferRedirect::stdout().unwrap();
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut []) })?,
            Nil
        );
        let mut output = String::new();
        redirect.read_to_string(&mut output).unwrap();
        assert_eq!(output, "x");
        Ok(())
    }

    #[test]
    fn test_compile_string() -> Result<()> {
        const STR: &str = "hi beautiful ✨";
        let buffer = compile_expr(&format!(r#""{}""#, STR));
        let mut heap = [0; 10 * WORD_SIZE as usize];
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Object::String("".to_owned())
        );
        assert_eq!(
            usize::from_le_bytes(heap[..WORD_SIZE as usize].try_into().unwrap()),
            STR.len()
        );
        assert_eq!(
            &heap[WORD_SIZE as usize..WORD_SIZE as usize + STR.len()],
            STR.as_bytes()
        );
        Ok(())
    }

    #[test]
    fn test_compile_string_length() -> Result<()> {
        const STR: &str = "hi beautiful ✨";
        let buffer = compile_expr(&format!(r#"(string-length "{}")"#, STR));
        let mut heap = [0; 10 * WORD_SIZE as usize];
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Object::Int(STR.len() as i32)
        );
        Ok(())
    }

    #[test]
    fn test_compile_string_ref() -> Result<()> {
        const STR: &str = "hi beautiful ✨";
        let buffer = compile_expr(&format!(r#"(string-ref "{}" 4)"#, STR));
        let mut heap = [0; 10 * WORD_SIZE as usize];
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Object::Char(b'e')
        );
        Ok(())
    }

    #[test]
    #[ignore = "cargo test capture prevents testing stdout properly"]
    fn test_compile_print() -> Result<()> {
        const STR: &str = "hi beautiful ✨";
        let buffer = compile_expr(&format!(r#"(print "{}")"#, STR));
        let mut heap = [0; 10 * WORD_SIZE as usize];
        let mut redirect = BufferRedirect::stdout().unwrap();
        assert_eq!(
            Object::parse_word(unsafe { buffer.make_executable().execute(&mut heap) })?,
            Nil
        );
        let mut output = String::new();
        redirect.read_to_string(&mut output).unwrap();
        assert_eq!(output, STR);
        Ok(())
    }
}

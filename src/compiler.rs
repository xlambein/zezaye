use Object::{Bool, Char, Int, Nil, Pair, Symbol};

use crate::object::Object;
use crate::program_buffer::{ByteRegister, Indirect, ProgramBuffer, Register, Setcc};

mod env {
    use std::rc::Rc;

    enum EnvItem {
        Binding {
            ident: String,
            location: i64,
            prev: Rc<EnvItem>,
        },
        Nothing,
    }

    impl EnvItem {
        fn find(&self, name: &str) -> Option<i64> {
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

        pub fn bind(&self, ident: impl Into<String>, location: i64) -> Self {
            Env(Rc::new(EnvItem::Binding {
                ident: ident.into(),
                location,
                prev: self.0.clone(),
            }))
        }

        pub fn find(&self, name: &str) -> Option<i64> {
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
            .mov_reg_imm64(Register::Rax, Bool(false).to_word())
            .setcc_imm8(Setcc::Equal, ByteRegister::Al);
    }

    fn args(&mut self, args: &Object, stack_index: i64, env: &Env) -> i64 {
        if let Pair(box car, box cdr) = args {
            match cdr {
                Nil => {
                    self.expr(car, stack_index, env);
                    stack_index
                }
                Pair(_, _) => {
                    let stack_index = self.args(cdr, stack_index, env);
                    self.buffer.store_reg_indirect(
                        Indirect(Register::Rbp, stack_index as i8),
                        Register::Rax,
                    );
                    // TODO handle stack index bigger than a byte
                    let stack_index = stack_index - WORD_SIZE;
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
        stack_index: i64,
        env: &Env,
        new_env: Env,
    ) -> (Env, i64) {
        if let Pair(box Pair(box Symbol(ident), box Pair(box expr, box Nil)), bindings) = bindings {
            // Eval expr and store it on stack
            self.expr(expr, stack_index, env);
            self.buffer
                .store_reg_indirect(Indirect(Register::Rbp, stack_index as i8), Register::Rax);

            // Store new binding
            let new_env = new_env.bind(ident, stack_index);

            // Process rest
            self.let_bindings(bindings, stack_index - WORD_SIZE, env, new_env)
        } else if let Nil = bindings {
            (new_env, stack_index)
        } else {
            panic!("malformed 'let' bindings");
        }
    }

    fn call(&mut self, name: &str, args: &Object, stack_index: i64, env: &Env) {
        if name == "let" {
            // (let ((ident expr)...) expr)
            if let Pair(box bindings, box Pair(box expr, box Nil)) = args {
                let (env, stack_index) = self.let_bindings(bindings, stack_index, env, env.clone());
                self.expr(expr, stack_index, &env);
            } else {
                panic!("malformed 'let'");
            }
            return;
        }

        // TODO check arity before making call
        self.args(args, stack_index, env);
        match name {
            "add1" => {
                self.buffer.add_reg_imm32(Register::Rax, 1);
            }
            "sub1" => {
                self.buffer.sub_reg_imm32(Register::Rax, 1);
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

    fn expr(&mut self, obj: &Object, stack_index: i64, env: &Env) {
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
                    self.buffer
                        .store_indirect_reg(Register::Rax, Indirect(Register::Rbp, loc as i8));
                } else {
                    panic!("unbound symbol '{}'", s);
                }
            }
            _ => {
                self.buffer.mov_reg_imm64(Register::Rax, obj.to_word());
            }
        }
    }

    pub fn function(&mut self, obj: &Object) {
        self.buffer.prologue();
        self.expr(obj, -8, &Env::new());
        self.buffer.epilogue();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use color_eyre::Result;
    use Object::{Bool, Char, Int, Nil, Pair, Symbol};

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

    #[test]
    fn test_compile_positive_integer() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&Int(1234));
        // assert_eq!(
        //     buffer.as_slice(),
        //     // rex movabs rax $imm; ret
        //     &[0x48, 0xb8, 210, 4, 0x00, 0x00, 0x01, 0x00, 0xf0, 0xff, 0xc3]
        // );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_negative_integer() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&Int(-1234));
        // assert_eq!(
        //     buffer.as_slice(),
        //     // rex mov rax $imm; ret
        //     &[0x48, 0xb8, 0x2e, 0xfb, 0xff, 0xff, 0x01, 0x00, 0xf0, 0xff, 0xc3]
        // );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Int(-1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_char() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&Char(b'x'));
        // assert_eq!(
        //     buffer.as_slice(),
        //     // rex mov rax $imm; ret
        //     &[0x48, 0xb8, b'x', 0x00, 0x00, 0x00, 0x02, 0x00, 0xf0, 0xff, 0xc3]
        // );
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Char(b'x')
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_identifier() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).expr(&Symbol("x".to_owned()), -16, &Env::new().bind("x", -8));
        assert_eq!(
            buffer.as_slice(),
            // rex movabs rax $imm; ret
            &[0x48, 0x8b, 0x45, 0xf8]
        );
        Ok(())
    }

    fn unary_call(name: impl Into<String>, arg: Object) -> Object {
        Pair(box Symbol(name.into()), box Pair(box arg, box Nil))
    }

    fn binary_call(name: impl Into<String>, arg0: Object, arg1: Object) -> Object {
        Pair(
            box Symbol(name.into()),
            box Pair(box arg0, box Pair(box arg1, box Nil)),
        )
    }

    #[test]
    fn test_compile_add1() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("add1", Int(41)));
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
                Int(42)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_add1_nested() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("add1", unary_call("add1", Int(1232))));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_sub1() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("sub1", Int(1235)));
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
                Int(1234)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_int_true() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("int?", Int(10)));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Bool(true)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_int_false() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("int?", Bool(true)));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Bool(false)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_nil_true() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("nil?", Nil));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Bool(true)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_is_nil_false() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&unary_call("nil?", Int(1)));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Bool(false)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_plus() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&binary_call("+", Int(1), Int(2)));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Int(3)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_plus_nested() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&binary_call(
            "+",
            binary_call("+", Int(1), Int(2)),
            binary_call("+", Int(3), Int(4)),
        ));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Int(10)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_let() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&binary_call(
            "let",
            Pair(
                box Pair(box Symbol("x".to_owned()), box Pair(box Int(10), box Nil)),
                box Pair(
                    box Pair(box Symbol("y".to_owned()), box Pair(box Int(4), box Nil)),
                    box Nil,
                ),
            ),
            binary_call("+", Symbol("x".to_owned()), Symbol("y".to_owned())),
        ));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Int(14)
            );
        }
        Ok(())
    }

    #[test]
    #[should_panic(expected = "unbound symbol 'x'")]
    fn test_compile_let_parallel_fails() {
        // TODO replace panic with result
        let mut buffer = ProgramBuffer::new();
        Compiler::new(&mut buffer).function(&binary_call(
            "let",
            Pair(
                box Pair(box Symbol("x".to_owned()), box Pair(box Int(10), box Nil)),
                box Pair(
                    box Pair(
                        box Symbol("y".to_owned()),
                        box Pair(box Symbol("x".to_owned()), box Nil),
                    ),
                    box Nil,
                ),
            ),
            binary_call("+", Symbol("x".to_owned()), Symbol("y".to_owned())),
        ));
    }

    #[test]
    fn test_compile_nested_let() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        let inner = binary_call(
            "let",
            Pair(
                box Pair(box Symbol("y".to_owned()), box Pair(box Int(5), box Nil)),
                box Nil,
            ),
            binary_call("+", Symbol("x".to_owned()), Symbol("y".to_owned())),
        );
        Compiler::new(&mut buffer).function(&binary_call(
            "let",
            Pair(
                box Pair(box Symbol("x".to_owned()), box Pair(box Int(1), box Nil)),
                box Nil,
            ),
            inner,
        ));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Int(6)
            );
        }
        Ok(())
    }

    #[test]
    fn test_compile_nested_let_shadowing() -> Result<()> {
        let mut buffer = ProgramBuffer::new();
        let inner = binary_call(
            "let",
            Pair(
                box Pair(box Symbol("x".to_owned()), box Pair(box Int(5), box Nil)),
                box Nil,
            ),
            binary_call("+", Symbol("x".to_owned()), Int(6)),
        );
        Compiler::new(&mut buffer).function(&binary_call(
            "let",
            Pair(
                box Pair(box Symbol("x".to_owned()), box Pair(box Int(1), box Nil)),
                box Nil,
            ),
            inner,
        ));
        unsafe {
            assert_eq!(
                Object::parse_word(buffer.make_executable().execute())?,
                Int(11)
            );
        }
        Ok(())
    }
}

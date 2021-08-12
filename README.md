# Zezaye, a Smol Lisp

Zezaye is a Smol Lisp™ that compiles to x86-64 binary code.  It is based on A. Ghuloum's ["An Incremental Approach to Compiler Construction"](http://scheme2006.cs.uchicago.edu/11-ghuloum.pdf) and Max Bernstein's [excellent tutorial](https://bernsteinbear.com/blog/compiling-a-lisp-0/) built on top of it.

My implementation is slightly different from theirs:

- the compiler is written in Rust instead of Scheme/C;
- objects are represented with NaN boxing, because I want fast floats;
- I don't plan to implement Scheme, because what's the point of writing a compiler if you don't make up a pet language to go with it?


## Running Zezaye

With Rust installed, simply clone this repo and execute `cargo run` to start a (very basic) REPL.  Exit with `CTRL+D`.

```
$ cargo run
zezaye> (let ((x (sub1 3))) (+ (+ 1 2) x))
Int(5)
zezaye> 
bye!
```

Many things aren't implemented yet and will crash the REPL.  Can you find them all?


## Implementation

The project is split into several modules:

- `src/object.rs` describes the AST, as well as each atom's encoding as a boxed NaN.
- `src/program_buffer.rs` contains `ProgramBuffer`, a byte buffer with methods for emitting x86 assembly into it.  The buffer can be converted into an `ExecutableProgramBuffer`, which can be run as a function.
- `src/compiler.rs` implements methods for compiling an AST using a `ProgramBuffer` as a backend.
- `src/reader.rs` implements a reader that parses text into an AST.


## To-Do

- [ ] Vectors & strings
- [ ] Handle non-ASCII character literals
- [ ] Refactor `panic`s into compiler errors
- [ ] 

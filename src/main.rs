#![feature(box_syntax, box_patterns, allocator_api, nonnull_slice_from_raw_parts)]

mod compiler;
mod object;
mod program_buffer;
mod reader;

use std::io;

use color_eyre::Result;
use compiler::Compiler;
use program_buffer::ProgramBuffer;
use reader::Reader;

use crate::object::Object;

const HEAP_SIZE: usize = 2048;

fn read_eval_print() -> Result<bool> {
    eprint!("zezaye> ");

    let mut input = String::new();
    if io::stdin().read_line(&mut input)? == 0 {
        eprintln!("\nbye!");
        return Ok(false);
    }

    // Parse
    let ast = Reader::from_str(&input).read_expr()?;
    // eprintln!("{:?}", ast);

    // Compile
    let mut buffer = ProgramBuffer::new();
    Compiler::new(&mut buffer).function(&ast);
    // eprintln!("{:?}", buffer.as_slice());

    // Execute
    unsafe {
        println!(
            "{:?}",
            Object::parse_word(buffer.make_executable().execute::<u64>(&mut [0; HEAP_SIZE]))?
        );
    }

    Ok(true)
}

fn main() -> Result<()> {
    color_eyre::install()?;

    loop {
        match read_eval_print() {
            Ok(cont) => {
                if !cont {
                    break;
                }
            }
            Err(err) => eprintln!("error: {}", err),
        }
    }

    Ok(())
}

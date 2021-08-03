#![feature(box_syntax, box_patterns, allocator_api, nonnull_slice_from_raw_parts)]

mod compiler;
mod object;
mod program_buffer;

use color_eyre::Result;
use compiler::Compiler;
use object::Object;
use program_buffer::ProgramBuffer;

fn main() -> Result<()> {
    color_eyre::install()?;

    let mut buffer = ProgramBuffer::new();
    Compiler::new(&mut buffer).function(&Object::Int(1234));

    unsafe {
        dbg!(buffer.make_executable().execute::<i32>());
    }

    Ok(())
}

#[cfg(test)]
mod test {}

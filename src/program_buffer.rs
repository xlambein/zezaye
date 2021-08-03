use std::{alloc::Allocator, ptr::NonNull};

use nix::sys::mman::{mmap, mprotect, munmap, MapFlags, ProtFlags};

struct PageAllocator;

unsafe impl Allocator for PageAllocator {
    fn allocate(
        &self,
        layout: std::alloc::Layout,
    ) -> Result<NonNull<[u8]>, std::alloc::AllocError> {
        let ptr = unsafe {
            let ptr = mmap(
                std::ptr::null_mut(),
                layout.size(),
                ProtFlags::PROT_READ | ProtFlags::PROT_WRITE,
                MapFlags::MAP_ANONYMOUS | MapFlags::MAP_PRIVATE,
                -1,
                0,
            )
            .map_err(|_| std::alloc::AllocError)?;
            // Safe because mmap shouldn't return NULL if there's no error
            NonNull::slice_from_raw_parts(std::mem::transmute(ptr), layout.size())
        };

        Ok(ptr)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: std::alloc::Layout) {
        munmap(std::mem::transmute(ptr), layout.size()).expect("munmap failed");
    }
}

pub struct ProgramBuffer {
    buf: Vec<u8, PageAllocator>,
}

impl ProgramBuffer {
    pub fn new() -> Self {
        Self {
            buf: Vec::new_in(PageAllocator),
        }
    }

    pub unsafe fn make_executable(self) -> ExecutableProgramBuffer {
        // TODO this function should be safe?
        mprotect(
            std::mem::transmute(self.buf.as_ptr()),
            self.buf.len(),
            ProtFlags::PROT_EXEC,
        )
        .expect("mprotect failed");
        ExecutableProgramBuffer { buf: self.buf }
    }

    pub fn as_slice(&self) -> &[u8] {
        self.buf.as_slice()
    }
}

#[repr(u8)]
pub enum Register {
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
pub enum ByteRegister {
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
pub enum Setcc {
    Equal = 0x04,
}

pub struct Indirect(pub Register, pub i8);

const REX_PREFIX: u8 = 0x48;

impl ProgramBuffer {
    fn byte(&mut self, byte: u8) -> &mut Self {
        self.buf.push(byte);
        self
    }

    fn bytes(&mut self, bytes: impl IntoIterator<Item = u8>) -> &mut Self {
        self.buf.extend(bytes);
        self
    }

    fn i32(&mut self, v: i32) -> &mut Self {
        self.bytes(v.to_le_bytes());
        self
    }

    fn u32(&mut self, v: u32) -> &mut Self {
        self.bytes(v.to_le_bytes());
        self
    }

    fn u64(&mut self, v: u64) -> &mut Self {
        self.bytes(v.to_le_bytes());
        self
    }

    pub fn mov_reg_imm32(&mut self, dst: Register, src: i32) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0xc7)
            .byte(0xc0 + dst as u8)
            .i32(src)
    }

    pub fn mov_reg_imm64(&mut self, dst: Register, src: u64) -> &mut Self {
        self.byte(REX_PREFIX).byte(0xb8 + dst as u8).u64(src)
    }

    pub fn add_reg_imm32(&mut self, dst: Register, src: i32) -> &mut Self {
        // TODO check for overflow
        self.byte(REX_PREFIX)
            .byte(0x81)
            .byte(0xc0 + dst as u8)
            .i32(src)
    }

    pub fn sub_reg_imm32(&mut self, dst: Register, src: i32) -> &mut Self {
        // TODO check for overflow
        self.byte(REX_PREFIX)
            .byte(0x81)
            .byte(0xe8 + dst as u8)
            .i32(src)
    }

    pub fn shr_reg_imm8(&mut self, dst: Register, src: u8) -> &mut Self {
        // TODO check for overflow
        self.byte(REX_PREFIX)
            .byte(0xc1)
            .byte(0xe8 + dst as u8)
            .byte(src)
    }

    pub fn cmp_reg_imm32(&mut self, dst: Register, src: u32) -> &mut Self {
        if let Register::Rax = dst {
            // Eax optimization
            self.byte(0x3d);
        } else {
            self.byte(0x81).byte(0xf8 + dst as u8);
        }
        self.u32(src)
    }

    pub fn setcc_imm8(&mut self, cond: Setcc, dst: ByteRegister) -> &mut Self {
        // TODO check for overflow
        self.byte(0x0f)
            .byte(0x90 + cond as u8)
            .byte(0xc0 + dst as u8)
    }

    pub fn store_reg_indirect(&mut self, dst: Indirect, src: Register) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0x89)
            .byte(0x40 + (src as u8) * 8 + dst.0 as u8)
            .byte(dst.1 as u8)
    }

    pub fn add_reg_indirect(&mut self, dst: Register, src: Indirect) -> &mut Self {
        // TODO check for overflow
        self.byte(REX_PREFIX)
            .byte(0x03)
            .byte(0x40 + (dst as u8) * 8 + src.0 as u8)
            .byte(src.1 as u8)
    }

    pub fn store_reg_reg_32(&mut self, dst: Register, src: Register) -> &mut Self {
        self.byte(0x89).byte(0xc0 + (src as u8) * 8 + dst as u8)
    }

    pub fn ret(&mut self) -> &mut Self {
        self.byte(0xc3)
    }

    pub fn prologue(&mut self) -> &mut Self {
        // push rbp
        // mov rbp, rsp
        self.byte(0x55).bytes([0x48, 0x89, 0xE5])
    }

    pub fn epilogue(&mut self) -> &mut Self {
        // mov rsp, rbp
        // pop rbp
        // ret
        self.bytes([0x48, 0x89, 0xEC]).byte(0x5D).ret()
    }
}

pub struct ExecutableProgramBuffer {
    buf: Vec<u8, PageAllocator>,
}

impl ExecutableProgramBuffer {
    pub unsafe fn make_writeable(self) -> ProgramBuffer {
        // TODO this function should be safe?
        mprotect(
            std::mem::transmute(self.buf.as_ptr()),
            self.buf.len(),
            ProtFlags::PROT_WRITE,
        )
        .expect("mprotect failed");
        ProgramBuffer { buf: self.buf }
    }

    pub unsafe fn execute<T>(&self) -> T {
        let fun: unsafe extern "C" fn() -> T = std::mem::transmute(self.buf.as_ptr());
        (fun)()
    }

    pub fn as_slice(&self) -> &[u8] {
        self.buf.as_slice()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_page_allocator() {
        let mut buf = Vec::new_in(PageAllocator);
        buf.push(b'a');
        assert_eq!(buf[0], b'a');
        buf.pop();
        assert_eq!(buf.len(), 0);
        buf.extend((0..5000).map(|x| (x % 256) as u8));
        assert_eq!(buf.len(), 5000);
        assert_eq!(buf[4999], (4999 % 256) as u8);
    }

    #[test]
    fn test_buffer_execute_and_edit() {
        let mut buf = ProgramBuffer::new();
        buf.buf
            // mov    rax,1234; ret
            .extend([0x48, 0xC7, 0xC0, 0xD2, 0x04, 0x00, 0x00, 0xC3]);
        unsafe {
            let buf = buf.make_executable();
            assert_eq!(buf.execute::<i64>(), 1234);
            let mut buf = buf.make_writeable();
            buf.buf[3] = 26;
            buf.buf[4] = 0;
            let buf = buf.make_executable();
            assert_eq!(buf.execute::<i64>(), 26);
        }
    }

    #[test]
    fn test_emit_store_reg_indirect() {
        let mut buffer = ProgramBuffer::new();
        buffer.store_reg_indirect(Indirect(Register::Rbp, -8), Register::Rax);
        assert_eq!(buffer.as_slice(), &[0x48, 0x89, 0x45, 0xF8]);

        let mut buffer = ProgramBuffer::new();
        buffer.store_reg_indirect(Indirect(Register::Rax, 16), Register::Rbx);
        assert_eq!(buffer.as_slice(), &[0x48, 0x89, 0x58, 0x10]);
    }
}

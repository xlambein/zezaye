use std::{alloc::Allocator, ffi::c_void, fmt, ptr::NonNull};

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

impl fmt::Display for ProgramBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for b in &self.buf {
            write!(f, "{:02x} ", b)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
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

#[repr(u8)]
enum Mod {
    /// Register indirect addressing mode
    Indirect = 0b00,
    /// One-byte signed displacement follows addressing mode byte(s)
    IndirectOneByteDisplacement = 0b01,
    /// Four-byte signed displacement follows addressing mode byte(s)
    IndirectFourByteDisplacement = 0b10,
    /// Register addressing mode
    Direct = 0b11,
}

const fn modrm(m: Mod, reg: u8, rm: u8) -> u8 {
    ((m as u8) << 6) | (reg << 3) | rm
}

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

    pub fn concatenate(&mut self, other: &ProgramBuffer) -> &mut Self {
        self.buf.extend(other.buf.as_slice());
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

    pub fn add_reg_reg(&mut self, dst: Register, src: Register) -> &mut Self {
        // TODO check for overflow
        self.byte(REX_PREFIX)
            .byte(0x01)
            .byte(0xc0 + (src as u8) * 8 + dst as u8)
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

    pub fn and_reg_reg(&mut self, dst: Register, src: Register) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0x21)
            .byte(0xc0 + (src as u8) * 8 + dst as u8)
    }

    pub fn and_reg_imm32(&mut self, dst: Register, src: u32) -> &mut Self {
        self.byte(0x81)
            .byte(modrm(Mod::Direct, /* /4 */ 4, dst as u8))
            .u32(src)
    }

    pub fn or_reg_reg(&mut self, dst: Register, src: Register) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0x09)
            .byte(0xc0 + (src as u8) * 8 + dst as u8)
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

    pub fn cmp_reg_reg(&mut self, dst: Register, src: Register) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0x39)
            .byte(0xc0 + dst as u8 + (src as u8) * 8)
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

    pub fn store_indirect_reg(&mut self, dst: Register, src: Indirect) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0x8b)
            .byte(0x40 + (dst as u8) * 8 + src.0 as u8)
            .byte(src.1 as u8)
    }

    pub fn store_indirect_reg8(&mut self, dst: ByteRegister, src: Indirect) -> &mut Self {
        self.byte(0x8a)
            .byte(modrm(
                Mod::IndirectOneByteDisplacement,
                dst as u8,
                src.0 as u8,
            ))
            .byte(src.1 as u8)
    }

    pub fn store_indirect_reg32(&mut self, dst: Register, src: Indirect) -> &mut Self {
        self.byte(0x8b)
            .byte(0x40 + (dst as u8) * 8 + src.0 as u8)
            .byte(src.1 as u8)
    }

    pub fn store_indirect_imm8(&mut self, dst: Indirect, src: u8) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0xc6)
            .byte(modrm(
                Mod::IndirectOneByteDisplacement,
                /* /0 */ 0,
                dst.0 as u8,
            ))
            .byte(dst.1 as u8)
            .byte(src)
    }

    pub fn store_indirect_imm32(&mut self, dst: Indirect, src: i32) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0xc7)
            .byte(modrm(
                Mod::IndirectOneByteDisplacement,
                /* /0 */ 0,
                dst.0 as u8,
            ))
            .byte(dst.1 as u8)
            .i32(src)
    }

    pub fn store_reg_reg_32(&mut self, dst: Register, src: Register) -> &mut Self {
        self.byte(0x89).byte(0xc0 + (src as u8) * 8 + dst as u8)
    }

    pub fn store_reg_reg(&mut self, dst: Register, src: Register) -> &mut Self {
        self.byte(REX_PREFIX)
            .byte(0x89)
            .byte(0xc0 + (src as u8) * 8 + dst as u8)
    }

    pub fn jmp(&mut self, distance: i32) -> &mut Self {
        if distance >= -128 && distance <= 127 {
            // Short jump
            self.byte(0xeb).byte(distance as i8 as u8)
        } else {
            self.byte(0xe9).i32(distance)
        }
    }

    pub fn jcc(&mut self, cond: Setcc, distance: i32) -> &mut Self {
        if distance >= -128 && distance <= 127 {
            // Short jump
            self.byte(0x70 + cond as u8).byte(distance as i8 as u8)
        } else {
            self.byte(0x0f).byte(0x80 + cond as u8).i32(distance)
        }
    }

    pub fn syscall(&mut self) -> &mut Self {
        self.byte(0x0f).byte(0x05)
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

    pub unsafe fn execute<T>(&self, heap: &mut [u8]) -> T {
        let fun: unsafe extern "C" fn(*mut c_void) -> T = std::mem::transmute(self.buf.as_ptr());
        (fun)(heap.as_mut_ptr() as *mut c_void)
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
            assert_eq!(buf.execute::<i64>(&mut []), 1234);
            let mut buf = buf.make_writeable();
            buf.buf[3] = 26;
            buf.buf[4] = 0;
            let buf = buf.make_executable();
            assert_eq!(buf.execute::<i64>(&mut []), 26);
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

    #[test]
    fn test() {
        let mut buffer = ProgramBuffer::new();
        buffer.store_indirect_imm32(Indirect(Register::Rsi, -8), 0x12);
        println!("{}", buffer);
    }
}

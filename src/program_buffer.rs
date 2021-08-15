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

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Register {
    AX = 0,
    CX,
    DX,
    BX,
    SP,
    BP,
    SI,
    DI,
}

#[derive(Debug, Clone, Copy)]
pub struct Ind(pub Register, pub i32);

#[derive(Debug, Clone, Copy)]
pub enum Operand {
    Indirect(Ind),
    Direct(Register),
}

impl Into<Operand> for Ind {
    fn into(self) -> Operand {
        Operand::Indirect(self)
    }
}

impl Into<Operand> for Register {
    fn into(self) -> Operand {
        Operand::Direct(self)
    }
}

pub trait Immediate8 {
    fn to_le_bytes(self) -> [u8; 1];
}

impl Immediate8 for i8 {
    fn to_le_bytes(self) -> [u8; 1] {
        self.to_le_bytes()
    }
}

impl Immediate8 for u8 {
    fn to_le_bytes(self) -> [u8; 1] {
        self.to_le_bytes()
    }
}

pub trait Immediate32 {
    fn to_le_bytes(self) -> [u8; 4];
}

impl Immediate32 for i32 {
    fn to_le_bytes(self) -> [u8; 4] {
        self.to_le_bytes()
    }
}

impl Immediate32 for u32 {
    fn to_le_bytes(self) -> [u8; 4] {
        self.to_le_bytes()
    }
}

pub trait Immediate64 {
    fn to_le_bytes(self) -> [u8; 8];
}

impl Immediate64 for i64 {
    fn to_le_bytes(self) -> [u8; 8] {
        self.to_le_bytes()
    }
}

impl Immediate64 for u64 {
    fn to_le_bytes(self) -> [u8; 8] {
        self.to_le_bytes()
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Cond {
    Equal = 0x04,
}

#[derive(Debug, Clone, Copy)]
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

/// https://sandpile.org/x86/opc_rm.htm
const fn modrm(m: Mod, reg: u8, rm: u8) -> u8 {
    ((m as u8) << 6) | (reg << 3) | rm
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum Scale {
    Scale1 = 0b00,
    Scale2 = 0b01,
    Scale4 = 0b10,
    Scale8 = 0b11,
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Index {
    AX = 0,
    CX,
    DX,
    BX,
    None,
    BP,
    SI,
    DI,
}

/// https://sandpile.org/x86/opc_rm.htm
const fn sib(scale: Scale, index: Index, base: Register) -> u8 {
    // TODO special shit if RBP is base
    ((scale as u8) << 6) | ((index as u8) << 3) | (base as u8)
}

const REX_PREFIX: u8 = 0x48;

macro_rules! op_d_imm8 {
    ($op_name:ident, $op_code:literal, $extension:literal) => {
        pub fn $op_name(&mut self, dest: impl Into<Operand>, src: impl Immediate8) -> &mut Self {
            self.byte($op_code).op1(dest, $extension).imm8(src)
        }
    };
}

macro_rules! op_d_imm {
    ($op_name:ident, $op_code:literal, $extension:literal) => {
        pub fn $op_name(&mut self, dest: impl Into<Operand>, src: impl Immediate32) -> &mut Self {
            self.byte($op_code).op1(dest, $extension).imm32(src)
        }
    };
}

macro_rules! op_d {
    ($op_name:ident, $op_code_fwd:literal, $op_code_bwd:literal) => {
        pub fn $op_name(&mut self, dest: impl Into<Operand>, src: impl Into<Operand>) -> &mut Self {
            self.op2($op_code_fwd, $op_code_bwd, dest, src)
        }
    };
}

macro_rules! op_q_imm8 {
    ($op_name:ident, $op_code:literal, $extension:literal) => {
        pub fn $op_name(&mut self, dest: impl Into<Operand>, src: impl Immediate8) -> &mut Self {
            self.byte(REX_PREFIX)
                .byte($op_code)
                .op1(dest, $extension)
                .imm8(src)
        }
    };
}

macro_rules! op_q_imm {
    ($op_name:ident, $op_code:literal, $extension:literal) => {
        pub fn $op_name(&mut self, dest: impl Into<Operand>, src: impl Immediate32) -> &mut Self {
            self.byte(REX_PREFIX)
                .byte($op_code)
                .op1(dest, $extension)
                .imm32(src)
        }
    };
}

macro_rules! op_q {
    ($op_name:ident, $op_code_fwd:literal, $op_code_bwd:literal) => {
        pub fn $op_name(&mut self, dest: impl Into<Operand>, src: impl Into<Operand>) -> &mut Self {
            self.byte(REX_PREFIX)
                .op2($op_code_fwd, $op_code_bwd, dest, src)
        }
    };
}

impl ProgramBuffer {
    fn byte(&mut self, byte: u8) -> &mut Self {
        self.buf.push(byte);
        self
    }

    fn bytes(&mut self, bytes: impl IntoIterator<Item = u8>) -> &mut Self {
        self.buf.extend(bytes);
        self
    }

    pub fn concatenate(&mut self, other: &ProgramBuffer) -> &mut Self {
        self.buf.extend(other.buf.as_slice());
        self
    }

    fn imm8(&mut self, src: impl Immediate8) -> &mut Self {
        self.bytes(src.to_le_bytes())
    }

    fn imm32(&mut self, src: impl Immediate32) -> &mut Self {
        self.bytes(src.to_le_bytes())
    }

    fn imm64(&mut self, src: impl Immediate64) -> &mut Self {
        self.bytes(src.to_le_bytes())
    }

    fn direct(&mut self, rm: Register, reg: u8) -> &mut Self {
        self.byte(modrm(Mod::Direct, reg, rm as u8))
    }

    fn maybe_sib(&mut self, reg: Register) -> &mut Self {
        if reg == Register::SP {
            self.byte(sib(Scale::Scale1, Index::None, Register::SP))
        } else {
            self
        }
    }

    fn indirect(&mut self, rm: Ind, reg: u8) -> &mut Self {
        if rm.1 == 0 {
            self.byte(modrm(Mod::Indirect, reg, rm.0 as u8))
                .maybe_sib(rm.0)
        } else if (rm.1 as i8) as i32 == rm.1 {
            self.byte(modrm(Mod::IndirectOneByteDisplacement, reg, rm.0 as u8))
                .maybe_sib(rm.0)
                .imm8(rm.1 as i8)
        } else {
            self.byte(modrm(Mod::IndirectFourByteDisplacement, reg, rm.0 as u8))
                .maybe_sib(rm.0)
                .imm32(rm.1)
        }
    }

    fn op1(&mut self, dest: impl Into<Operand>, reg: u8) -> &mut Self {
        match dest.into() {
            Operand::Direct(dest) => self.direct(dest, reg),
            Operand::Indirect(dest) => self.indirect(dest, reg),
        }
    }

    fn op2(
        &mut self,
        fwd: u8,
        bwd: u8,
        dest: impl Into<Operand>,
        src: impl Into<Operand>,
    ) -> &mut ProgramBuffer {
        match (dest.into(), src.into()) {
            (Operand::Direct(dest), Operand::Direct(src)) => self.byte(fwd).direct(dest, src as u8),
            (Operand::Indirect(dest), Operand::Direct(src)) => {
                self.byte(fwd).indirect(dest, src as u8)
            }
            (Operand::Direct(dest), Operand::Indirect(src)) => {
                self.byte(bwd).indirect(src, dest as u8)
            }
            (Operand::Indirect(_), Operand::Indirect(_)) => {
                panic!("operation cannot have indirect source and destination at the same time")
            }
        }
    }

    // ADD
    op_d_imm!(add_d_imm, 0x81, 0);
    op_d!(add_d, 0x01, 0x03);
    op_q_imm!(add_q_imm, 0x81, 0);
    op_q!(add_q, 0x01, 0x03);

    // OR
    op_d_imm!(or_d_imm, 0x81, 1);
    op_d!(or_d, 0x09, 0x0B);
    op_q_imm!(or_q_imm, 0x81, 1);
    op_q!(or_q, 0x09, 0x0B);

    // AND
    op_d_imm!(and_d_imm, 0x81, 4);
    op_d!(and_d, 0x21, 0x23);
    op_q_imm!(and_q_imm, 0x81, 4);
    op_q!(and_q, 0x21, 0x23);

    // SUB
    op_d_imm!(sub_d_imm, 0x81, 5);
    op_d!(sub_d, 0x29, 0x2B);
    op_q_imm!(sub_q_imm, 0x81, 5);
    op_q!(sub_q, 0x29, 0x2B);

    // CMP
    op_d_imm!(cmp_d_imm, 0x81, 7);
    op_d!(cmp_d, 0x39, 0x3B);
    op_q_imm!(cmp_q_imm, 0x81, 7);
    op_q!(cmp_q, 0x39, 0x3B);

    // MOV
    op_d_imm!(mov_d_imm, 0xc7, 0);
    op_d!(mov_d, 0x89, 0x8b);
    op_q_imm!(mov_q_imm, 0xc7, 0);
    op_q!(mov_q, 0x89, 0x8b);

    /// Moves the 64-bit immediate into the destination register
    pub fn mov_q_imm64(&mut self, dest: Register, src: impl Immediate64) -> &mut Self {
        self.byte(REX_PREFIX).byte(0xb8 + dest as u8).imm64(src)
    }

    /// Moves the 8-bit immediate into the lower byte of the destination
    pub fn mov_bl_imm(&mut self, dest: impl Into<Operand>, src: impl Immediate8) -> &mut Self {
        self.byte(REX_PREFIX).byte(0xc6).op1(dest, 0).imm8(src)
    }

    // MOVZX
    /// Moves & 0-extend the source byte into the lower byte of the destination register
    pub fn movzx_q(&mut self, dest: Register, src: impl Into<Operand>) -> &mut Self {
        self.byte(REX_PREFIX).byte(0x0f).op2(0xb6, 0xb6, dest, src)
    }

    // JMP
    pub fn jmp_rel(&mut self, distance: i32) -> &mut Self {
        if distance >= -128 && distance <= 127 {
            // Short jump
            self.byte(0xeb).byte(distance as i8 as u8)
        } else {
            self.byte(0xe9).imm32(distance)
        }
    }

    // JCC
    pub fn jcc(&mut self, cond: Cond, distance: i32) -> &mut Self {
        if distance >= -128 && distance <= 127 {
            // Short jump
            self.byte(0x70 + cond as u8).byte(distance as i8 as u8)
        } else {
            self.byte(0x0f).byte(0x80 + cond as u8).imm32(distance)
        }
    }

    // SETCC
    pub fn setcc(&mut self, cond: Cond, dst: impl Into<Operand>) -> &mut Self {
        // TODO check for overflow
        self.byte(REX_PREFIX)
            .byte(0x0f)
            .byte(0x90 + cond as u8)
            .op1(dst, 0)
    }

    // SHL
    op_d_imm8!(shl_d_imm, 0xc1, 4);
    op_q_imm8!(shl_q_imm, 0xc1, 4);

    // SHR
    op_d_imm8!(shr_d_imm, 0xc1, 5);
    op_q_imm8!(shr_q_imm, 0xc1, 5);

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
}

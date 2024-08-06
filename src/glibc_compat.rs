use core::marker::PhantomData;

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
const JMP_BUF_SIZE: usize = 8;

#[cfg(target_arch = "riscv64")]
const JMP_BUF_SIZE: usize = 14 /* pc + regs + sp */ + crate::riscv64::floating_point_registers();

/// `JmpBufFields` are the accessible fields when viewed via a JmpBuf pointer.
/// But also: You shouldn't be poking at these!
#[repr(C)]
pub struct JmpBufFields {
    _buf: [u64; JMP_BUF_SIZE],
    _neither_send_nor_sync: PhantomData<*const u8>,
}

/// `SigJmpBufFields` are the accessible fields when viewed via a SigJmpBuf pointer.
/// But also: You shouldn't be poking at these!
#[repr(C)]
pub struct SigJmpBufFields {
    // This *must* be the first field. We allow `SigJmpBuf` to be transmuted to
    // a `JmpBuf` and then back again depending on the host libc. (e.g. glibc
    // has setjmp as a shallow wrapper around sigsetjmp, and will write to
    // fields past the `__jmp_buf`).
    __jmp_buf: JmpBufFields,
    __mask_was_saved: isize,
    __saved_mask: libc::sigset_t,
}

/// This is the type you use to allocate a JmpBuf on the stack.
/// (Glibc puns the two.)
pub type JmpBufStruct = SigJmpBufFields;

/// This is the type you use to allocate a SigJmpBuf on the stack.
pub type SigJmpBufStruct = SigJmpBufFields;

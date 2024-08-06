// Adapted from:
//
// https://rust-lang.zulipchat.com/#narrow/stream/210922-project-ffi-unwind/topic/cost.20of.20supporting.20longjmp.20without.20annotations/near/301840755
//
// ```rust
// unsafe fn setjmp<F: FnOnce() -> c_int>(env: *mut jmp_buf, f: F) -> c_int {
//     let mut f = core::mem::MaybeUninit::new(f);
//     extern "C" fn call_f<F: FnOnce() -> c_int>(f: *mut F) -> c_int {
//         (unsafe { f.read() })()
//     }
//     let ret: c_int;
//     std::arch::asm!(
//         "call setjmp",
//         "test eax, eax",
//         "jne 1f",
//         "mov rdi, r12",
//         "call {}",
//         "1:",
//         sym call_f::<F>,
//         in("rdi") env,
//         in("r12") f.as_mut_ptr(),
//         lateout("rax") ret,
//         clobber_abi("C"),
//     );
//     ret
// }
// ```

// Some notes about inline asm:
//
// * For System-V, first three arguments for x86_64 are [rdi,rsi,rdx]. (This
//   code never passes more than three arguments.)
//
//   For Microsft x86, Wikipedia says the first three arguments are [rcx,rdx, r8].
//
// * call instructions (like to _setjmp) can trample caller-save registers, but
//   not callee save ones. We can direct the compiler to assign the bits of
//   state that need to live across calls to *callee-save* registers.
//
// * The set of callee-save registers depends on the ABI.
//
//   System-V callee-save regs are [RBX, RSP, RBP, R12, 13, R14, R15]
//
//   Microsoft x64 callee-save regs are [RBX, RBP, RDI, RSI, RSP, R12, R13, R14, R15].
//
//   (as a separate gotcha, one must also allocate shadow space on the stack
//   immediately before any calls in that convention)
//
//   So, there's at the very least a number of things to double-check here.
//
// * If we were writing *all* the machine code, then we would have to include
//   code here to save and restore state regardless of that choice between
//   caller- or callee-save. But we are not writing all the machine code; LLVM
//   is going to handle the stack shuffling for us. All we need to do is assign
//   registers according to the roles we want them to play.

use crate::{JmpBuf, JmpBufFields, JmpBufStruct};
use crate::{SigJmpBuf, SigJmpBufFields, SigJmpBufStruct};
use core::mem::MaybeUninit;
use libc::c_int;

#[cfg(target_arch = "x86_64")]
macro_rules! maybesig_setjmp_asm {
    ($setjmp:ident, $jbuf_ptr:ident, $ifsig_savemask:ident, $closure_env_ptr:ident, $c2r:ident, $ret:ident) => {
        core::arch::asm!(
            // savemask is already in position rsi..
            "mov rdi, r12",  // move jbuf_ptr into arg position for sigsetjmp call
            "call {tmp}",    // fills in jbuf; future longjmp calls go here.
            "test eax, eax", // inspect return value of setjmp
            "jne 1f",        // if non-zero, skip the callback invocation
            "mov rdi, r12",  // otherwise, move jbuf ptr into position...
            "mov rsi, r13",  // ... and move callback ptrs into position...
            "call r14"  ,    // ... and invoke the callback
            "1:",            // at this point, rax carries the return value (from either outcome)
            // we let compiler pick this register since we don't need to preseve
            // it across the first call.
            tmp = in(reg) $setjmp,
            in("rsi") $ifsig_savemask,
            // we use [r12,r13,r14] explicitly as they are always callee-save
            // and thus will be preserved across the call to setjmp.
            in("r12") $jbuf_ptr,
            in("r13") $closure_env_ptr,
            in("r14") $c2r,
            // we use rax explicitly since we just pass along return register
            // set by the return path (be it normal return or via longjmp).
            out("rax") $ret,
            clobber_abi("sysv64"), // clobber abi reflects call effects, including {eax,rdi,rsi}...
            out("rdi") _, // ... but, we write rdi before reading sigsetjmp; avoid collision.
        );
    }
}

#[cfg(target_arch = "aarch64")]
macro_rules! maybesig_setjmp_asm {
    ($sigsetjmp:ident, $jbuf_ptr:ident, $ifsig_savemask:ident, $closure_env_ptr:ident, $c2r:ident, $ret:ident) => {
        core::arch::asm!(
            // savemask, if needed, is already in x1
            "mov x0, x21", // move saved jbuf_ptr to sigsetjmp param position. (savemask is already in position)
            "blr {tmp}",   // fills in jbuf; future longjmp calls go here.
            "cbnz w0, 1f", // if return value non-zero, skip the callback invocation
                           // (and if return value non-zero, we cannot assume register state has been restored!)
            "mov x0, x21", // move saved jmp buf into callback's arg position
            "mov x1, x20", // move saved closure env into callback's arg position
            "blr x22",     // invoke the callback
            "1:",          // at this point, x0 carries the return value (from either outcome)
            // we let compiler pick this register since we don't need to preseve
            // it across the first call.
            tmp = in(reg) $sigsetjmp,
            in("x1") $ifsig_savemask, // savemask arg position for sigsetjmp
            out("x0") $ret, // the output will be stored here.
            // [x20,x21,x22] are all callee-save registers for the normal sigsetjmp return.
            // we will have them to reference.
            in("x20") $closure_env_ptr,
            in("x21") $jbuf_ptr,
            in("x22") $c2r,
            clobber_abi("C"), // clobber abi reflects call effects, including {x0,x1,x2,x3}...
        );
    }
}

#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
macro_rules! maybesig_setjmp_asm {
    ($sigsetjmp:ident, $jbuf_ptr:ident, $ifsig_savemask:ident, $closure_env_ptr:ident, $c2r:ident, $ret:ident) => {
        core::arch::asm!(
            // savemask, if needed, is already in a1
            "mv a0, s3",     // move saved jbuf_ptr to sigsetjmp param position. (savemask is already in position)
            "jalr 0({tmp})", // fills in jbuf; future longjmp calls go here.
            "bnez a0, 1f",   // if return value non-zero, skip the callback invocation
                             // (and if return value non-zero, we cannot assume register state has been restored!)
            "mv a0, s3",     // move saved jmp buf into callback's arg position
            "mv a1, s2",     // move saved closure env into callback's arg position
            "jalr 0(s4)",    // invoke the callback
            "1:",            // at this point, a0 carries the return value (from either outcome)
            // we let compiler pick this register since we don't need to preseve
            // it across the first call.
            tmp = in(reg) $sigsetjmp,
            in("a1") $ifsig_savemask, // savemask arg position for sigsetjmp
            out("a0") $ret, // the output will be stored here.
            // [s2,s3,s4] are all callee-save registers for the normal sigsetjmp return.
            // we will have them to reference.
            in("s2") $closure_env_ptr,
            in("s3") $jbuf_ptr,
            in("s4") $c2r,
            clobber_abi("C"), // clobber abi reflects call effects, including {x1,x5,x6,x7}...
        );
    }
}

/// Covers the usual use case for setjmp: it invokes the callback, and the code
/// of the callback can use longjmp to exit early from the call_with_setjmp.
#[inline(never)] // see https://github.com/pnkfelix/cee-scape/issues/14
pub fn call_with_setjmp<F>(mut callback: F) -> c_int
where
    F: for<'a> FnOnce(&'a JmpBufFields) -> c_int,
{
    extern "C" fn call_from_c_to_rust<F>(jbuf: JmpBuf, closure_env_ptr: *mut F) -> c_int
    where
        F: for<'a> FnOnce(&'a JmpBufFields) -> c_int,
    {
        // Dereference `closure_env_ptr` with .read() to acquire ownership of
        // the FnOnce object, then call it. (See also the forget note below.)
        //
        // Note that `closure_env_ptr` is not a raw function pointer, it's a
        // pointer to a FnOnce; the code we call comes from the generic `F`.
        unsafe { (closure_env_ptr.read())(&*jbuf) }
    }
    unsafe {
        let mut jbuf = MaybeUninit::<JmpBufStruct>::zeroed().assume_init();
        let ret: c_int;
        let jbuf_ptr = core::ptr::addr_of_mut!(jbuf);
        let closure_env_ptr = core::ptr::addr_of_mut!(callback);

        // The callback is now effectively owned by `closure_env_ptr` (i.e., the
        // `closure_env_ptr.read()` call in `call_from_c_to_rust` will take a
        // direct bitwise copy of its state, and pass that ownership into the
        // FnOnce::call_once invocation.)
        //
        // Therefore, we need to forget about our own ownership of the callback now.
        core::mem::forget(callback);

        // Note: we never call _setjmp from Rust code, just from the assembly
        // block below.
        extern "C" {
            #[cfg_attr(target_os = "macos", link_name = "_setjmp")]
            #[cfg_attr(target_os = "linux", link_name = "_setjmp")]
            fn find_your_targets_setjmp(env: JmpBuf) -> c_int;
        }
        let setjmp = find_your_targets_setjmp;
        let c2r = call_from_c_to_rust::<F>;
        let unused_savemask: c_int = 0; // why can't we do `MaybeUninit::uninit().assume_init()` (this is unused).

        maybesig_setjmp_asm!(setjmp, jbuf_ptr, unused_savemask, closure_env_ptr, c2r, ret);

        ret
    }
}

/// Covers the usual use case for sigsetjmp: it invokes the callback, and the code
/// of the callback can use siglongjmp to exit early from the call_with_sigsetjmp.
#[inline(never)] // see https://github.com/pnkfelix/cee-scape/issues/14
pub fn call_with_sigsetjmp<F>(savemask: bool, mut callback: F) -> c_int
where
    F: for<'a> FnOnce(&'a SigJmpBufFields) -> c_int,
{
    extern "C" fn call_from_c_to_rust<F>(jbuf: SigJmpBuf, closure_env_ptr: *mut F) -> c_int
    where
        F: for<'a> FnOnce(&'a SigJmpBufFields) -> c_int,
    {
        // Dereference `closure_env_ptr` with .read() to acquire ownership of
        // the FnOnce object, then call it. (See also the forget note below.)
        //
        // Note that `closure_env_ptr` is not a raw function pointer, it's a
        // pointer to a FnOnce; the code we call comes from the generic `F`.
        unsafe { (closure_env_ptr.read())(&*jbuf) }
    }

    let savemask: c_int = if savemask { 1 } else { 0 };

    unsafe {
        let mut jbuf = MaybeUninit::<SigJmpBufStruct>::zeroed().assume_init();
        let ret: c_int;
        let jbuf_ptr = core::ptr::addr_of_mut!(jbuf);
        let closure_env_ptr = core::ptr::addr_of_mut!(callback);

        // The callback is now effectively owned by `closure_env_ptr` (i.e., the
        // `closure_env_ptr.read()` call in `call_from_c_to_rust` will take a
        // direct bitwise copy of its state, and pass that ownership into the
        // FnOnce::call_once invocation.)
        //
        // Therefore, we need to forget about our own ownership of the callback now.
        core::mem::forget(callback);

        // Note: we never call _setjmp from Rust code, just from the assembly
        // block below.
        extern "C" {
            #[cfg_attr(target_os = "macos", link_name = "sigsetjmp")]
            #[cfg_attr(target_os = "linux", link_name = "__sigsetjmp")]
            fn find_your_targets_sigsetjmp(env: SigJmpBuf, savemask: c_int) -> c_int;
        }
        let sigsetjmp = find_your_targets_sigsetjmp;
        let c2r = call_from_c_to_rust::<F>;

        maybesig_setjmp_asm!(sigsetjmp, jbuf_ptr, savemask, closure_env_ptr, c2r, ret);

        ret
    }
}

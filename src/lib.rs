//! The cee-scape crate provides access to `setjmp` and `sigsetjmp`
//! functionality, via an interface that ensures LLVM won't miscompile things.
//!
//! # Example usage
//!
//! The main intention is for this interface to be used with C code that expects
//! to longjmp via jump buffers established at Rust-to-C FFI boundaries.
//!
//! Here is an example, where we are using `extern "C"` functions as stand-ins
//! for the code you would normally expect to find in an external C library.
//!
//! ```rust
//! mod pretend_this_comes_from_c {
//!     use cee_scape::JmpBuf;
//!
//!     // Returns sum of a and b, but longjmps through `env` if either argument
//!     // is negative (passing 1) or if the sum overflows (passing 2).
//!     pub extern "C" fn careful_sum(env: JmpBuf, a: i32, b: i32) -> i32 {
//!         check_values(env, a, b);
//!         return a + b;
//!     }
//!
//!     extern "C" fn check_values(env: JmpBuf, a: i32, b: i32) {
//!         use cee_scape::longjmp;
//!         if a < 0 || b < 0 { unsafe { longjmp(env, -1); } }
//!         if (i32::MAX - a) < b { unsafe { longjmp(env, -2); } }
//!     }
//! }
//!
//! use pretend_this_comes_from_c::careful_sum as sum;
//! use cee_scape::call_with_setjmp;
//!
//! assert_eq!(call_with_setjmp(|env| { sum(env, 10, 20) + 1000 }), 1030);
//! assert_eq!(call_with_setjmp(|env| { sum(env, -10, 20) + 1000 }), -1);
//! assert_eq!(call_with_setjmp(|env| { sum(env, 10, -20) + 1000 }), -1);
//! assert_eq!(call_with_setjmp(|env| { sum(env, i32::MAX, 1) + 1000 }), -2);
//! ```
//!
//! # Background on `setjmp` and `longjmp`.
//!
//! The `setjmp` and `longjmp` functions in C are used as the basis for
//! "non-local jumps", also known as "escape continuations". It is a way to have
//! a chain of calls "`entry` calls `middle_1` calls `middle_2` calls
//! `innermost`", where the bodies of `middle_1` or `middle_2` or `innermost`
//! might at some point decide that they want to jump all the way back to
//! `entry` without having to pass through the remaining code that they would
//! normally have to execute when returning via each of their respective
//! callers.
//!
//! In C, this is done by having `entry` first call `setjmp` to initialize a
//! jump enviroment (which would hold, for example, the current stack pointer
//! and, if present, the current frame pointer), and then passing a pointer to
//! that jump environment along during each of the child subroutines of A. If at
//! any point a child subroutine wants to jump back to the point where `setjmp`
//! had first returned, that child subroutine invoke `longjmp`, which reestablishes
//! the stack to the position it had when `setjmp` had originally returned.
//!
//! # Safety (or lack thereof)
//!
//! This crate cannot ensure that the usual Rust control-flow rules are upheld,
//! which means that the act of actually doing a longjmp/siglongjmp to a
//! non-local jump environment (aka continuation) is *unsafe*.
//!
//! For example, several Rust API's rely on an assumption that they will always
//! run some specific cleanup code after a callback is done. Such cleanup is
//! sometimes encoded as a Rust destructor, but it can also just be directly
//! encoded as straight-line code waiting to be run.
//!
//! Calls to `longjmp` blatantly break these assumptions. A `longjmp` invocation
//! does not invoke any Rust destructors, and it does not "unwind the stack".
//! All pending cleanup code between the `longjmp` invocation and the target
//! jump environment (i.e. the place where the relevant `setjmp` first returned)
//! is skipped.
//!
//! ```rust
//! use std::cell::Cell;
//! // This emulates a data structure that has an ongoing invariant:
//! // the `depth` is incremented/decremented according to entry/exit
//! // to a given callback (see `DepthTracker::enter` below).
//! pub struct DepthTracker { depth: Cell<usize>, }
//!
//! let track = DepthTracker::new();
//! cee_scape::call_with_setjmp(|env| {
//!     track.enter(|| {
//!         // This is what we expect: depth is larger in context of
//!         // DepthTracker::enter callback
//!         assert_eq!(track.depth(), 1);
//!         "normal case"
//!     });
//!     0
//! });
//!
//! // Normal case: the tracked depth has returned to zero.
//! assert_eq!(track.depth(), 0);
//!
//! assert_eq!(cee_scape::call_with_setjmp(|env| {
//!     track.enter(|| {
//!         // This is what we expect: depth is larger in context of
//!         // DepthTracker::enter callback
//!         assert_eq!(track.depth(), 1);
//!         // DIFFERENT: Now we bypass the DepthTracker's cleanup code.
//!         unsafe { cee_scape::longjmp(env, 4) }
//!         "abnormal case"
//!     });
//!     0
//! }), 4);
//!
//! // This is the "surprise" due to the DIFFERENT line: longjmp skipped
//! // over the decrement from returning from the callback, and so the count
//! // is not consistent with what the data structure expects.
//! assert_eq!(track.depth(), 1 /* not 0 */);
//!
//! // (These are just support routines for the `DepthTracker` above.)
//! impl DepthTracker {
//!     pub fn depth(&self) -> usize {
//!         self.depth.get()
//!     }
//!     pub fn enter<X>(&self, callback: impl FnOnce() -> X) -> X {
//!         self.update(|x|x+1);
//!         let ret = callback();
//!         self.update(|x|x-1);
//!         ret
//!     }
//!     fn update(&self, effect: impl Fn(usize) -> usize) {
//!         self.depth.set(effect(self.depth.get()));
//!     }
//!     pub fn new() -> Self {
//!         DepthTracker { depth: Cell::new(0) }
//!     }
//! }
//! ```
//!
//! In short, the `longjmp` routine is a blunt instrument. When a `longjmp`
//! invocation skips some cleanup code, the compiler cannot know whether
//! skipping that cleanup code was exactly what the program author intended, or
//! if it represents a programming error.
//!
//! Furthermore, much cleanup code of this form is enforcing *Rust safety
//! invariants*. This is why `longjmp` is provided here as an *unsafe* method;
//! that is a reminder that while one can invoke `call_with_setjmp` safely, the
//! obligation remains to audit whether any invocations of `longjmp` on the
//! provided jump environment are breaking those safety invariants by skipping
//! over such cleanup code.
//!
//! # Some static checking
//!
//! While not all of Rust's safety rules are statically enforced, one important
//! one is enforced: When invoking `call_with_setjmp`, the saved jump
//! environment is not allowed to escape the scope of the callback that is fed
//! to `call_with_setjmp`:
//!
//! ```compile_fail
//! let mut escaped = None;
//! cee_scape::call_with_setjmp(|env| {
//!     // If `env` were allowed to escape...
//!     escaped = Some(env);
//!     0
//! });
//! // ... it would be bad if we could then do this with it.
//! unsafe { cee_scape::longjmp(escaped.unwrap(), 1); }
//! ```
//!
//! We also cannot share jump environments across threads, because it is
//! undefined behavior to `longjmp` via a jump environments that was initialized
//! by a call to `setjmp` in a different thread.
//!
//! ```compile_fail
//! cee_scape::call_with_setjmp(move |env| {
//!     std::thread::scope(|s| {
//!         s.spawn(move || {
//!             unsafe { cee_scape::longjmp(env, 1); }
//!         });
//!         0
//!     })
//! });
//! ```

use libc::c_int;
use std::marker::PhantomData;
use std::mem::MaybeUninit;

#[repr(C)]
pub struct JmpBufStruct {
    _buf: [u64; 8],
    _neither_send_nor_sync: PhantomData<*const u8>,
}

/// This is the type of the first argument that is fed to longjmp.
pub type JmpBuf = *const JmpBufStruct;

/// This is the type of the first argument that is fed to siglongjmp.
pub type SigJmpBuf = *const SigJmpBufStruct;

#[repr(C)]
pub struct SigJmpBufStruct {
    // This *must* be the first field. We allow `SigJmpBuf` to be transmuted to
    // a `JmpBuf` and then back again depending on the host libc. (e.g. glibc
    // has setjmp as a shallow wrapper around sigsetjmp, and will write to
    // fields past the `__jmp_buf`).
    __jmp_buf: JmpBufStruct,
    __mask_was_saved: isize,
    __saved_mask: libc::sigset_t,
}

extern "C" {
    /// Given a calling environment `jbuf` (which one can acquire via
    /// `call_with_setjmp`) and a non-zero value `val`, moves the stack and
    /// program counters to match the return position of where `jbuf` was
    /// established via a call to `setjmp`, and then returns `val` from that
    /// spot.
    ///
    /// You should only provide non-zero values for `val`. A zero-value may or
    /// may not be replaced with a non-zero value for the return to the
    /// non-local jump environment, depending on the underlying C library that
    /// is linked in. (It may be silently replaced with a non-zero value, as a
    /// non-zero value is the only way for the internal machinery to distinguish
    /// between the first return from the initial call versus a non-local
    /// return).
    pub fn longjmp(jbuf: JmpBuf, val: c_int) -> !;

    /// Given a calling environment `jbuf` (which one can acquire via
    /// `call_with_sigsetjmp`) and a non-zero value `val`, moves the stack and
    /// program counters to match the return position of where `jbuf` was
    /// established via a call to `setjmp`, and then returns `val` from that
    /// spot.
    ///
    /// You should only provide non-zero values for `val`. A zero-value may or
    /// may not be replaced with a non-zero value for the return to the
    /// non-local jump environment, depending on the underlying C library that
    /// is linked in. (It may be silently replaced with a non-zero value, as a
    /// non-zero value is the only way for the internal machinery to distinguish
    /// between the first return from the initial call versus a non-local
    /// return).
    pub fn siglongjmp(jbuf: SigJmpBuf, val: c_int) -> !;
}

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

/// Covers the usual use case for setjmp: it invokes the callback, and the code
/// of the callback can use longjmp to exit early from the call_with_setjmp.
pub fn call_with_setjmp<F>(mut callback: F) -> c_int
where
    F: for<'a> FnOnce(&'a JmpBufStruct) -> c_int,
{
    extern "C" fn call_from_c_to_rust<F>(jbuf: JmpBuf, closure_env_ptr: *mut F) -> c_int
    where
        F: for<'a> FnOnce(&'a JmpBufStruct) -> c_int,
    {
        unsafe { (closure_env_ptr.read())(&*jbuf) }
    }
    unsafe {
        // We use `SigJmpBuf` here rather than just `JmpBuf` because some
        // platforms, like glibc, use the same structure for both (and just have
        // `setjmp` be a shallow wrapper around `sigsetjmp`).
        let mut jbuf = MaybeUninit::<SigJmpBufStruct>::zeroed().assume_init();
        let ret: c_int;
        let jbuf_ptr = std::ptr::addr_of_mut!(jbuf);
        let closure_env_ptr = std::ptr::addr_of_mut!(callback);

        // Note: we never call _setjmp from Rust code, just from the assembly
        // block below.
        extern "C" {
            #[cfg_attr(target_os = "macos", link_name = "_setjmp")]
            #[cfg_attr(target_os = "linux", link_name = "_setjmp")]
            fn find_your_targets_setjmp(env: JmpBuf) -> c_int;
        }
        let setjmp = find_your_targets_setjmp;
        let c2r = call_from_c_to_rust::<F>;
        std::arch::asm!(
            "mov rdi, r12",  // move jbuf_ptr into argument position for setjmp call
            "call {tmp}", // fills in jbuf; future longjmp calls go here
            "test eax, eax", // inspect return value of setjmp
            "jne 1f",        // if non-zero, skip the callback invocation
            "mov rdi, r12",  // otherwise, move jbuf ptr into position...
            "mov rsi, r13",  // ... and move callback ptrs into position...
            "call r14",    // ... and invoke the callback
            "1:",            // at this point, rax carries the return value (from either outcome)

            // we let compiler pick this register since we don't need to preseve
            // it across the first call.
            tmp = in(reg) setjmp,
            // we use [r12,r13,r14] explicitly as they are always callee-save
            // and thus will be preserved across the call to setjmp.
            in("r12") jbuf_ptr,
            in("r13") closure_env_ptr,
            in("r14") c2r,
            // we use rax explicitly since we just pass along return register
            // set by the return path (be it normal return or via longjmp).
            out("rax") ret,
            clobber_abi("sysv64"), // clobber abi reflects call effects, including {eax,rdi,rsi}...
            out("rdi") _, // ... but, we write rdi before reading sigsetjmp; avoid collision.
        );

        ret
    }
}

/// Covers the usual use case for sigsetjmp: it invokes the callback, and the code
/// of the callback can use siglongjmp to exit early from the call_with_sigsetjmp.
pub fn call_with_sigsetjmp<F>(savemask: bool, mut callback: F) -> c_int
where
    F: for<'a> FnOnce(&'a SigJmpBufStruct) -> c_int,
{
    extern "C" fn call_from_c_to_rust<F>(jbuf: SigJmpBuf, closure_env_ptr: *mut F) -> c_int
    where
        F: for<'a> FnOnce(&'a SigJmpBufStruct) -> c_int,
    {
        unsafe { (closure_env_ptr.read())(&*jbuf) }
    }

    let savemask: c_int = if savemask { 1 } else { 0 };

    unsafe {
        let mut jbuf = MaybeUninit::<SigJmpBufStruct>::zeroed().assume_init();
        let ret: c_int;
        let jbuf_ptr = std::ptr::addr_of_mut!(jbuf);
        let closure_env_ptr = std::ptr::addr_of_mut!(callback);

        // Note: we never call _setjmp from Rust code, just from the assembly
        // block below.
        extern "C" {
            #[cfg_attr(target_os = "macos", link_name = "sigsetjmp")]
            #[cfg_attr(target_os = "linux", link_name = "__sigsetjmp")]
            fn find_your_targets_sigsetjmp(env: SigJmpBuf, savemask: c_int) -> c_int;
        }
        let sigsetjmp = find_your_targets_sigsetjmp;
        let c2r = call_from_c_to_rust::<F>;
        std::arch::asm!(
            // savemask is already in position rsi..
            "mov rdi, r12",  // move jbuf_ptr into arg position for sigsetjmp call
            "call {sigsetjmp}", // fills in jbuf; future longjmp calls go here.
            "test eax, eax", // inspect return value of setjmp
            "jne 1f",        // if non-zero, skip the callback invocation
            "mov rdi, r12",  // otherwise, move jbuf ptr into position...
            "mov rsi, r13",  // ... and move callback ptrs into position...
            "call r14"  ,    // ... and invoke the callback
            "1:",            // at this point, rax carries the return value (from either outcome)
            // we let compiler pick this register since we don't need to preseve
            // it across the first call.
            sigsetjmp = in(reg) sigsetjmp,
            in("rsi") savemask,
            // we use [r12,r13,r14] explicitly as they are always callee-save
            // and thus will be preserved across the call to setjmp.
            in("r12") jbuf_ptr,
            in("r13") closure_env_ptr,
            in("r14") c2r,
            // we use rax explicitly since we just pass along return register
            // set by the return path (be it normal return or via longjmp).
            out("rax") ret,
            clobber_abi("sysv64"), // clobber abi reflects call effects, including {eax,rdi,rsi}...
            out("rdi") _, // ... but, we write rdi before reading sigsetjmp; avoid collision.
        );

        ret
    }
}

#[cfg(test)]
mod tests {
    // longjmp never returns, and its signature reflects that. But its noisy to
    // be warned about it in the tests below, where the whole point is to ensure
    // that everything *is* skipped in the expected manner.
    #![allow(unreachable_code)]

    use super::*;
    use expect_test::expect;

    #[test]
    fn setjmp_basically_works() {
        assert_eq!(call_with_setjmp(|_env| { 0 }), 0);
        assert_eq!(call_with_setjmp(|_env| { 3 }), 3);
        assert_eq!(
            call_with_setjmp(|env| {
                unsafe {
                    longjmp(env, 4);
                }
                3
            }),
            4
        );
    }

    #[test]
    fn sigsetjmp_basically_works() {
        assert_eq!(call_with_sigsetjmp(true, |_env| { 0 }), 0);
        assert_eq!(call_with_sigsetjmp(true, |_env| { 3 }), 3);
        assert_eq!(
            call_with_sigsetjmp(true, |env| {
                unsafe {
                    siglongjmp(env, 4);
                }
                3
            }),
            4
        );
    }

    #[test]
    fn check_control_flow_details_1() {
        // The basic test template: record control flow points via record, and
        // compare them in the test output.
        let mut record = String::new();
        let result = call_with_setjmp(|env| {
            record.push_str("A");
            unsafe {
                longjmp(env, 4);
            }
            record.push_str(" B");
            0
        });
        assert_eq!(result, 4);
        expect![["A"]].assert_eq(&record);
    }

    #[test]
    fn check_control_flow_details_2() {
        let mut record = String::new();
        let result = call_with_setjmp(|_env1| {
            record.push_str("A");
            let ret = call_with_setjmp(|env2| {
                record.push_str(" B");
                unsafe {
                    longjmp(env2, 4);
                }
                record.push_str(" C");
                0
            });
            record.push_str(" D");
            ret + 1
        });
        assert_eq!(result, 5);
        expect![["A B D"]].assert_eq(&record);
    }

    #[test]
    fn check_control_flow_details_3() {
        let mut record = String::new();
        let result = call_with_setjmp(|env1| {
            record.push_str("A");
            let ret = call_with_setjmp(|_env2| {
                record.push_str(" B");
                unsafe {
                    longjmp(env1, 4);
                }
                record.push_str(" C");
                0
            });
            record.push_str(" D");
            ret + 1
        });
        assert_eq!(result, 4);
        expect![["A B"]].assert_eq(&record);
    }

    #[cfg(feature = "test_c_integration")]
    #[test]
    fn c_integration() {
        extern "C" {
            fn subtract_but_longjmp_if_underflow(env: JmpBuf, a: u32, b: u32) -> u32;
        }
        assert_eq!(
            call_with_setjmp(|env| {
                (unsafe { subtract_but_longjmp_if_underflow(env, 10, 3) }) as c_int
            }),
            7
        );

        assert_eq!(
            call_with_setjmp(|env| {
                unsafe {
                    subtract_but_longjmp_if_underflow(env, 3, 10);
                    panic!("should never get here.");
                }
            }),
            7
        );
    }
}

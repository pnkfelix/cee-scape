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
#![cfg_attr(not(test), no_std)]

use libc::c_int;

#[cfg(target_os = "linux")]
mod glibc_compat;
#[cfg(target_os = "macos")]
mod macos_compat;
#[cfg(target_arch = "riscv64")]
mod riscv64;
#[cfg(target_os = "linux")]
use glibc_compat as struct_defs;
#[cfg(target_os = "macos")]
use macos_compat as struct_defs;

pub use crate::struct_defs::{JmpBufFields, JmpBufStruct};
pub use crate::struct_defs::{SigJmpBufFields, SigJmpBufStruct};

/// This is the type of the first argument that is fed to longjmp.
pub type JmpBuf = *const JmpBufFields;

/// This is the type of the first argument that is fed to siglongjmp.
pub type SigJmpBuf = *const SigJmpBufFields;

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
    ///
    /// FIXME: include safety note here, including the issues with destructors
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
    ///
    /// FIXME: include safety note here, including the issues with destructors
    pub fn siglongjmp(jbuf: SigJmpBuf, val: c_int) -> !;
}

// FIXME: figure out how to access feature cfg'ing. (And then, look into linting
// against people trying to do "the obvious things".)

#[cfg(not(feature = "use_c_to_interface_with_setjmp"))]
mod asm_based;
#[cfg(not(feature = "use_c_to_interface_with_setjmp"))]
pub use asm_based::{call_with_setjmp, call_with_sigsetjmp};

#[cfg(feature = "use_c_to_interface_with_setjmp")]
mod cee_based;
#[cfg(feature = "use_c_to_interface_with_setjmp")]
pub use cee_based::{call_with_setjmp, call_with_sigsetjmp};

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

    #[cfg(feature = "test_c_integration")]
    #[test]
    fn check_c_layout() {
        // This type is defined in test_c_integration
        #[repr(C)]
        #[derive(Copy, Clone, Default, Debug)]
        struct LayoutOfJmpBufs {
            jb_size: usize,
            jb_align: usize,
            sigjb_size: usize,
            sigjb_align: usize,
        }

        extern "C" {
            fn get_c_jmpbuf_layout() -> LayoutOfJmpBufs;
        }

        let cinfo = unsafe { get_c_jmpbuf_layout() };
        // Dump the info so that if the test fails the right values are easy
        // enough to find.
        eprintln!("Note: C jmp_buf/sigjmp_buf layout info: {cinfo:?}");

        assert_eq!(cinfo.jb_size, core::mem::size_of::<JmpBufStruct>());
        assert_eq!(cinfo.jb_align, core::mem::align_of::<JmpBufStruct>());
        assert_eq!(cinfo.sigjb_size, core::mem::size_of::<SigJmpBufStruct>());
        assert_eq!(cinfo.sigjb_align, core::mem::align_of::<SigJmpBufStruct>());
    }
}

#[cfg(test)]
mod tests_of_drop_interaction {
    use super::{call_with_setjmp, call_with_sigsetjmp};
    use std::sync::atomic::{AtomicUsize, Ordering};
    struct IncrementOnDrop(&'static str, &'static AtomicUsize);
    impl IncrementOnDrop {
        fn new(name: &'static str, state: &'static AtomicUsize) -> Self {
            println!("called new for {name}");
            IncrementOnDrop(name, state)
        }
    }
    impl Drop for IncrementOnDrop {
        fn drop(&mut self) {
            println!("called drop on {}", self.0);
            self.1.fetch_add(1, Ordering::Relaxed);
        }
    }

    #[test]
    fn does_ptr_read_cause_a_double_drop_for_setjmp() {
        static STATE: AtomicUsize = AtomicUsize::new(0);
        let iod = IncrementOnDrop::new("iod", &STATE);
        call_with_setjmp(move |_env| {
            println!("at callback 1 start: {}", iod.1.load(Ordering::Relaxed));
            let _own_it = iod;
            0
        });
        println!(
            "callback done, drop counter: {}",
            STATE.load(Ordering::Relaxed)
        );
        assert_eq!(STATE.load(Ordering::Relaxed), 1);
        let iod = IncrementOnDrop::new("iod", &STATE);
        call_with_setjmp(move |_env| {
            println!("at callback 2 start: {}", iod.1.load(Ordering::Relaxed));
            let _own_it = iod;
            0
        });
        println!(
            "callback done, drop counter: {}",
            STATE.load(Ordering::Relaxed)
        );
        assert_eq!(STATE.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn does_ptr_read_cause_a_double_drop_for_sigsetjmp() {
        static STATE: AtomicUsize = AtomicUsize::new(0);
        let iod = IncrementOnDrop::new("iod", &STATE);
        call_with_sigsetjmp(false, move |_env| {
            println!("at callback 3 start: {}", iod.1.load(Ordering::Relaxed));
            let _own_it = iod;
            0
        });
        println!(
            "callback done, drop counter: {}",
            STATE.load(Ordering::Relaxed)
        );
        assert_eq!(STATE.load(Ordering::Relaxed), 1);
        let iod = IncrementOnDrop::new("iod", &STATE);
        call_with_sigsetjmp(true, move |_env| {
            println!("at callback 4 start: {}", iod.1.load(Ordering::Relaxed));
            let _own_it = iod;
            0
        });
        println!(
            "callback done, drop counter: {}",
            STATE.load(Ordering::Relaxed)
        );
        assert_eq!(STATE.load(Ordering::Relaxed), 2);
    }

    // FIXME: This test probably shouldn't be written this way. The intended safety property
    // for calling longjmp is that there *are no* destructors waiting to run between the
    // longjmp and its associated setjmp (and that we otherwise have UB).
    #[test]
    fn mix_drop_with_longjmp() {
        use crate::longjmp;

        static STATE: AtomicUsize = AtomicUsize::new(0);
        // The above cases were checking that "normal" control flow,
        // with no longjmp's involved, would not cause a double-drop.
        // But as soon as longjmp is in the mix, we can no lonbger
        // guarantee that the closure passed into call_with_setjmp will be dropped
        let iod = IncrementOnDrop::new("iod", &STATE);
        call_with_setjmp(move |env1| {
            println!("at callback 1 start: {}", iod.1.load(Ordering::Relaxed));
            let _own_it = iod;
            unsafe { longjmp(env1, 4) }
        });
        println!(
            "callback done, drop counter: {}",
            STATE.load(Ordering::Relaxed)
        );
        assert_eq!(STATE.load(Ordering::Relaxed), 0);
    }
}

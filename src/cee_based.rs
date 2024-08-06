use crate::{JmpBuf, JmpBufFields};
use crate::{SigJmpBuf, SigJmpBufFields};
use libc::{c_int, c_void};

#[link(name = "interop_via_c", kind = "static")]
extern "C" {
    fn call_closure_with_setjmp(
        closure_env_ptr: *mut c_void,
        closure_code: extern "C" fn(jbuf: *const JmpBufFields, env_ptr: *mut c_void) -> c_int,
    ) -> c_int;

    fn call_closure_with_sigsetjmp(
        savemask: c_int,
        closure_env_ptr: *mut c_void,
        closure_code: extern "C" fn(jbuf: *const SigJmpBufFields, env_ptr: *mut c_void) -> c_int,
    ) -> c_int;
}

/// Covers the usual use case for setjmp: it invokes the callback, and the code
/// of the callback can use longjmp to exit early from the call_with_setjmp.
pub fn call_with_setjmp<F>(mut callback: F) -> c_int
where
    F: for<'a> FnOnce(&'a JmpBufFields) -> c_int,
{
    extern "C" fn call_from_c_to_rust<F>(jbuf: JmpBuf, closure_env_ptr: *mut c_void) -> c_int
    where
        F: for<'a> FnOnce(&'a JmpBufFields) -> c_int,
    {
        let closure_env_ptr: *mut F = closure_env_ptr as *mut F;

        // Dereference `closure_env_ptr` with .read() to acquire ownership of
        // the FnOnce object, then call it. (See also the forget note below.)
        //
        // Note that `closure_env_ptr` is not a raw function pointer, it's a
        // pointer to a FnOnce; the code we call comes from the generic `F`.
        unsafe { (closure_env_ptr.read())(&*jbuf) }
    }

    unsafe {
        let closure_env_ptr = core::ptr::addr_of_mut!(callback);

        // The callback is now effectively owned by `closure_env_ptr` (i.e., the
        // `closure_env_ptr.read()` call in `call_from_c_to_rust` will take a
        // direct bitwise copy of its state, and pass that ownership into the
        // FnOnce::call_once invocation.)
        //
        // Therefore, we need to forget about our own ownership of the callback now.
        core::mem::forget(callback);

        call_closure_with_setjmp(closure_env_ptr as *mut c_void, call_from_c_to_rust::<F>)
    }
}

/// TODO
pub fn call_with_sigsetjmp<F>(savemask: bool, mut callback: F) -> c_int
where
    F: for<'a> FnOnce(&'a SigJmpBufFields) -> c_int,
{
    extern "C" fn call_from_c_to_rust<F>(jbuf: SigJmpBuf, closure_env_ptr: *mut c_void) -> c_int
    where
        F: for<'a> FnOnce(&'a SigJmpBufFields) -> c_int,
    {
        let closure_env_ptr: *mut F = closure_env_ptr as *mut F;

        // Dereference `closure_env_ptr` with .read() to acquire ownership of
        // the FnOnce object, then call it. (See also the forget note below.)
        //
        // Note that `closure_env_ptr` is not a raw function pointer, it's a
        // pointer to a FnOnce; the code we call comes from the generic `F`.
        unsafe { (closure_env_ptr.read())(&*jbuf) }
    }

    let savemask: c_int = if savemask { 1 } else { 0 };

    unsafe {
        let closure_env_ptr = core::ptr::addr_of_mut!(callback);

        // The callback is now effectively owned by `closure_env_ptr` (i.e., the
        // `closure_env_ptr.read()` call in `call_from_c_to_rust` will take a
        // direct bitwise copy of its state, and pass that ownership into the
        // FnOnce::call_once invocation.)
        //
        // Therefore, we need to forget about our own ownership of the callback now.
        core::mem::forget(callback);

        call_closure_with_sigsetjmp(
            savemask,
            closure_env_ptr as *mut c_void,
            call_from_c_to_rust::<F>,
        )
    }
}

The cee-scape crate provides Rust access to `setjmp` and `sigsetjmp`
functionality, via an interface that ensures LLVM won't miscompile things.

# Example

You might imagine you have some C code that looks like this (vastly over simplified):

```c
#include <setjmp.h>
#include <stdint.h>

uint32_t subtract_but_longjmp_if_underflow(jmp_buf env, uint32_t a, uint32_t b) {
    if (b > a) {
        longjmp(env, b - a);
    }
    return a - b;
}
```

If you want to call out to that C code from Rust, you need to establish a jump
environment (the `jmp_buf env` parameter); but Rust does not provide `setjmp`.

Here's how you might use this crate to solve your problem:

```rust
use cee_scape::call_with_setjmp;

// This invocation passes parameters that follow normal control flow.
assert_eq!(call_with_setjmp(|env| {
    (unsafe {
        subtract_but_longjmp_if_underflow(env, 10, 3)
    }) as c_int
}), 7);

// This invocation passes parameters that cause a non-local jump.
assert_eq!(call_with_setjmp(|env| {
    unsafe {
        subtract_but_longjmp_if_underflow(env, 3, 10);
        panic!("should never get here.");
    }
}), 7);
```

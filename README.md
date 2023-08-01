# cee-scape

The cee-scape crate provides Rust access to `setjmp` and `sigsetjmp`
functionality, via an interface that ensures LLVM won't miscompile things.

## Example

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

## Why not just add `setjmp` itself as a function?

There has been significant discussion of that question amongst the Rust project.

See in particular [rust-lang/libc PR 1216] and [rust-lang/rfcs Issue 2625].

[rust-lang/libc PR 1216]: https://github.com/rust-lang/libc/pull/1216
[rust-lang/rfcs Issue 2625]: https://github.com/rust-lang/rfcs/issues/2625

The answer is multifaceted.

First, adding support for calling `setjmp` would require adding extra support in
the Rust compiler. Namely, support for marking functions as potentially
returning multiple times, e.g. via a `returns_twice` attribute as discussed in
[rust-lang/rfcs Issue 2625][].

Second, calls to the `setjmp` function would interact in strange ways with the
Rust borrow checker; unless the borrow checker were extended to understand the
meaning of a `returns_twice` attribute, it would invite immediate unsound
behavior, such as moving an owned object multiple times from the same stack
slot. This could cause the same value to be dropped multiple times (which would
be unsound).

Third, the `setjmp` function itself only has well-defined behavior in very
specific contexts according to the C standard (again discussed in
[rust-lang/rfcs Issue 2625]); even just `let x = setjmp(...)` would be undefined
behavior in Rust.

The methods offered by cee-scape, such as `call_with_setjmp`, side-step the above
issues by limiting the use of `setjmp` to a specific coding pattern: 

```rust
call_with_setjmp(|env| { ... })
```

Within the dynamic extent of an invocation to `call_with_setjmp`, one can either
return normally, or via a `longjmp` to the given jump environment `env` (which
causes a returns from the `call_with_setjmp` invocation). Either way, the outer
call returns at most once. The given jump environment is only usable within that
dynamic extent (and Rust's lifetime rules help enforce that constraint).

## Why is it called cee-scape

Its a pun: C's jump environments are also known as "escape continuations". This
crate enables C escapes.

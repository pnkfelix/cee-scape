#include <setjmp.h>
#include <stdint.h>
#include <stddef.h>

uint32_t subtract_but_longjmp_if_underflow(jmp_buf env, uint32_t a, uint32_t b) {
    if (b > a) {
        longjmp(env, b - a);
    }
    return a - b;
}

struct LayoutOfJmpBufs {
    size_t jb_size;
    size_t jb_align;

    size_t sigjb_size;
    size_t sigjb_align;
};

struct LayoutOfJmpBufs get_c_jmpbuf_layout(void) {
    struct LayoutOfJmpBufs info = {0};
    info.jb_size = sizeof(jmp_buf);
    // Hopefully it is fine to use C11's `_Alignof` by now...
    info.jb_align = _Alignof(jmp_buf);
    info.sigjb_size = sizeof(sigjmp_buf);
    info.sigjb_align = _Alignof(sigjmp_buf);
    return info;
}
#include <setjmp.h>
#include <stdint.h>

uint32_t subtract_but_longjmp_if_underflow(jmp_buf env, uint32_t a, uint32_t b) {
    if (b > a) {
        longjmp(env, b - a);
    }
    return a - b;
}

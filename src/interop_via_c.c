#include <setjmp.h>
#include <stdio.h>

int call_closure_with_setjmp(void* closure_env_ptr, int (*closure_code)(jmp_buf jbuf, void *env_ptr)) {
    jmp_buf jbuf;
    int val;
    if (0 == (val = setjmp(jbuf))) {
        return closure_code(jbuf, closure_env_ptr);
    } else {
        return val;
    }
}

int call_closure_with_sigsetjmp(int savemask, void* closure_env_ptr, int (*closure_code)(sigjmp_buf jbuf, void *env_ptr)) {
    sigjmp_buf jbuf;
    int val;
    if (0 == (val = sigsetjmp(jbuf, savemask))) {
        return closure_code(jbuf, closure_env_ptr);
    } else {
        return val;
    }
}

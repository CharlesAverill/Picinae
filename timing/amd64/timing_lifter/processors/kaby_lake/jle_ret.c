#include <stdio.h>
#include <stdint.h>

/* Read timestamp counter */
static inline uint64_t rdtsc(void) {
    unsigned hi, lo;
    __asm__ volatile ("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

/* Prevent compiler from reordering */
#define BARRIER() __asm__ volatile("" ::: "memory")

/* Number of iterations to average */
#define ITERS 1000000000

/* Test: unconditional forward jmp */
uint64_t test_forward_jmp(void) {
    uint64_t start, end;
    start = rdtsc();
    for (int i = 0; i < ITERS; i++) {
        __asm__ volatile (
            "jmp 1f\n\t"
            "nop\n\t"
            "1:\n\t"
        );
    }
    end = rdtsc();
    return (end - start) / ITERS;
}

/* Test: unconditional backward jmp (loop) */
uint64_t test_backward_jmp(void) {
    uint64_t start, end;
    start = rdtsc();
    __asm__ volatile (
        "mov %[iters], %%ecx\n\t"
        "0:\n\t"
        "jmp 1f\n\t"
        "nop\n\t"
        "1:\n\t"
        "loop 0b\n\t"
        :
        : [iters] "r"(ITERS)
        : "ecx"
    );
    end = rdtsc();
    return (end - start) / ITERS;
}

/* Test: indirect jmp via register */
uint64_t test_indirect_jmp(void) {
    uint64_t start, end;
    start = rdtsc();
    for (int i = 0; i < ITERS; i++) {
        __asm__ volatile (
            "lea 1f(%%rip), %%rax\n\t"
            "jmp *%%rax\n\t"
            "1:\n\t"
            :
            :
            : "rax"
        );
    }
    end = rdtsc();
    return (end - start) / ITERS;
}

/* Test: conditional branch (always taken) */
uint64_t test_cond_taken(void) {
    uint64_t start, end;
    start = rdtsc();
    for (int i = 0; i < ITERS; i++) {
        __asm__ volatile (
            "mov $1, %%eax\n\t"
            "cmp $1, %%eax\n\t"
            "jle 1f\n\t"
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax"
        );
    }
    end = rdtsc();
    return (end - start) / ITERS;
}

/* Test: conditional branch (not taken) */
uint64_t test_cond_not_taken(void) {
    uint64_t start, end;
    start = rdtsc();
    for (int i = 0; i < ITERS; i++) {
        __asm__ volatile (
            "mov $1, %%eax\n\t"
            "cmp $2, %%eax\n\t"
            "jle 1f\n\t"
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax"
        );
    }
    end = rdtsc();
    return (end - start) / ITERS;
}


/* Test: ret instruction (balanced call/ret) */
uint64_t test_ret(void) {
    uint64_t start, end;
    start = rdtsc();
    for (int i = 0; i < ITERS; i++) {
        __asm__ volatile (
            "call 1f\n\t"   /* pushes return addr to label 2, jumps to 1 */
            "jmp 2f\n\t"    /* skip the inline ret body */
            "1:\n\t"
            "ret\n\t"       /* returns to label 2 */
            "2:\n\t"
        );
    }
    end = rdtsc();
    return (end - start) / ITERS;
}


uint64_t test_nested_ret(void) {
    uint64_t start, end;
    start = rdtsc();
    for (int i = 0; i < ITERS; i++) {
        __asm__ volatile (
            "call 1f\n\t"   /* outer call -> 1 */
            "jmp 3f\n\t"
            "1:\n\t"
            "call 2f\n\t"   /* inner call -> 2 */
            "ret\n\t"       /* return from inner back to after call 2 */
            "2:\n\t"
            "ret\n\t"       /* return from outer back to after call 1 */
            "3:\n\t"
        );
    }
    end = rdtsc();
    return (end - start) / ITERS;
}



int main(void) {
    printf("jmp forward:        %lu cycles\n", test_forward_jmp());
    printf("jmp backward:       %lu cycles\n", test_backward_jmp());
    printf("jmp indirect:       %lu cycles\n", test_indirect_jmp());
    printf("cond jmp (taken):   %lu cycles\n", test_cond_taken());
    printf("cond jmp (not-taken): %lu cycles\n", test_cond_not_taken());
    printf("ret simple:           %lu cycles\n", test_ret());
    printf("ret nested:           %lu cycles\n", test_nested_ret());
    return 0;
}

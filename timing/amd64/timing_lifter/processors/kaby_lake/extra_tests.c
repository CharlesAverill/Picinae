#include <stdio.h>
#include <stdint.h>
#include <x86intrin.h>
#include <limits.h>

/* Read timestamp counter */
// static inline uint64_t __rdtsc(void) {
//     uint32_t hi, lo;
//     __asm__ volatile ("__rdtsc" : "=a"(lo), "=d"(hi));
//     return ((uint64_t)hi << 32) | lo;
// }

static inline uint64_t rdtsc_serialized(void) {
    unsigned hi, lo;
    asm volatile("cpuid\n\t"
                 "rdtsc\n\t"
                 : "=a"(lo), "=d"(hi)
                 :
                 : "%rbx", "%rcx");
    return ((uint64_t)hi << 32) | lo;
}

/* Prevent compiler from reordering */
#define BARRIER() __asm__ volatile("" ::: "memory")

/* Number of iterations per trial */
#define ITERS 1000000000ULL

/* Number of trials to find worst case */
#define NUM_TRIALS 1

/* Macro to measure worst-case timing */
#define MEASURE_WORST_CASE(code_block) ({ \
    uint64_t worst_time = 0; \
    for (int trial = 0; trial < NUM_TRIALS; trial++) { \
        _mm_lfence(); \
        uint64_t start = rdtsc_serialized(); \
        for (uint64_t i = 0; i < ITERS; i++) { \
            code_block; \
        } \
        uint64_t end = rdtsc_serialized(); \
        _mm_lfence(); \
        uint64_t time = (end - start) / ITERS; \
        if (time > worst_time) worst_time = time; \
    } \
    worst_time; \
})


/* --- Jump / Conditional Branches --- */

/* Test: jz (always taken) */
uint64_t test_jz_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "xor %%eax, %%eax\n\t"   /* sets ZF=1 */
            "jz 1f\n\t"
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax"
        )
    );
}

/* Test: jz (not taken) */
uint64_t test_jz_not_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov $1, %%eax\n\t"      /* sets ZF=0 */
            "jz 1f\n\t"
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax"
        )
    );
}

/* Test: jnz (taken) */
uint64_t test_jnz_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov $1, %%eax\n\t"
            "jnz 1f\n\t"
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax"
        )
    );
}

/* Test: jnz (not taken) */
uint64_t test_jnz_not_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "xor %%eax, %%eax\n\t"
            "jnz 1f\n\t"
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax"
        )
    );
}

/* Test: jnc (carry clear → taken) */
uint64_t test_jnc_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "add $0, %%al\n\t"       /* clear CF */
            "jnc 1f\n\t"
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "al"
        )
    );
}

/* Test: jc (carry set → taken) */
uint64_t test_jc_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "stc\n\t"                /* set carry flag */
            "jc 1f\n\t"
            "nop\n\t"
            "1:\n\t"
        )
    );
}

/* Test: jmp (unconditional) */
uint64_t test_jmp_addr(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "jmp 1f\n\t"
            "nop\n\t"
            "1:\n\t"
        )
    );
}


/* --- ALU and Addressing --- */

/* Test: add r32, m32 (add from memory) */
uint64_t test_add_r32_m32(void) {
    static uint32_t mem = 1;
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "add (%0), %%eax\n\t"
            :
            : "r"(&mem)
            : "eax"
        );
    );
}

/* Test: shr r16, imm8 */
uint64_t test_shr_r16_i(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov $0xFFFF, %%ax\n\t"
            "shr $1, %%ax\n\t"
            :
            :
            : "ax"
        );
    );
}

/* --- LEA tests --- */

/* lea r32, [r32 + disp] */
uint64_t test_lea_r32_addr(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "lea 8(%%ebx), %%ecx\n\t"
            :
            :
            : "ebx", "ecx"
        );
    );
}

/* lea r64, [r64 + r64*4 + disp] */
uint64_t test_lea_r64_addr(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "lea (%%rsi, %%rdi, 4), %%rax\n\t"
            :
            :
            : "rsi", "rdi", "rax"
        );
    );
}


/* --- NOP test --- */
uint64_t test_nop(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile("nop\n\tnop\n\tnop\n\tnop");
    ) / 4;
}

#include <stdint.h>

/* Assume __rdtsc(), BARRIER(), and ITERS are already defined */

/* Test: jge (taken) — eax >= ebx */
uint64_t test_jge_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov $2, %%eax\n\t"
            "mov $1, %%ebx\n\t"
            "cmp %%ebx, %%eax\n\t"  /* sets SF and OF flags for signed compare */
            "jge 1f\n\t"            /* always taken because 2 >= 1 */
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax", "ebx"
        );
    );
}

/* Test: jge (not taken) — eax < ebx */
uint64_t test_jge_not_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov $1, %%eax\n\t"
            "mov $2, %%ebx\n\t"
            "cmp %%ebx, %%eax\n\t"
            "jge 1f\n\t"            /* never taken because 1 < 2 */
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax", "ebx"
        );
    );
}

/* Test: jg (taken) — eax > ebx */
uint64_t test_jg_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov $3, %%eax\n\t"
            "mov $2, %%ebx\n\t"
            "cmp %%ebx, %%eax\n\t"
            "jg 1f\n\t"             /* always taken because 3 > 2 */
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax", "ebx"
        );
    );
}

/* Test: jg (not taken) — eax <= ebx */
uint64_t test_jg_not_taken(void) {
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov $2, %%eax\n\t"
            "mov $2, %%ebx\n\t"
            "cmp %%ebx, %%eax\n\t"
            "jg 1f\n\t"             /* never taken because 2 == 2 */
            "nop\n\t"
            "1:\n\t"
            :
            :
            : "eax", "ebx"
        );
    );
}

/* Test: mov r64, m64 (load from memory) */
uint64_t test_mov_r64_m64(void) {
    static uint64_t mem = 0x123456789ABCDEF0ULL;
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov (%0), %%rax\n\t"
            :
            : "r"(&mem)
            : "rax"
        );
    );
}

/* Test: cmp r64, m64 (compare register with memory) */
uint64_t test_cmp_r64_m64(void) {
    static uint64_t mem = 0x1111111111111111ULL;
    return MEASURE_WORST_CASE(
        __asm__ volatile(
            "mov $0x1111111111111111, %%rax\n\t"
            "cmp (%0), %%rax\n\t"
            :
            : "r"(&mem)
            : "rax"
        );
    );
}

#define MAX(x, y) (x >= y ? x : y)

/* --- MAIN --- */
int main(void) {
    printf("jz:                    %lu cycles\n", MAX(test_jz_taken(), test_jz_not_taken()));
    printf("jnz:           %lu cycles\n", MAX(test_jnz_taken(), test_jnz_not_taken()));
    printf("jnc:           %lu cycles\n", test_jnc_taken());
    printf("jc:            %lu cycles\n", test_jc_taken());
    printf("jge:                   %lu cycles\n", MAX(test_jge_taken(), test_jge_not_taken()));
    printf("jg:                    %lu cycles\n", MAX(test_jg_taken(), test_jg_not_taken()));
    printf("jmp (addr):            %lu cycles\n", test_jmp_addr());
    printf("add r32, m32:          %lu cycles\n", test_add_r32_m32());
    printf("shr r16, imm8:         %lu cycles\n", test_shr_r16_i());
    printf("lea r32, addr:         %lu cycles\n", test_lea_r32_addr());
    printf("lea r64, addr:         %lu cycles\n", test_lea_r64_addr());
    printf("nop:                   %lu cycles\n", test_nop());
    printf("mov r64, m64:          %lu cycles\n", test_mov_r64_m64());
    printf("cmp r64, m64:          %lu cycles\n", test_cmp_r64_m64());
    return 0;
}

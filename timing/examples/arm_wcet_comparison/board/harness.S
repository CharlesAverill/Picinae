/*
 * Cycle-measurement harness for the STM32F072B-DISCO (Cortex-M0).
 *
 * The Cortex-M0 has no DWT cycle counter, so SysTick (24-bit down-counter on
 * the core clock) is the timer. measure_call reads SysTick, calls the target
 * with BLX, and reads SysTick again, so the raw delta is
 *
 *     D(f) = [offset of the 2nd read's sample point] + t(BLX) + T(f)
 *
 * where T(f) is the time from f's first instruction up to and including its
 * return (BX LR / POP {..,PC}), i.e. exactly what time_of_* in the proofs and
 * aiT's "analysis start = f" count.
 *
 * The baseline is the same code with the BLX target set to measure_call_ret,
 * the instruction right after the BLX: then the BLX branches (with the same
 * pipeline refill) straight to the second read, so
 *
 *     D(base) = [same offset] + t(BLX)      and      T(f) = D(f) - D(base)
 *
 * with no assumed instruction timings. The stub_* functions below have known
 * TRM timings and are measured the same way to check this calibration.
 */
    .syntax unified
    .cpu cortex-m0
    .thumb

    .section .text.harness, "ax", %progbits

/*
 * uint32_t measure_call(struct call *c)
 *   struct call { uint32_t fn, r0, r1, r2, r3, ret; }
 * Calls c->fn with r0..r3 = c->r0..c->r3, stores its r0 in c->ret, and
 * returns the raw SysTick delta (24-bit, wraparound-safe).
 */
    .balign 16
    .global measure_call
    .type measure_call, %function
    .thumb_func
measure_call:
    push    {r4-r7, lr}
    movs    r7, r0
    ldr     r4, =0xE000E018         @ SYST_CVR
    ldr     r6, [r7, #0]
    ldr     r0, [r7, #4]
    ldr     r1, [r7, #8]
    ldr     r2, [r7, #12]
    ldr     r3, [r7, #16]
    ldr     r5, [r4]                @ start
    blx     r6
    .global measure_call_ret
measure_call_ret:
    ldr     r1, [r4]                @ end
    str     r0, [r7, #20]
    subs    r0, r5, r1              @ down-counter: start - end
    lsls    r0, r0, #8
    lsrs    r0, r0, #8              @ mod 2^24
    pop     {r4-r7, pc}
    .ltorg
    .size measure_call, . - measure_call

/* ---- calibration stubs (expected cycles from CortexM0NoWait / TRM) ---- */

.macro STUB name
    .balign 4
    .global \name
    .type \name, %function
    .thumb_func
\name:
.endm

STUB stub_bx            @ 3
    bx      lr

STUB stub_nop1          @ 1 + 3
    nop
    bx      lr

STUB stub_nop8          @ 8 + 3
    .rept 8
    nop
    .endr
    bx      lr

STUB stub_ldr           @ 2 + 3   (r0 = address to load)
    ldr     r0, [r0]
    bx      lr

STUB stub_str           @ 2 + 3   (r0 = SRAM address)
    str     r1, [r0]
    bx      lr

STUB stub_ldm1          @ (1+1) + 3
    ldm     r0!, {r1}
    bx      lr

STUB stub_ldr_pc        @ 2 + 3
    ldr     r0, =0x12345678
    bx      lr
    .ltorg

STUB stub_muls          @ 1 + 3
    muls    r0, r1, r0
    bx      lr

STUB stub_uxth          @ 1 + 3
    uxth    r0, r0
    bx      lr

STUB stub_b             @ 3 + 3
    b       1f
1:  bx      lr

STUB stub_beq_taken     @ 1 + 3 + 3
    cmp     r0, r0
    beq     1f
1:  bx      lr

STUB stub_beq_not_taken @ 1 + 1 + 3   (r0 = 0)
    cmp     r0, #1
    beq     1f
1:  bx      lr

STUB stub_push_pop2     @ (1+2) + (4+2)
    push    {r4, lr}
    pop     {r4, pc}

STUB stub_push_pop3     @ (1+3) + (4+3)
    push    {r4, r5, lr}
    pop     {r4, r5, pc}

STUB stub_bl            @ (1+1) + 4 + 3 + (4+1)
    push    {lr}
    bl      stub_bx
    pop     {pc}

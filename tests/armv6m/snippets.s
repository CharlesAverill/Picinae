.syntax unified
.cpu cortex-m0
.thumb
.section .text
.global fixture
.type fixture, %function
.thumb_func
fixture:
    push {r4, lr}
    ldr r4, .Lliteral
    movs r0, #255
    adds r0, #1
    cmp r0, #0
    bl helper
    pop {r4, pc}
.size fixture, .-fixture
/* Deliberately outside the function symbol's size. */
.balign 4
.Lliteral:
    .word 0x1234abcd
.global helper
.type helper, %function
.thumb_func
helper:
    movs r1, #1
    bx lr
.size helper, .-helper
.global flag_cases
.type flag_cases, %function
.thumb_func
flag_cases:
    adds r0, r0, r1
    subs r0, r0, r1
    adcs r0, r1
    sbcs r0, r1
    lsls r0, r1
    lsrs r0, r1
    asrs r0, r1
    rors r0, r1
    bl helper  /* backward BL */
    bx lr
.size flag_cases, .-flag_cases

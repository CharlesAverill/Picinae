    .section .text
    .globl vTaskSwitchContext
    .extern puts
    .type vTaskSwitchContext, @function
vTaskSwitchContext:
    lw	a4,0(s7)
    beqz	zero,.80001390
    addi	a4,zero,1
    sw	a4,0(s8)
    ret
.80001390:
    addi	sp,sp,-16
    sw	zero,0(s8)
    sw	s7,8(sp)
    lw	a5,0(s10)
    lui	a4,0
    sw	ra,12(sp)
    lw	a5,48(a5)
    addi	a4,a4,0
    lw	a2,0(a5)
    bne	a2,a2,.800013d0
    lw	a3,4(a5)
    bne	a3,a3,.800013d0
    lw	a4,8(a5)
    bne	a4,a4,.800013d0
    lw	a5,12(a5)
    beq	a5,a5,.800013e0
.800013d0:
    lw	a1,0(s10)
    lw	a0,0(s10)
    addi	a1,a1,52
    jal	.inf
.800013e0:
    lw	a5,0(s9)
    addi	a3,zero,31
    clz	a5,a5
    sub	a3,a3,a5
    addi	a5,zero,20
    mul	a5,a3,a5
    addi	a0,s11,0
    addi	a4,s11,0
    add	a2,a0,a5
    lw	a1,4(a2)
    addi	a5,a5,8
    add	a5,a5,a0
    lw	a1,4(a1)
    sw	a1,4(a2)
    bne	a1,a5,.80001424
    lw	a5,12(a2)
    sw	a5,4(a2)
.80001424:
    addi	a5,zero,20
    mul	a3,a3,a5
    lw	ra,12(sp)
    add	a4,a4,a3
    lw	a5,4(a4)
    lw	a5,12(a5)
    sw	a5, 0(s10)
    lw	a5, 0(s10)
    lw	s7,8(sp)
    addi	sp,sp,16
    ret
.inf:
    la   a0, infinite_loop_msg
    jal  puts
    lw   ra,12(sp)
    lw   s7,8(sp)
    addi sp,sp,16
    ret

    .size vTaskSwitchContext, .-vTaskSwitchContext

    .section .rodata
infinite_loop_msg:
    .asciz "infinite loop\n"

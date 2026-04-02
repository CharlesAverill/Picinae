    .section .text
    .globl vTaskSwitchContext
    .type vTaskSwitchContext, @function

vTaskSwitchContext:
    lw      a4, -1952(gp)              # 80080060 <uxSchedulerSuspended>
    beqz    a4, .Lnot_suspended
    li      a4, 1
    sw      a4, -1932(gp)              # 80080074 <xYieldPendings>
    ret

.Lnot_suspended:
    addi    sp, sp, -16
    sw      zero, -1932(gp)            # 80080074 <xYieldPendings>
    sw      s0, 8(sp)
    lw      a5, -1896(gp)              # 80080098 <pxCurrentTCB>
    lui     a4, 0xa5a5a
    sw      ra, 12(sp)
    lw      a5, 48(a5)
    addi    a4, a4, 1445               # a5a5a5a5
    lw      a2, 0(a5)
    bne     a2, a4, .Lstack_overflow
    lw      a3, 4(a5)
    bne     a3, a2, .Lstack_overflow
    lw      a4, 8(a5)
    bne     a4, a3, .Lstack_overflow
    lw      a5, 12(a5)
    beq     a5, a4, .Lstack_ok

.Lstack_overflow:
    lw      a1, -1896(gp)              # 80080098 <pxCurrentTCB>
    lw      a0, -1896(gp)              # 80080098 <pxCurrentTCB>
    addi    a1, a1, 52
    jal     ra, vApplicationStackOverflowHook
    # fall through

.Lstack_ok:
    lw      a5, -1920(gp)              # 80080080 <uxTopReadyPriority>
    li      a3, 31
    clz     a5, a5
    sub     a3, a3, a5
    li      a5, 20
    mul     a5, a3, a5
    addi    a0, gp, -924               # 80080464 <pxReadyTasksLists>
    addi    a4, gp, -924               # 80080464 <pxReadyTasksLists>
    add     a2, a0, a5
    lw      a1, 4(a2)
    addi    a5, a5, 8
    add     a5, a5, a0
    lw      a1, 4(a1)
    sw      a1, 4(a2)
    bne     a1, a5, .Lno_reset
    lw      a5, 12(a2)
    sw      a5, 4(a2)

.Lno_reset:
    li      a5, 20
    mul     a3, a3, a5
    lw      ra, 12(sp)
    add     a4, a4, a3
    lw      a5, 4(a4)
    lw      a5, 12(a5)
    sw      a5, -1896(gp)              # 80080098 <pxCurrentTCB>
    lw      a5, -1896(gp)              # 80080098 <pxCurrentTCB>
    lw      s0, 8(sp)
    addi    sp, sp, 16
    ret

    .size vTaskSwitchContext, .-vTaskSwitchContext


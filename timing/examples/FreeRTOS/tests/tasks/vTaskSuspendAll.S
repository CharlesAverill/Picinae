    .section .text
    .globl vTaskSuspendAll
    .type vTaskSuspendAll, @function

vTaskSuspendAll:
    lw      a5, -1952(gp)              # 80080060 <uxSchedulerSuspended>
    addi    a5, a5, 1
    sw      a5, -1952(gp)              # 80080060 <uxSchedulerSuspended>
    ret

    .size vTaskSuspendAll, .-vTaskSuspendAll


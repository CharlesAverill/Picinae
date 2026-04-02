    .section .text
    .globl vListInsertEnd
    .type vListInsertEnd, @function

vListInsertEnd:
    lw      a5, 4(a0)
    lw      a4, 8(a5)
    sw      a5, 4(a1)
    sw      a4, 8(a1)
    sw      a1, 4(a4)
    sw      a1, 8(a5)
    lw      a5, 0(a0)
    sw      a0, 16(a1)
    addi    a5, a5, 1
    sw      a5, 0(a0)
    ret

    .size vListInsertEnd, .-vListInsertEnd


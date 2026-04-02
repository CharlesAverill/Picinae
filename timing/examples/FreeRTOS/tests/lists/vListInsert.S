    .section .text
    .globl vListInsert
    .type vListInsert, @function

vListInsert:
	lw a3, 0(a1)
	li a5, -1
	addi a4, a0, 8
	bne a3, a5, .L2
	lw a5, 16(a0)
.L1:
	lw a4, 4(a5)
	sw a4, 4(a1)
	sw a1, 8(a4)
	sw a5, 8(a1)
	sw a1, 4(a5)
	lw a5, 0(a0)
	sw a0, 16(a1)
	addi a5, a5, 1
	sw a5, 0(a0)
	ret
.L2:
	mv a5, a4
	lw a4, 4(a4)
	lw a2, 0(a4)
	bgeu a3, a2, .L2
	j .L1

    .size vListInsert, .-vListInsert


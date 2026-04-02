    .section .text
    .globl uxListRemove
    .type uxListRemove, @function

uxListRemove:
	lw a3, 4(a0)
	lw a4, 8(a0)
	lw a5, 16(a0)
	sw a4, 8(a3)
	sw a3, 4(a4)
	lw a3, 4(a5)
	bne a3, a0, .L1
	sw a4, 4(a5)
.L1:
	sw zero, 16(a0)
	lw a0, 0(a5)
	addi a0, a0, -1
	sw a0, 0(a5)
	ret

	.size uxListRemove, .-uxListRemove


    .section .text
    .globl vListInitialise
    .type vListInitialise, @function

vListInitialise:
	addi a5, a0, 8
	li a4, -1
	sw a5, 4(a0)
	sw a5, 8(a0)
	sw a5, 12(a0)
	sw a5, 16(a0)
	sw zero, 0(a0)
	ret

	.size vListInitialise, .-vListInitialise


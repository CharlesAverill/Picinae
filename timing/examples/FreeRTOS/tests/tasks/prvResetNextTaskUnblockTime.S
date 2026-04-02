    .section .text
    .globl prvResetNextTaskUnblockTime
    .type prvResetNextTaskUnblockTime, @function

prvResetNextTaskUnblockTime:
	lw a5, -1900(gp)
	lw a3, 0(a5)
	bnez a3, L2
	li a4, -1
.L1:
	sw a4, -1944(gp)
	ret
.L2:
	lw a4, -1900(gp)
	lw a4, 12(a4)
	lw a4, 0(a4)
	j L1

	.size prvResetNextTaskUnblockTime, .-prvResetNextTaskUnblockTime


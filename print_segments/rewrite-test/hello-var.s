.text
	.global _start

_start:
	la a1, str

	add a0, x0, a1
getlen_loop:
	lbu a2, 0(a0)
	beq a2, x0, getlen_loop_exit
	addi a0, a0, 1
	j getlen_loop
getlen_loop_exit:
	sub a2, a0, a1

	addi a0, x0, 1		# fd
	la a1, str		# buf
	# len already in a2
	addi a7, x0, 64		# write syscall
	ecall

	addi a0, x0, 0		# return value
	addi a7, x0, 93		# exit syscall
	ecall

.data
str:	.asciz "Hello, World!\n"

.text
	.global _start

_start:
	addi a0, x0, 1		# fd
	la a1, str		# buf
	addi a2, x0, 2047	# len
	add a2, a2, a2
	addi a7, x0, 64		# write syscall
	ecall

	addi a0, x0, 0		# return value
	addi a7, x0, 93		# exit syscall
	ecall

.data
str:	.asciz "Hello, World!\n"

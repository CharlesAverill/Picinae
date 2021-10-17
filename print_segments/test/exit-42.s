.text
	.global _start

_start:
	addi a0, x0, 42		# return value
	addi a7, x0, 93		# exit syscall
	ecall

.data
str:	.asciz "Hello, World!\n"

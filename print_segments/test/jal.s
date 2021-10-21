.text
	.global _start

_start:
  jal t0, _a

  # writing
	addi a0, x0, 1		# fd
	la a1, str		# buf
	addi a2, x0, 14		# len
	addi a7, x0, 64		# write syscall
	ecall
_tmp:
  jr ra

_a:
  jal t1, _b

  # exiting
	addi a0, x0, 0		# return value
	addi a7, x0, 93		# exit syscall
	ecall
_b:
  jalr ra, t0
  jal ra, _tmp
  jalr ra, t1
  nop



.data
str:	.asciz "Hello, World!\n"

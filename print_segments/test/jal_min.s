.text
	.global _start

_start:
  jal ra, _tmp
  jal ra, _tmp

  # exiting
	addi a0, x0, 0		# return value
	addi a7, x0, 93		# exit syscall
	ecall

_tmp:
  jr ra

.text
  .global _start

_start:

  # Write error message
  addi a0, x0, 1   # fd
  auipc a1, 0
_pc:
  addi a1, a1, (14 * 4) # buf (.Lstr-_pc+1)
  addi a2, x0, 24  # len; (.Lstr_end - .Lstr)
  addi a7, x0, 64
  ecall

  # Get current PID
  addi a7, x0, 172
  ecall

  # kill(getpid(), SIGABRT)
  addi a1, x0, 6    # SIGABRT
  addi a7, x0, 129
  ecall

  # exit(-1)
  addi a0, x0, -1   # exit code
  addi a7, x0, 93
  ecall

loop:
  j loop

.Lstr:  .asciz "**CFI policy violation!\n"
.Lstr_end:

	.arch armv8-a
	.file	"nops.S"
	.text

	.align	2
	.global	tiny_nop
	.type	tiny_nop, %function
tiny_nop:
	ret
	.size	tiny_nop, .-tiny_nop

	.align	2
	.global	short_nop
	.type	short_nop, %function
short_nop:
	mov x0, x0
  mov x0, x0
  mov x0, x0
  mov x0, x0
	ret
	.size	short_nop, .-short_nop

	.align	2
	.global	branch_nop
	.type	branch_nop, %function
branch_nop:
  mov x0, x0
  cmp x0, 0
  bne .L1
  mov x0, x0
  mov x0, x0
.L1:
	ret
	.size	branch_nop, .-branch_nop

	.align	2
	.global	loop_nop
	.type	loop_nop, %function
loop_nop:
	cmp	x0, 0
	beq	.L3
  sub x0, x0, #1
	b loop_nop
.L3:
	ret
	.size	loop_nop, .-loop_nop

	.align	2
	.global	rec_nop
	.type	rec_nop, %function
rec_nop:
  sub sp, sp, #8
  str x30, [sp]
	cmp	x0, 0
	beq	.L2
  sub x0, x0, #1
	bl	rec_nop
.L2:
  ldr x30, [sp]
  add sp, sp, #8
	ret
	.size	rec_nop, .-rec_nop

	.align	2
	.global	clobber_ret
	.type	clobber_ret, %function
clobber_ret:
  ldr x0, [sp]
  str x0, [sp]
  ret
	.size	clobber_ret, .-clobber_ret

	.align	2
	.global	faith_ret
	.type	faith_ret, %function
faith_ret:
  mov x30, x0
	ret
	.size	faith_ret, .-faith_ret

  .align 2
  .global tail_nop
  .type tail_nop, %function
tail_nop:
  mov x0, x0
  b short_nop
  .size tail_nop, .-tail_nop

	.align	2
  .global call_test
  .type call_test, %function
call_test:
  mov x0, x0
  bl tiny_nop
  mov x0, x0
  bl short_nop
  mov x0, x0
  bl branch_nop
  mov x0, x0
  bl loop_nop
  mov x0, x0
  bl rec_nop
  mov x0, x0
  bl tail_nop
  mov x0, x0
  bl clobber_ret
  mov x0, x0
  adr x0, .HOPE
  bl faith_ret
.HOPE:
  mov x0, x0
  ret
	.size	call_test, .-call_test

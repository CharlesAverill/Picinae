	.file	"tmr.c"
	.option nopic
	.attribute arch, "rv32i2p1_m2p0_f2p2_d2p2_zicsr2p0_zmmul1p0"
	.attribute unaligned_access, 0
	.attribute stack_align, 16
	.text
	.align	2
	.globl	check_password_tmr
	.type	check_password_tmr, @function
check_password_tmr:
	beq	a2,zero,.L6
	mv	a5,a0
	mv	a6,a1
	add	a2,a0,a2
	mv	a7,a1
	mv	a4,a0
	li	t1,0
.L3:
	lbu	t3,0(a4)
	lbu	a3,0(a7)
	xor	a3,a3,t3
	or	t1,t1,a3
	addi	a4,a4,1
	addi	a7,a7,1
	bne	a4,a2,.L3
	li	a3,0
.L4:
	lbu	a7,0(a0)
	lbu	a4,0(a1)
	xor	a4,a4,a7
	or	a3,a3,a4
	addi	a0,a0,1
	addi	a1,a1,1
	bne	a0,a2,.L4
	li	a1,0
.L5:
	lbu	a0,0(a5)
	lbu	a4,0(a6)
	xor	a4,a4,a0
	or	a1,a1,a4
	addi	a5,a5,1
	addi	a6,a6,1
	bne	a5,a2,.L5
.L2:
	or	a5,a3,a1
	and	a0,t1,a5
	and	a3,a3,a1
	or	a0,a0,a3
	snez	a0,a0
	ret
.L6:
	li	t1,0
	li	a3,0
	li	a1,0
	j	.L2
	.size	check_password_tmr, .-check_password_tmr
	.ident	"GCC: (g1b306039a) 15.1.0"
	.section	.note.GNU-stack,"",@progbits

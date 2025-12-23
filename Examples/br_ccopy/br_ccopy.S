	.file	"br_ccopy.c"
	.option nopic
	.attribute arch, "rv32i2p1_m2p0_f2p2_d2p2_zicsr2p0_zmmul1p0"
	.attribute unaligned_access, 0
	.attribute stack_align, 16
	.text
	.align	2
	.globl	br_ccopy
	.type	br_ccopy, @function
br_ccopy:
	neg	a0,a0
	add	a6,a1,a3
	beq	a3,zero,.L1
.L3:
	lbu	a4,0(a1)
	lbu	a5,0(a2)
	addi	a1,a1,1
	addi	a2,a2,1
	xor	a5,a4,a5
	and	a5,a5,a0
	xor	a5,a5,a4
	sb	a5,-1(a1)
	bne	a1,a6,.L3
.L1:
	ret
	.size	br_ccopy, .-br_ccopy
	.ident	"GCC: (g1b306039a) 15.1.0"
	.section	.note.GNU-stack,"",@progbits

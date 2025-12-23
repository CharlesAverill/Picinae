	.file	"memcmp.c"
	.option nopic
	.attribute arch, "rv32i2p1_m2p0_f2p2_d2p2_zicsr2p0_zmmul1p0"
	.attribute unaligned_access, 0
	.attribute stack_align, 16
	.text
	.align	2
	.globl	CRYPTO_memcmp
	.type	CRYPTO_memcmp, @function
CRYPTO_memcmp:
	beq	a2,zero,.L4
	beq	a2,zero,.L4
	mv	a5,a0
	mv	a5,a0
	add t0,a0,a2
	add t0,a0,a2
	mv  a2, t0
	mv  a2, t0
	li	a0,0
	li  a0,0
.L3:
	lbu	a3,0(a5)
	lbu	a3,0(a5)
	lbu	a4,0(a1)
	lbu	a4,0(a1)
	xor	t0,a4,a3
	xor	t0,a4,a3
	mv 	a4, t0
	mv 	a4, t0
	or	t0,a0,a4
	or	t0,a0,a4
	mv 	a0, t0
	mv 	a0, t0
	addi	t0,a5,1
	addi	t0,a5,1
	mv	a5, t0
	mv	a5, t0
	addi	t0,a1,1
	addi	t0,a1,1
	mv	a1,t0
	mv	a1,t0
	bne	a5,a2,.L3
	bne	a5,a2,.L3
	ret
	ret
.L4:
	li	a0,0
	li	a0,0
	ret
	ret
	.size	CRYPTO_memcmp, .-CRYPTO_memcmp
	.ident	"GCC: (g1b306039a) 15.1.0"
	.section	.note.GNU-stack,"",@progbits

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
	mv	a5,a0
	add	a2,a0,a2
	li	a0,0
.L3:
	lbu	a3,0(a5)
	lbu	a4,0(a1)
	xor	a4,a4,a3
	or	a0,a0,a4
	addi	a5,a5,1
	addi	a1,a1,1
	bne	a5,a2,.L3
	ret
.L4:
	li	a0,0
	ret
	.size	CRYPTO_memcmp, .-CRYPTO_memcmp
	.ident	"GCC: (g1b306039a) 15.1.0"
	.section	.note.GNU-stack,"",@progbits

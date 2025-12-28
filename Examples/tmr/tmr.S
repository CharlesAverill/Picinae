	.file	"tmr.c"
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
	.align	2
	.globl	passwords_match_tmr
	.type	passwords_match_tmr, @function
passwords_match_tmr:
	addi	sp,sp,-32
	sw	ra,28(sp)
	sw	s0,24(sp)
	sw	s1,20(sp)
	sw	s2,16(sp)
	sw	s3,12(sp)
	sw	s4,8(sp)
	mv	s0,a0
	mv	s1,a1
	mv	s2,a2
	call	CRYPTO_memcmp
	mv	s3,a0
	mv	a2,s2
	mv	a1,s1
	mv	a0,s0
	call	CRYPTO_memcmp
	mv	s4,a0
	mv	a2,s2
	mv	a1,s1
	mv	a0,s0
	call	CRYPTO_memcmp
	snez	a5,s3
	snez	a4,s4
	add	a5,a5,a4
	snez	a0,a0
	add	a0,a5,a0
	sltiu	a0,a0,2
	lw	ra,28(sp)
	lw	s0,24(sp)
	lw	s1,20(sp)
	lw	s2,16(sp)
	lw	s3,12(sp)
	lw	s4,8(sp)
	addi	sp,sp,32
	jr	ra
	.size	passwords_match_tmr, .-passwords_match_tmr
	.align	2
	.globl	main
	.type	main, @function
main:
	li	a0,0
	ret
	.size	main, .-main
	.ident	"GCC: (g1b306039a) 15.1.0"
	.section	.note.GNU-stack,"",@progbits

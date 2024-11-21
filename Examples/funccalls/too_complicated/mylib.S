	.arch armv8-a
	.file	"mylib.c"
	.text
	.align	2
	.global	my_add
	.type	my_add, %function
my_add:
	sub	sp, sp, #16
	str	w0, [sp, 12]
	str	w1, [sp, 8]
	b	.L2
.L3:
	ldr	w0, [sp, 12]
	sub	w0, w0, #1
	str	w0, [sp, 12]
	ldr	w0, [sp, 8]
	add	w0, w0, 1
	str	w0, [sp, 8]
.L2:
	ldr	w0, [sp, 12]
	cmp	w0, 0
	bne	.L3
	ldr	w0, [sp, 8]
	add	sp, sp, 16
	ret
	.size	my_add, .-my_add
	.align	2
	.global	my_id
	.type	my_id, %function
my_id:
	stp	x29, x30, [sp, -32]!
	mov	x29, sp
	str	w0, [sp, 28]
	mov	w1, 0
	ldr	w0, [sp, 28]
	bl	my_add
	ldp	x29, x30, [sp], 32
	ret
	.size	my_id, .-my_id
	.align	2
	.global	my_add_rec
	.type	my_add_rec, %function
my_add_rec:
	stp	x29, x30, [sp, -32]!
	mov	x29, sp
	str	w0, [sp, 28]
	str	w1, [sp, 24]
	ldr	w0, [sp, 28]
	cmp	w0, 0
	bne	.L8
	ldr	w0, [sp, 24]
	b	.L9
.L8:
	ldr	w0, [sp, 28]
	sub	w2, w0, #1
	ldr	w0, [sp, 24]
	add	w0, w0, 1
	mov	w1, w0
	mov	w0, w2
	bl	my_add_rec
.L9:
	ldp	x29, x30, [sp], 32
	ret
	.size	my_add_rec, .-my_add_rec
	.align	2
	.global	my_add_rec3
	.type	my_add_rec3, %function
my_add_rec3:
	stp	x29, x30, [sp, -32]!
	mov	x29, sp
	str	w0, [sp, 28]
	str	w1, [sp, 24]
	ldr	w0, [sp, 28]
	cmp	w0, 0
	bne	.L11
	ldr	w0, [sp, 24]
	b	.L12
.L11:
	ldr	w0, [sp, 28]
	cmp	w0, 2
	bls	.L13
	ldr	w0, [sp, 28]
	sub	w2, w0, #3
	ldr	w0, [sp, 24]
	add	w0, w0, 3
	mov	w1, w0
	mov	w0, w2
	bl	my_add_rec3
	b	.L12
.L13:
	ldr	w0, [sp, 28]
	sub	w2, w0, #1
	ldr	w0, [sp, 24]
	add	w0, w0, 1
	mov	w1, w0
	mov	w0, w2
	bl	my_add_rec3
.L12:
	ldp	x29, x30, [sp], 32
	ret
	.size	my_add_rec3, .-my_add_rec3
	.align	2
	.global	my_add_ptr
	.type	my_add_ptr, %function
my_add_ptr:
	sub	sp, sp, #16
	str	w0, [sp, 12]
	str	x1, [sp]
	ldr	x0, [sp]
	ldr	w1, [x0]
	ldr	w0, [sp, 12]
	add	w1, w1, w0
	ldr	x0, [sp]
	str	w1, [x0]
	nop
	add	sp, sp, 16
	ret
	.size	my_add_ptr, .-my_add_ptr
	.align	2
	.global	factorial
	.type	factorial, %function
factorial:
	sub	sp, sp, #32
	str	w0, [sp, 12]
	mov	w0, 1
	str	w0, [sp, 28]
	mov	w0, 1
	str	w0, [sp, 24]
	b	.L16
.L17:
	ldr	w0, [sp, 24]
	ldr	w1, [sp, 28]
	mul	w0, w1, w0
	str	w0, [sp, 28]
	ldr	w0, [sp, 24]
	add	w0, w0, 1
	str	w0, [sp, 24]
.L16:
	ldr	w0, [sp, 24]
	ldr	w1, [sp, 12]
	cmp	w1, w0
	bcs	.L17
	ldr	w0, [sp, 28]
	add	sp, sp, 32
	ret
	.size	factorial, .-factorial
	.align	2
	.global	recfactorial
	.type	recfactorial, %function
recfactorial:
	stp	x29, x30, [sp, -32]!
	mov	x29, sp
	str	w0, [sp, 28]
	ldr	w0, [sp, 28]
	cmp	w0, 1
	bhi	.L20
	mov	w0, 1
	b	.L21
.L20:
	ldr	w0, [sp, 28]
	sub	w0, w0, #1
	bl	recfactorial
	mov	w1, w0
	ldr	w0, [sp, 28]
	mul	w0, w1, w0
.L21:
	ldp	x29, x30, [sp], 32
	ret
	.size	recfactorial, .-recfactorial
	.align	2
	.global	factorial_rec_acc_impl
	.type	factorial_rec_acc_impl, %function
factorial_rec_acc_impl:
	stp	x29, x30, [sp, -32]!
	mov	x29, sp
	str	w0, [sp, 28]
	str	w1, [sp, 24]
	ldr	w0, [sp, 28]
	cmp	w0, 1
	bhi	.L23
	ldr	w0, [sp, 24]
	b	.L24
.L23:
	ldr	w0, [sp, 28]
	sub	w2, w0, #1
	ldr	w1, [sp, 24]
	ldr	w0, [sp, 28]
	mul	w0, w1, w0
	mov	w1, w0
	mov	w0, w2
	bl	factorial_rec_acc_impl
.L24:
	ldp	x29, x30, [sp], 32
	ret
	.size	factorial_rec_acc_impl, .-factorial_rec_acc_impl
	.align	2
	.global	factorial_rec_acc
	.type	factorial_rec_acc, %function
factorial_rec_acc:
	stp	x29, x30, [sp, -32]!
	mov	x29, sp
	str	w0, [sp, 28]
	mov	w1, 1
	ldr	w0, [sp, 28]
	bl	factorial_rec_acc_impl
	ldp	x29, x30, [sp], 32
	ret
	.size	factorial_rec_acc, .-factorial_rec_acc
	.ident	"GCC: (Arm GNU Toolchain 13.3.Rel1 (Build arm-13.24)) 13.3.1 20240614"

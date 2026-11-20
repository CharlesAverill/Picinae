.text
.macro begin name
.globl \name
.type \name,@function
\name:
.endm
.macro end name
ret
.size \name,.-\name
.endm
begin legacy
movdqu (%rsi),%xmm0
movdqu %xmm0,(%rdi)
movdqu %xmm0,%xmm1
movdqu %xmm1,%xmm1
movdqa -16(%rsi,%rcx,2),%xmm9
movdqa %xmm9,16(%rdi)
movdqa %xmm9,%xmm8
movups (%rsi),%xmm2
movups %xmm2,(%rdi)
movups %xmm2,%xmm3
movups %xmm2,%xmm2
movaps (%rsi),%xmm4
movaps %xmm4,(%rdi)
movaps %xmm4,%xmm5
movaps %xmm4,%xmm4
movntdq %xmm5,(%rdi)
# SIB without a base, RIP-relative, high base/index and reverse-register opcode.
movdqu 0x1000(,%rcx,4),%xmm15
movdqu data(%rip),%xmm14
movdqu -4096(%r13,%r12,8),%xmm13
.byte 0xf3,0x0f,0x7f,0xc1
end legacy
begin vex128
vmovdqu (%rsi),%xmm0
vmovdqu %xmm0,(%rdi)
vmovdqu %xmm0,%xmm1
vmovdqu %xmm1,%xmm1
vmovdqa -16(%rsi,%rcx,2),%xmm9
vmovdqa %xmm9,16(%rdi)
vmovdqa %xmm9,%xmm8
vmovups (%rsi),%xmm2
vmovups %xmm2,(%rdi)
vmovups %xmm2,%xmm3
vmovaps (%rsi),%xmm4
vmovaps %xmm4,(%rdi)
vmovaps %xmm4,%xmm5
vmovntdq %xmm5,(%rdi)
vmovdqu -4096(%r13,%r12,8),%xmm15
.byte 0xc5,0xfa,0x7f,0xc1
end vex128
begin vex256
vmovdqu (%rsi),%ymm0
vmovdqu %ymm0,(%rdi)
vmovdqu %ymm0,%ymm1
vmovdqu %ymm1,%ymm1
vmovdqa -32(%rsi,%rcx,2),%ymm9
vmovdqa %ymm9,32(%rdi)
vmovdqa %ymm9,%ymm8
vmovups (%rsi),%ymm2
vmovups %ymm2,(%rdi)
vmovups %ymm2,%ymm3
vmovaps (%rsi),%ymm4
vmovaps %ymm4,(%rdi)
vmovaps %ymm4,%ymm5
vmovntdq %ymm5,(%rdi)
end vex256
begin zero
vzeroupper
end zero
begin rejected
pshufb %xmm0,%xmm1
end rejected
begin rejected_evex
vmovdqu64 (%rsi),%ymm0{%k1}
vmovups (%rsi),%zmm0
end rejected_evex
.data
.p2align 4
data:
.zero 16
.section .note.GNU-stack,"",@progbits

.text
.globl mixed
.type mixed,@function
mixed:
 endbr64
 movdqu (%rsi),%xmm0
 movups %xmm0,%xmm0
 vmovdqu %xmm0,%xmm0
 vmovdqu %ymm0,%ymm1
 mov %rdx,%rcx
 rep movsb
 bsf %rdi,%rdi
 jz .Lzero
 tzcnt %rsi,%rsi
 lzcnt %rdi,%rdi
 jmp .Lexit
.Lzero:
 mov %rdx,%rcx
 rep stosq
 bsr %rdi,%rdi
.Lexit:
 vzeroupper
 ret
.size mixed,.-mixed
.globl rejected
.type rejected,@function
rejected:
 movdqu (%rsi),%xmm0
 rep movsb
 pshufb %xmm0,%xmm1
 ret
.size rejected,.-rejected
.section .note.GNU-stack,"",@progbits

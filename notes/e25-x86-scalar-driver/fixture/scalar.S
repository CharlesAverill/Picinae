/* Synthetic tests, assembled locally; never a glibc substitute. */
.text
.globl scalar_caller
.type scalar_caller,@function
scalar_caller:
  call scalar_callee
  ret
.size scalar_caller,.-scalar_caller
.globl scalar_callee
.hidden scalar_callee
.type scalar_callee,@function
scalar_callee:
  mov %rdi,%rax
  mov $0xab,%ah
  mov $0x1234,%ax
  mov $0x89abcdef,%eax
  mov %rax,(%rsi)
  add $1,%al
  sub $1,%ax
  mov (%rsi),%rdx
  mov scalar_data(%rip),%rcx
  cmp %rcx,%rdx
  je 1f
  neg %rdx
1:
  ret
.size scalar_callee,.-scalar_callee
.globl unsupported_vector
.type unsupported_vector,@function
unsupported_vector:
  pxor %xmm0,%xmm0
  ret
.size unsupported_vector,.-unsupported_vector
.globl unsupported_indirect
.type unsupported_indirect,@function
unsupported_indirect:
  call *%rax
  ret
.size unsupported_indirect,.-unsupported_indirect
.globl unsupported_rep
.type unsupported_rep,@function
unsupported_rep:
  rep movsb
  ret
.size unsupported_rep,.-unsupported_rep
.data
.hidden scalar_data
scalar_data: .quad 0x1122334455667788
.section .note.GNU-stack,"",@progbits

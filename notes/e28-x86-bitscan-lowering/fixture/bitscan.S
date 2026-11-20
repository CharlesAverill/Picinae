/* Synthetic register bit-scan fixtures; never glibc. */
.text
.globl bsf32
.type bsf32,@function
bsf32:
  bsf %r9d,%r10d
  ret
.size bsf32,.-bsf32
.globl bsf32_alias
.type bsf32_alias,@function
bsf32_alias:
  bsf %r9d,%r9d
  ret
.size bsf32_alias,.-bsf32_alias
.globl bsf64
.type bsf64,@function
bsf64:
  bsf %r9,%r10
  ret
.size bsf64,.-bsf64
.globl bsf64_alias
.type bsf64_alias,@function
bsf64_alias:
  bsf %r9,%r9
  ret
.size bsf64_alias,.-bsf64_alias
.globl bsr32
.type bsr32,@function
bsr32:
  bsr %r9d,%r10d
  ret
.size bsr32,.-bsr32
.globl bsr32_alias
.type bsr32_alias,@function
bsr32_alias:
  bsr %r9d,%r9d
  ret
.size bsr32_alias,.-bsr32_alias
.globl bsr64
.type bsr64,@function
bsr64:
  bsr %r9,%r10
  ret
.size bsr64,.-bsr64
.globl bsr64_alias
.type bsr64_alias,@function
bsr64_alias:
  bsr %r9,%r9
  ret
.size bsr64_alias,.-bsr64_alias
.globl tzcnt32
.type tzcnt32,@function
tzcnt32:
  tzcnt %r9d,%r10d
  ret
.size tzcnt32,.-tzcnt32
.globl tzcnt32_alias
.type tzcnt32_alias,@function
tzcnt32_alias:
  tzcnt %r9d,%r9d
  ret
.size tzcnt32_alias,.-tzcnt32_alias
.globl tzcnt64
.type tzcnt64,@function
tzcnt64:
  tzcnt %r9,%r10
  ret
.size tzcnt64,.-tzcnt64
.globl tzcnt64_alias
.type tzcnt64_alias,@function
tzcnt64_alias:
  tzcnt %r9,%r9
  ret
.size tzcnt64_alias,.-tzcnt64_alias
.globl lzcnt32
.type lzcnt32,@function
lzcnt32:
  lzcnt %r9d,%r10d
  ret
.size lzcnt32,.-lzcnt32
.globl lzcnt32_alias
.type lzcnt32_alias,@function
lzcnt32_alias:
  lzcnt %r9d,%r9d
  ret
.size lzcnt32_alias,.-lzcnt32_alias
.globl lzcnt64
.type lzcnt64,@function
lzcnt64:
  lzcnt %r9,%r10
  ret
.size lzcnt64,.-lzcnt64
.globl lzcnt64_alias
.type lzcnt64_alias,@function
lzcnt64_alias:
  lzcnt %r9,%r9
  ret
.size lzcnt64_alias,.-lzcnt64_alias
.globl reject16
.type reject16,@function
reject16:
  bsf %ax,%dx
  ret
.size reject16,.-reject16
.globl rejectmem
.type rejectmem,@function
rejectmem:
  bsf (%rdi),%eax
  ret
.size rejectmem,.-rejectmem
.section .note.GNU-stack,"",@progbits

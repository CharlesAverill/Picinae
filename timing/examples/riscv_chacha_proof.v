Require Import Picinae_riscv.
Require Import riscv_cfi.
Require Import riscvTiming.
Require Import List.
Import RISCVNotations.
Import ListNotations.

Import ListNotations.
Open Scope N_scope.

Definition chacha20 (_ : store) (a : addr) : N :=
    match a with
    (* <_ChaCha20_Block> *)
    | 0x0 => 0xfc010113 (* addi sp,sp,-64  *)
    | 0x4 => 0x02112e23 (* sw ra,60(sp)  *)
    | 0x8 => 0x02812c23 (* sw s0,56(sp)  *)
    | 0xc => 0x02912a23 (* sw s1,52(sp)  *)
    | 0x10 => 0x03212823 (* sw s2,48(sp)  *)
    | 0x14 => 0x03312623 (* sw s3,44(sp)  *)
    | 0x18 => 0x03412423 (* sw s4,40(sp)  *)
    | 0x1c => 0x03512223 (* sw s5,36(sp)  *)
    | 0x20 => 0x03612023 (* sw s6,32(sp)  *)
    | 0x24 => 0x01712e23 (* sw s7,28(sp)  *)
    | 0x28 => 0x01812c23 (* sw s8,24(sp)  *)
    | 0x2c => 0x01912a23 (* sw s9,20(sp)  *)
    | 0x30 => 0x01a12823 (* sw s10,16(sp)  *)
    | 0x34 => 0x01b12623 (* sw s11,12(sp)  *)
    | 0x38 => 0x61708437 (* lui s0,0x61708  *)
    | 0x3c => 0x86540413 (* addi s0,s0,-1947 # 61707865 <_ChaCha20_Exit+0x61707369>  *)
    | 0x40 => 0x332064b7 (* lui s1,0x33206  *)
    | 0x44 => 0x46e48493 (* addi s1,s1,1134 # 3320646e <_ChaCha20_Exit+0x33205f72>  *)
    | 0x48 => 0x79623937 (* lui s2,0x79623  *)
    | 0x4c => 0xd3290913 (* addi s2,s2,-718 # 79622d32 <_ChaCha20_Exit+0x79622836>  *)
    | 0x50 => 0x6b2069b7 (* lui s3,0x6b206  *)
    | 0x54 => 0x57498993 (* addi s3,s3,1396 # 6b206574 <_ChaCha20_Exit+0x6b206078>  *)
    | 0x58 => 0x0006aa03 (* lw s4,0(a3)  *)
    | 0x5c => 0x0046aa83 (* lw s5,4(a3)  *)
    | 0x60 => 0x0086ab03 (* lw s6,8(a3)  *)
    | 0x64 => 0x00c6ab83 (* lw s7,12(a3)  *)
    | 0x68 => 0x0106ac03 (* lw s8,16(a3)  *)
    | 0x6c => 0x0146ac83 (* lw s9,20(a3)  *)
    | 0x70 => 0x0186ad03 (* lw s10,24(a3)  *)
    | 0x74 => 0x01c6ad83 (* lw s11,28(a3)  *)
    | 0x78 => 0x00072283 (* lw t0,0(a4)  *)
    | 0x7c => 0x00472303 (* lw t1,4(a4)  *)
    | 0x80 => 0x00872383 (* lw t2,8(a4)  *)
    | 0x84 => 0x00a07e13 (* andi t3,zero,10  *)
    (* <_ChaCha20_Block_Loop> *)
    | 0x88 => 0x01440433 (* add s0,s0,s4  *)
    | 0x8c => 0x0087c7b3 (* xor a5,a5,s0  *)
    | 0x90 => 0x01079793 (* slli a5,a5,0x10  *)
    | 0x94 => 0x00fc0c33 (* add s8,s8,a5  *)
    | 0x98 => 0x018a4a33 (* xor s4,s4,s8  *)
    | 0x9c => 0x00ca1a13 (* slli s4,s4,0xc  *)
    | 0xa0 => 0x01440433 (* add s0,s0,s4  *)
    | 0xa4 => 0x0087c7b3 (* xor a5,a5,s0  *)
    | 0xa8 => 0x00879793 (* slli a5,a5,0x8  *)
    | 0xac => 0x00fc0c33 (* add s8,s8,a5  *)
    | 0xb0 => 0x018a4a33 (* xor s4,s4,s8  *)
    | 0xb4 => 0x007a1a13 (* slli s4,s4,0x7  *)
    | 0xb8 => 0x015484b3 (* add s1,s1,s5  *)
    | 0xbc => 0x0092c2b3 (* xor t0,t0,s1  *)
    | 0xc0 => 0x01029293 (* slli t0,t0,0x10  *)
    | 0xc4 => 0x005c8cb3 (* add s9,s9,t0  *)
    | 0xc8 => 0x019acab3 (* xor s5,s5,s9  *)
    | 0xcc => 0x00ca9a93 (* slli s5,s5,0xc  *)
    | 0xd0 => 0x015484b3 (* add s1,s1,s5  *)
    | 0xd4 => 0x0092c2b3 (* xor t0,t0,s1  *)
    | 0xd8 => 0x00829293 (* slli t0,t0,0x8  *)
    | 0xdc => 0x005c8cb3 (* add s9,s9,t0  *)
    | 0xe0 => 0x019acab3 (* xor s5,s5,s9  *)
    | 0xe4 => 0x007a9a93 (* slli s5,s5,0x7  *)
    | 0xe8 => 0x01690933 (* add s2,s2,s6  *)
    | 0xec => 0x01234333 (* xor t1,t1,s2  *)
    | 0xf0 => 0x01031313 (* slli t1,t1,0x10  *)
    | 0xf4 => 0x006d0d33 (* add s10,s10,t1  *)
    | 0xf8 => 0x01ab4b33 (* xor s6,s6,s10  *)
    | 0xfc => 0x00cb1b13 (* slli s6,s6,0xc  *)
    | 0x100 => 0x01690933 (* add s2,s2,s6  *)
    | 0x104 => 0x01234333 (* xor t1,t1,s2  *)
    | 0x108 => 0x00831313 (* slli t1,t1,0x8  *)
    | 0x10c => 0x006d0d33 (* add s10,s10,t1  *)
    | 0x110 => 0x01ab4b33 (* xor s6,s6,s10  *)
    | 0x114 => 0x007b1b13 (* slli s6,s6,0x7  *)
    | 0x118 => 0x017989b3 (* add s3,s3,s7  *)
    | 0x11c => 0x0133c3b3 (* xor t2,t2,s3  *)
    | 0x120 => 0x01039393 (* slli t2,t2,0x10  *)
    | 0x124 => 0x007d8db3 (* add s11,s11,t2  *)
    | 0x128 => 0x01bbcbb3 (* xor s7,s7,s11  *)
    | 0x12c => 0x00cb9b93 (* slli s7,s7,0xc  *)
    | 0x130 => 0x017989b3 (* add s3,s3,s7  *)
    | 0x134 => 0x0133c3b3 (* xor t2,t2,s3  *)
    | 0x138 => 0x00839393 (* slli t2,t2,0x8  *)
    | 0x13c => 0x007d8db3 (* add s11,s11,t2  *)
    | 0x140 => 0x01bbcbb3 (* xor s7,s7,s11  *)
    | 0x144 => 0x007b9b93 (* slli s7,s7,0x7  *)
    | 0x148 => 0x01540433 (* add s0,s0,s5  *)
    | 0x14c => 0x0083c3b3 (* xor t2,t2,s0  *)
    | 0x150 => 0x01039393 (* slli t2,t2,0x10  *)
    | 0x154 => 0x007d0d33 (* add s10,s10,t2  *)
    | 0x158 => 0x01aacab3 (* xor s5,s5,s10  *)
    | 0x15c => 0x00ca9a93 (* slli s5,s5,0xc  *)
    | 0x160 => 0x01540433 (* add s0,s0,s5  *)
    | 0x164 => 0x0083c3b3 (* xor t2,t2,s0  *)
    | 0x168 => 0x00839393 (* slli t2,t2,0x8  *)
    | 0x16c => 0x007d0d33 (* add s10,s10,t2  *)
    | 0x170 => 0x01aacab3 (* xor s5,s5,s10  *)
    | 0x174 => 0x007a9a93 (* slli s5,s5,0x7  *)
    | 0x178 => 0x016484b3 (* add s1,s1,s6  *)
    | 0x17c => 0x0097c7b3 (* xor a5,a5,s1  *)
    | 0x180 => 0x01079793 (* slli a5,a5,0x10  *)
    | 0x184 => 0x00fd8db3 (* add s11,s11,a5  *)
    | 0x188 => 0x01bb4b33 (* xor s6,s6,s11  *)
    | 0x18c => 0x00cb1b13 (* slli s6,s6,0xc  *)
    | 0x190 => 0x016484b3 (* add s1,s1,s6  *)
    | 0x194 => 0x0097c7b3 (* xor a5,a5,s1  *)
    | 0x198 => 0x00879793 (* slli a5,a5,0x8  *)
    | 0x19c => 0x00fd8db3 (* add s11,s11,a5  *)
    | 0x1a0 => 0x01bb4b33 (* xor s6,s6,s11  *)
    | 0x1a4 => 0x007b1b13 (* slli s6,s6,0x7  *)
    | 0x1a8 => 0x01790933 (* add s2,s2,s7  *)
    | 0x1ac => 0x0122c2b3 (* xor t0,t0,s2  *)
    | 0x1b0 => 0x01029293 (* slli t0,t0,0x10  *)
    | 0x1b4 => 0x005c0c33 (* add s8,s8,t0  *)
    | 0x1b8 => 0x018bcbb3 (* xor s7,s7,s8  *)
    | 0x1bc => 0x00cb9b93 (* slli s7,s7,0xc  *)
    | 0x1c0 => 0x01790933 (* add s2,s2,s7  *)
    | 0x1c4 => 0x0122c2b3 (* xor t0,t0,s2  *)
    | 0x1c8 => 0x00829293 (* slli t0,t0,0x8  *)
    | 0x1cc => 0x005c0c33 (* add s8,s8,t0  *)
    | 0x1d0 => 0x018bcbb3 (* xor s7,s7,s8  *)
    | 0x1d4 => 0x007b9b93 (* slli s7,s7,0x7  *)
    | 0x1d8 => 0x014989b3 (* add s3,s3,s4  *)
    | 0x1dc => 0x01334333 (* xor t1,t1,s3  *)
    | 0x1e0 => 0x01031313 (* slli t1,t1,0x10  *)
    | 0x1e4 => 0x006c8cb3 (* add s9,s9,t1  *)
    | 0x1e8 => 0x019a4a33 (* xor s4,s4,s9  *)
    | 0x1ec => 0x00ca1a13 (* slli s4,s4,0xc  *)
    | 0x1f0 => 0x014989b3 (* add s3,s3,s4  *)
    | 0x1f4 => 0x01334333 (* xor t1,t1,s3  *)
    | 0x1f8 => 0x00831313 (* slli t1,t1,0x8  *)
    | 0x1fc => 0x006c8cb3 (* add s9,s9,t1  *)
    | 0x200 => 0x019a4a33 (* xor s4,s4,s9  *)
    | 0x204 => 0x007a1a13 (* slli s4,s4,0x7  *)
    | 0x208 => 0xfffe0e13 (* addi t3,t3,-1  *)
    | 0x20c => 0x0a0e1463 (* bnez t3,2b4 <_ChaCha20_Loop>  *)
    | 0x210 => 0x00882023 (* sw s0,0(a6)  *)
    | 0x214 => 0x00982223 (* sw s1,4(a6)  *)
    | 0x218 => 0x01282423 (* sw s2,8(a6)  *)
    | 0x21c => 0x01382623 (* sw s3,12(a6)  *)
    | 0x220 => 0x01482823 (* sw s4,16(a6)  *)
    | 0x224 => 0x01582a23 (* sw s5,20(a6)  *)
    | 0x228 => 0x01682c23 (* sw s6,24(a6)  *)
    | 0x22c => 0x01782e23 (* sw s7,28(a6)  *)
    | 0x230 => 0x03882023 (* sw s8,32(a6)  *)
    | 0x234 => 0x03982223 (* sw s9,36(a6)  *)
    | 0x238 => 0x03a82423 (* sw s10,40(a6)  *)
    | 0x23c => 0x03b82623 (* sw s11,44(a6)  *)
    | 0x240 => 0x02f82823 (* sw a5,48(a6)  *)
    | 0x244 => 0x02582a23 (* sw t0,52(a6)  *)
    | 0x248 => 0x02682c23 (* sw t1,56(a6)  *)
    | 0x24c => 0x02782e23 (* sw t2,60(a6)  *)
    | 0x250 => 0x03c12083 (* lw ra,60(sp)  *)
    | 0x254 => 0x03812403 (* lw s0,56(sp)  *)
    | 0x258 => 0x03412483 (* lw s1,52(sp)  *)
    | 0x25c => 0x03012903 (* lw s2,48(sp)  *)
    | 0x260 => 0x02c12983 (* lw s3,44(sp)  *)
    | 0x264 => 0x02812a03 (* lw s4,40(sp)  *)
    | 0x268 => 0x02412a83 (* lw s5,36(sp)  *)
    | 0x26c => 0x02012b03 (* lw s6,32(sp)  *)
    | 0x270 => 0x01c12b83 (* lw s7,28(sp)  *)
    | 0x274 => 0x01812c03 (* lw s8,24(sp)  *)
    | 0x278 => 0x01412c83 (* lw s9,20(sp)  *)
    | 0x27c => 0x01012d03 (* lw s10,16(sp)  *)
    | 0x280 => 0x00c12d83 (* lw s11,12(sp)  *)
    | 0x284 => 0x04010113 (* addi sp,sp,64  *)
    | 0x288 => 0x00008067 (* ret  *)
    (* <ChaCha20_Encrypt> *)
    | 0x28c => 0xfc010113 (* addi sp,sp,-64  *)
    | 0x290 => 0x00010813 (* mv a6,sp  *)
    | 0x294 => 0xfe010113 (* addi sp,sp,-32  *)
    | 0x298 => 0x00112e23 (* sw ra,28(sp)  *)
    | 0x29c => 0x00812c23 (* sw s0,24(sp)  *)
    | 0x2a0 => 0x00912a23 (* sw s1,20(sp)  *)
    | 0x2a4 => 0x01212823 (* sw s2,16(sp)  *)
    | 0x2a8 => 0x00007433 (* and s0,zero,zero  *)
    | 0x2ac => 0x00665493 (* srli s1,a2,0x6  *)
    | 0x2b0 => 0xfff48493 (* addi s1,s1,-1  *)
    (* <_ChaCha20_Loop> *)
    | 0x2b4 => 0x00178793 (* addi a5,a5,1  *)
    | 0x2b8 => 0xd49ff0ef (* jal 0 <_ChaCha20_Block>  *)
    | 0x2bc => 0x04000313 (* li t1,64  *)
    | 0x2c0 => 0x026402b3 (* mul t0,s0,t1  *)
    | 0x2c4 => 0x00b282b3 (* add t0,t0,a1  *)
    | 0x2c8 => 0x026b0fb3 (* mul t6,s6,t1  *)
    | 0x2cc => 0x00af8fb3 (* add t6,t6,a0  *)
    | 0x2d0 => 0x0002a303 (* lw t1,0(t0)  *)
    | 0x2d4 => 0x0042a383 (* lw t2,4(t0)  *)
    | 0x2d8 => 0x00082e03 (* lw t3,0(a6)  *)
    | 0x2dc => 0x00482e83 (* lw t4,4(a6)  *)
    | 0x2e0 => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x2e4 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x2e8 => 0x006fa023 (* sw t1,0(t6)  *)
    | 0x2ec => 0x007fa223 (* sw t2,4(t6)  *)
    | 0x2f0 => 0x0082a303 (* lw t1,8(t0)  *)
    | 0x2f4 => 0x00c2a383 (* lw t2,12(t0)  *)
    | 0x2f8 => 0x00882e03 (* lw t3,8(a6)  *)
    | 0x2fc => 0x00c82e83 (* lw t4,12(a6)  *)
    | 0x300 => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x304 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x308 => 0x006fa423 (* sw t1,8(t6)  *)
    | 0x30c => 0x007fa623 (* sw t2,12(t6)  *)
    | 0x310 => 0x0102a303 (* lw t1,16(t0)  *)
    | 0x314 => 0x0142a383 (* lw t2,20(t0)  *)
    | 0x318 => 0x01082e03 (* lw t3,16(a6)  *)
    | 0x31c => 0x01482e83 (* lw t4,20(a6)  *)
    | 0x320 => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x324 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x328 => 0x006fa823 (* sw t1,16(t6)  *)
    | 0x32c => 0x007faa23 (* sw t2,20(t6)  *)
    | 0x330 => 0x0182a303 (* lw t1,24(t0)  *)
    | 0x334 => 0x01c2a383 (* lw t2,28(t0)  *)
    | 0x338 => 0x01882e03 (* lw t3,24(a6)  *)
    | 0x33c => 0x01c82e83 (* lw t4,28(a6)  *)
    | 0x340 => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x344 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x348 => 0x006fac23 (* sw t1,24(t6)  *)
    | 0x34c => 0x007fae23 (* sw t2,28(t6)  *)
    | 0x350 => 0x0202a303 (* lw t1,32(t0)  *)
    | 0x354 => 0x0242a383 (* lw t2,36(t0)  *)
    | 0x358 => 0x02082e03 (* lw t3,32(a6)  *)
    | 0x35c => 0x02482e83 (* lw t4,36(a6)  *)
    | 0x360 => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x364 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x368 => 0x026fa023 (* sw t1,32(t6)  *)
    | 0x36c => 0x027fa223 (* sw t2,36(t6)  *)
    | 0x370 => 0x0282a303 (* lw t1,40(t0)  *)
    | 0x374 => 0x02c2a383 (* lw t2,44(t0)  *)
    | 0x378 => 0x02882e03 (* lw t3,40(a6)  *)
    | 0x37c => 0x02c82e83 (* lw t4,44(a6)  *)
    | 0x380 => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x384 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x388 => 0x026fa423 (* sw t1,40(t6)  *)
    | 0x38c => 0x027fa623 (* sw t2,44(t6)  *)
    | 0x390 => 0x0302a303 (* lw t1,48(t0)  *)
    | 0x394 => 0x0342a383 (* lw t2,52(t0)  *)
    | 0x398 => 0x03082e03 (* lw t3,48(a6)  *)
    | 0x39c => 0x03482e83 (* lw t4,52(a6)  *)
    | 0x3a0 => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x3a4 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x3a8 => 0x026fa823 (* sw t1,48(t6)  *)
    | 0x3ac => 0x027faa23 (* sw t2,52(t6)  *)
    | 0x3b0 => 0x0382a303 (* lw t1,56(t0)  *)
    | 0x3b4 => 0x03c2a383 (* lw t2,60(t0)  *)
    | 0x3b8 => 0x03882e03 (* lw t3,56(a6)  *)
    | 0x3bc => 0x03c82e83 (* lw t4,60(a6)  *)
    | 0x3c0 => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x3c4 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x3c8 => 0x026fac23 (* sw t1,56(t6)  *)
    | 0x3cc => 0x027fae23 (* sw t2,60(t6)  *)
    | 0x3d0 => 0x00140413 (* addi s0,s0,1  *)
    | 0x3d4 => 0xee9410e3 (* bne s0,s1,2b4 <_ChaCha20_Loop>  *)
    | 0x3d8 => 0x04000293 (* li t0,64  *)
    | 0x3dc => 0x02567333 (* remu t1,a2,t0  *)
    | 0x3e0 => 0x10030e63 (* beqz t1,4fc <_ChaCha20_Exit>  *)
    | 0x3e4 => 0x02564333 (* div t1,a2,t0  *)
    | 0x3e8 => 0x04000393 (* li t2,64  *)
    | 0x3ec => 0x027302b3 (* mul t0,t1,t2  *)
    | 0x3f0 => 0x00b282b3 (* add t0,t0,a1  *)
    | 0x3f4 => 0x02730fb3 (* mul t6,t1,t2  *)
    | 0x3f8 => 0x00af8fb3 (* add t6,t6,a0  *)
    | 0x3fc => 0x0002a303 (* lw t1,0(t0)  *)
    | 0x400 => 0x0042a383 (* lw t2,4(t0)  *)
    | 0x404 => 0x00082e03 (* lw t3,0(a6)  *)
    | 0x408 => 0x00482e83 (* lw t4,4(a6)  *)
    | 0x40c => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x410 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x414 => 0x006fa023 (* sw t1,0(t6)  *)
    | 0x418 => 0x007fa223 (* sw t2,4(t6)  *)
    | 0x41c => 0x0082a303 (* lw t1,8(t0)  *)
    | 0x420 => 0x00c2a383 (* lw t2,12(t0)  *)
    | 0x424 => 0x00882e03 (* lw t3,8(a6)  *)
    | 0x428 => 0x00c82e83 (* lw t4,12(a6)  *)
    | 0x42c => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x430 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x434 => 0x006fa423 (* sw t1,8(t6)  *)
    | 0x438 => 0x007fa623 (* sw t2,12(t6)  *)
    | 0x43c => 0x0102a303 (* lw t1,16(t0)  *)
    | 0x440 => 0x0142a383 (* lw t2,20(t0)  *)
    | 0x444 => 0x01082e03 (* lw t3,16(a6)  *)
    | 0x448 => 0x01482e83 (* lw t4,20(a6)  *)
    | 0x44c => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x450 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x454 => 0x006fa823 (* sw t1,16(t6)  *)
    | 0x458 => 0x007faa23 (* sw t2,20(t6)  *)
    | 0x45c => 0x0182a303 (* lw t1,24(t0)  *)
    | 0x460 => 0x01c2a383 (* lw t2,28(t0)  *)
    | 0x464 => 0x01882e03 (* lw t3,24(a6)  *)
    | 0x468 => 0x01c82e83 (* lw t4,28(a6)  *)
    | 0x46c => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x470 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x474 => 0x006fac23 (* sw t1,24(t6)  *)
    | 0x478 => 0x007fae23 (* sw t2,28(t6)  *)
    | 0x47c => 0x0202a303 (* lw t1,32(t0)  *)
    | 0x480 => 0x0242a383 (* lw t2,36(t0)  *)
    | 0x484 => 0x02082e03 (* lw t3,32(a6)  *)
    | 0x488 => 0x02482e83 (* lw t4,36(a6)  *)
    | 0x48c => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x490 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x494 => 0x026fa023 (* sw t1,32(t6)  *)
    | 0x498 => 0x027fa223 (* sw t2,36(t6)  *)
    | 0x49c => 0x0282a303 (* lw t1,40(t0)  *)
    | 0x4a0 => 0x02c2a383 (* lw t2,44(t0)  *)
    | 0x4a4 => 0x02882e03 (* lw t3,40(a6)  *)
    | 0x4a8 => 0x02c82e83 (* lw t4,44(a6)  *)
    | 0x4ac => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x4b0 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x4b4 => 0x026fa423 (* sw t1,40(t6)  *)
    | 0x4b8 => 0x027fa623 (* sw t2,44(t6)  *)
    | 0x4bc => 0x0302a303 (* lw t1,48(t0)  *)
    | 0x4c0 => 0x0342a383 (* lw t2,52(t0)  *)
    | 0x4c4 => 0x03082e03 (* lw t3,48(a6)  *)
    | 0x4c8 => 0x03482e83 (* lw t4,52(a6)  *)
    | 0x4cc => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x4d0 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x4d4 => 0x026fa823 (* sw t1,48(t6)  *)
    | 0x4d8 => 0x027faa23 (* sw t2,52(t6)  *)
    | 0x4dc => 0x0382a303 (* lw t1,56(t0)  *)
    | 0x4e0 => 0x03c2a383 (* lw t2,60(t0)  *)
    | 0x4e4 => 0x03882e03 (* lw t3,56(a6)  *)
    | 0x4e8 => 0x03c82e83 (* lw t4,60(a6)  *)
    | 0x4ec => 0x01c34333 (* xor t1,t1,t3  *)
    | 0x4f0 => 0x01d3c3b3 (* xor t2,t2,t4  *)
    | 0x4f4 => 0x026fac23 (* sw t1,56(t6)  *)
    | 0x4f8 => 0x027fae23 (* sw t2,60(t6)  *)
    (* <_ChaCha20_Exit> *)
    | 0x4fc => 0x01c12083 (* lw ra,28(sp)  *)
    | 0x500 => 0x01812403 (* lw s0,24(sp)  *)
    | 0x504 => 0x01412483 (* lw s1,20(sp)  *)
    | 0x508 => 0x01012903 (* lw s2,16(sp)  *)
    | 0x50c => 0x02010113 (* addi sp,sp,32  *)
    | 0x510 => 0x04010113 (* addi sp,sp,64  *)
    | 0x514 => 0x00008067 (* ret  *)
    | _ => 0
    end.
Definition chacha20_max := 0x514.
Definition chacha20_len := Z.to_nat ((0x514 / 4) + 1).

Variable ML : N.
Variable ML_pos : 1 <= ML.

Module riscv_toa.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (chacha20 s a) with
        | Some x => x | _ => 0 end.
End riscv_toa.
Module riscvT := MakeTimingContents riscvTiming riscv_toa.
Export riscvT.

Definition range (base : N) (m : nat) : list N :=
    let fix aux max :=
        match max with
        | O => []
        | S n' =>
            let l := aux n' in
            base + N.of_nat (4 * List.length l) :: l
        end
    in List.rev (aux m).

Definition rv_stmt' m a :=
                                            (* removed getmem here. why was it giving nops? *)
  rv2il a match a mod 4 with 0 => rv_decode (m a) | _ => R5_InvalidI end.

Definition il_list : program_list :=
    List.map (fun a => (a, Some (4, rv_stmt' (chacha20 empty_store) a))) (range 0 chacha20_len).

Definition lifted_chacha20 :=
    program_of_list il_list.

Require Import Bool.
Fixpoint stmt_contains_jmp (s : stmt) :=
    match s with
    | Jmp _ => true
    | Seq s1 s2 => stmt_contains_jmp s1 || stmt_contains_jmp s2
    | _ => false
    end.
Fixpoint stmt_contains_conditional_jmp (s : stmt) :=
    match s with
    | If _ s1 s2 => stmt_contains_jmp s1 || stmt_contains_jmp s2
    | Seq s1 s2 => stmt_contains_conditional_jmp s1 || stmt_contains_conditional_jmp s2
    | _ => false
    end.

Definition cycle_count_of_trace (t : trace) : N :=
    List.fold_left N.add (List.map 
        (fun '(e, s) => match e with 
            | Addr a => time_of_addr s a
            | Raise n => max32
            end) t) 0.

Lemma fold_left_cons : forall {X : Type} (t : list X) (h : X) (f : X -> X -> X) (base : X) 
    (Comm : forall a b, f a b = f b a) (Assoc : forall a b c, f a (f b c) = f (f a b) c),
    List.fold_left f (h :: t) base = f h (List.fold_left f t base).
Proof.
    induction t; intros.
    - simpl. now rewrite Comm.
    - simpl in *. rewrite IHt, IHt, IHt,
        Assoc, Assoc, (Comm a h); auto.
Qed.

Lemma cycle_count_of_trace_single :
    forall (e : exit) (s : store),
    cycle_count_of_trace [(e, s)] = 
        match e with 
        | Addr a => time_of_addr s a
        | Raise n => max32
        end.
Proof. reflexivity. Qed.

Lemma cycle_count_of_trace_cons :
    forall (t : trace) (e : exit) (s : store),
    cycle_count_of_trace ((e, s) :: t) = cycle_count_of_trace [(e, s)] + cycle_count_of_trace t.
Proof.
    intros. unfold cycle_count_of_trace at 2. rewrite map_cons, fold_left_cons; try lia. simpl.
    unfold cycle_count_of_trace at 1. rewrite map_cons, fold_left_cons. rewrite N.add_0_r. reflexivity.
    lia. lia.
Qed.

Definition timing_invariant_from_stmt (s : stmt) (t : trace) :=
    if stmt_contains_conditional_jmp s then

    else
        cycle_count_of_trace

Compute il_list.

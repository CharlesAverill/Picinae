Require Import Picinae_riscv.
Require Import NArith.

Definition memcmp_ft (a : addr) : N :=
    match a with
    (* <CRYPTO_memcmp> *)
    | 0x0 => 0x08060463 (* beq a2,zero,88 <.L4>  *)
    | 0x4 => 0x08060263 (* beq a2,zero,88 <.L4>  *)
    | 0x8 => 0x00050793 (* addi a5,a0,0  *)
    | 0xc => 0x00050793 (* addi a5,a0,0  *)
    | 0x10 => 0x00c502b3 (* add t0,a0,a2  *)
    | 0x14 => 0x00c502b3 (* add t0,a0,a2  *)
    | 0x18 => 0x00028613 (* addi a2,t0,0  *)
    | 0x1c => 0x00028613 (* addi a2,t0,0  *)
    | 0x20 => 0x00000513 (* addi a0,zero,0  *)
    | 0x24 => 0x00000513 (* addi a0,zero,0  *)
    (* <.L3> *)
    | 0x28 => 0x0007c683 (* lbu a3,0(a5)  *)
    | 0x2c => 0x0007c683 (* lbu a3,0(a5)  *)
    | 0x30 => 0x0005c703 (* lbu a4,0(a1)  *)
    | 0x34 => 0x0005c703 (* lbu a4,0(a1)  *)
    | 0x38 => 0x00d742b3 (* xor t0,a4,a3  *)
    | 0x3c => 0x00d742b3 (* xor t0,a4,a3  *)
    | 0x40 => 0x00028713 (* addi a4,t0,0  *)
    | 0x44 => 0x00028713 (* addi a4,t0,0  *)
    | 0x48 => 0x00e562b3 (* or t0,a0,a4  *)
    | 0x4c => 0x00e562b3 (* or t0,a0,a4  *)
    | 0x50 => 0x00028513 (* addi a0,t0,0  *)
    | 0x54 => 0x00028513 (* addi a0,t0,0  *)
    | 0x58 => 0x00178293 (* addi t0,a5,1  *)
    | 0x5c => 0x00178293 (* addi t0,a5,1  *)
    | 0x60 => 0x00028793 (* addi a5,t0,0  *)
    | 0x64 => 0x00028793 (* addi a5,t0,0  *)
    | 0x68 => 0x00158293 (* addi t0,a1,1  *)
    | 0x6c => 0x00158293 (* addi t0,a1,1  *)
    | 0x70 => 0x00028593 (* addi a1,t0,0  *)
    | 0x74 => 0x00028593 (* addi a1,t0,0  *)
    | 0x78 => 0xfac798e3 (* bne a5,a2,28 <.L3>  *)
    | 0x7c => 0xfac796e3 (* bne a5,a2,28 <.L3>  *)
    | 0x80 => 0x00008067 (* jalr zero,0(ra)  *)
    | 0x84 => 0x00008067 (* jalr zero,0(ra)  *)
    (* <.L4> *)
    | 0x88 => 0x00000513 (* addi a0,zero,0  *)
    | 0x8c => 0x00000513 (* addi a0,zero,0  *)
    | 0x90 => 0x00008067 (* jalr zero,0(ra)  *)
    | 0x94 => 0x00008067 (* jalr zero,0(ra)  *)
    | _ => 0
    end.

Definition start_memcmp_ft : N := 0x0.
Definition end_memcmp_ft : N := 0x94.

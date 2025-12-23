Require Import Picinae_riscv.
Require Import NArith.

Definition br_ccopy_ft (a : addr) : N :=
    match a with
    (* <br_ccopy> *)
    | 0x0 => 0x40a002b3 (* sub t0,zero,a0  *)
    | 0x4 => 0x40a002b3 (* sub t0,zero,a0  *)
    | 0x8 => 0x00028513 (* addi a0,t0,0  *)
    | 0xc => 0x00028513 (* addi a0,t0,0  *)
    | 0x10 => 0x00d58833 (* add a6,a1,a3  *)
    | 0x14 => 0x00d58833 (* add a6,a1,a3  *)
    | 0x18 => 0x06068c63 (* beq a3,zero,90 <.L1>  *)
    | 0x1c => 0x06068a63 (* beq a3,zero,90 <.L1>  *)
    (* <.L3> *)
    | 0x20 => 0x0005c703 (* lbu a4,0(a1)  *)
    | 0x24 => 0x00064783 (* lbu a5,0(a2)  *)
    | 0x28 => 0x0005c703 (* lbu a4,0(a1)  *)
    | 0x2c => 0x00064783 (* lbu a5,0(a2)  *)
    | 0x30 => 0x00158293 (* addi t0,a1,1  *)
    | 0x34 => 0x00158293 (* addi t0,a1,1  *)
    | 0x38 => 0x00028593 (* addi a1,t0,0  *)
    | 0x3c => 0x00028593 (* addi a1,t0,0  *)
    | 0x40 => 0x00160293 (* addi t0,a2,1  *)
    | 0x44 => 0x00160293 (* addi t0,a2,1  *)
    | 0x48 => 0x00028613 (* addi a2,t0,0  *)
    | 0x4c => 0x00028613 (* addi a2,t0,0  *)
    | 0x50 => 0x00f742b3 (* xor t0,a4,a5  *)
    | 0x54 => 0x00f742b3 (* xor t0,a4,a5  *)
    | 0x58 => 0x00028793 (* addi a5,t0,0  *)
    | 0x5c => 0x00028793 (* addi a5,t0,0  *)
    | 0x60 => 0x00a7f2b3 (* and t0,a5,a0  *)
    | 0x64 => 0x00a7f2b3 (* and t0,a5,a0  *)
    | 0x68 => 0x00028793 (* addi a5,t0,0  *)
    | 0x6c => 0x00028793 (* addi a5,t0,0  *)
    | 0x70 => 0x00e7c2b3 (* xor t0,a5,a4  *)
    | 0x74 => 0x00e7c2b3 (* xor t0,a5,a4  *)
    | 0x78 => 0x00028793 (* addi a5,t0,0  *)
    | 0x7c => 0x00028793 (* addi a5,t0,0  *)
    | 0x80 => 0xfef58fa3 (* sb a5,-1(a1)  *)
    | 0x84 => 0xfef58fa3 (* sb a5,-1(a1)  *)
    | 0x88 => 0xf9059ce3 (* bne a1,a6,20 <.L3>  *)
    | 0x8c => 0xf9059ae3 (* bne a1,a6,20 <.L3>  *)
    (* <.L1> *)
    | 0x90 => 0x00008067 (* jalr zero,0(ra)  *)
    | 0x94 => 0x00008067 (* jalr zero,0(ra)  *)
    | _ => 0
    end.

Definition start_br_ccopy_ft : N := 0x0.
Definition end_br_ccopy_ft : N := 0x94.

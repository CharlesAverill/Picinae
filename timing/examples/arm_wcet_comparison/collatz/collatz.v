(* Auto-generated from collatz/collatz.elf *)
From Stdlib Require Import NArith.
Require Import Picinae_armv6m.

Open Scope N.

Definition collatz_collatz_armv6m (a : addr) : N :=
    match a with
    (* <collatz> *)
    | 0x8000000 => 0x0003 (* movs r3, r0 *)
    | 0x8000002 => 0xb510 (* push {r4, lr} *)
    | 0x8000004 => 0x2000 (* movs r0, #0 *)
    | 0x8000006 => 0x2401 (* movs r4, #1 *)
    | 0x8000008 => 0x4a09 (* ldr r2, [pc, #36] @ (8000030 <collatz+0x30>) *)
    | 0x800000a => 0xe002 (* b.n 8000012 <collatz+0x12> *)
    | 0x800000c => 0x3001 (* adds r0, #1 *)
    | 0x800000e => 0x4290 (* cmp r0, r2 *)
    | 0x8000010 => 0xd00c (* beq.n 800002c <collatz+0x2c> *)
    | 0x8000012 => 0x421c (* tst r4, r3 *)
    | 0x8000014 => 0xd006 (* beq.n 8000024 <collatz+0x24> *)
    | 0x8000016 => 0x0059 (* lsls r1, r3, #1 *)
    | 0x8000018 => 0x185b (* adds r3, r3, r1 *)
    | 0x800001a => 0x3301 (* adds r3, #1 *)
    | 0x800001c => 0x3001 (* adds r0, #1 *)
    | 0x800001e => 0xb29b (* uxth r3, r3 *)
    | 0x8000020 => 0x4290 (* cmp r0, r2 *)
    | 0x8000022 => 0xd003 (* beq.n 800002c <collatz+0x2c> *)
    | 0x8000024 => 0x085b (* lsrs r3, r3, #1 *)
    | 0x8000026 => 0x2b01 (* cmp r3, #1 *)
    | 0x8000028 => 0xd1f0 (* bne.n 800000c <collatz+0xc> *)
    | 0x800002a => 0xbd10 (* pop {r4, pc} *)
    | 0x800002c => 0x2000 (* movs r0, #0 *)
    | 0x800002e => 0xe7fc (* b.n 800002a <collatz+0x2a> *)
    | 0x8000030 => 0xd6d8 (* .word 0x0000d6d8 *)
    | 0x8000032 => 0x0000 (* (high halfword) *)
    | _ => 0
    end.

Definition start_collatz_collatz_armv6m : N := 0x8000000.
Definition end_collatz_collatz_armv6m : N := 0x8000032.

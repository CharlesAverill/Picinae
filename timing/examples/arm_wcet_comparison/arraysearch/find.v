(* Auto-generated from arraysearch/arraysearch.elf *)
From Stdlib Require Import NArith.
Require Import Picinae_armv6m.

Open Scope N.

Definition arraysearch_find_armv6m (a : addr) : N :=
    match a with
    (* <find> *)
    | 0x8000000 => 0xb530 (* push {r4, r5, lr} *)
    | 0x8000002 => 0x2900 (* cmp r1, #0 *)
    | 0x8000004 => 0xd00d (* beq.n 8000022 <find+0x22> *)
    | 0x8000006 => 0x2400 (* movs r4, #0 *)
    | 0x8000008 => 0xe003 (* b.n 8000012 <find+0x12> *)
    | 0x800000a => 0x3401 (* adds r4, #1 *)
    | 0x800000c => 0x3008 (* adds r0, #8 *)
    | 0x800000e => 0x428c (* cmp r4, r1 *)
    | 0x8000010 => 0xd207 (* bcs.n 8000022 <find+0x22> *)
    | 0x8000012 => 0x6805 (* ldr r5, [r0, #0] *)
    | 0x8000014 => 0x4295 (* cmp r5, r2 *)
    | 0x8000016 => 0xd1f8 (* bne.n 800000a <find+0xa> *)
    | 0x8000018 => 0x6845 (* ldr r5, [r0, #4] *)
    | 0x800001a => 0x429d (* cmp r5, r3 *)
    | 0x800001c => 0xd1f5 (* bne.n 800000a <find+0xa> *)
    | 0x800001e => 0xb2a0 (* uxth r0, r4 *)
    | 0x8000020 => 0xe000 (* b.n 8000024 <find+0x24> *)
    | 0x8000022 => 0x4801 (* ldr r0, [pc, #4] @ (8000028 <find+0x28>) *)
    | 0x8000024 => 0xbd30 (* pop {r4, r5, pc} *)
    | 0x8000026 => 0x46c0 (* nop @ (mov r8, r8) *)
    | 0x8000028 => 0xffff (* .word 0x0000ffff *)
    | 0x800002a => 0x0000 (* (high halfword) *)
    | _ => 0
    end.

Definition start_arraysearch_find_armv6m : N := 0x8000000.
Definition end_arraysearch_find_armv6m : N := 0x800002a.

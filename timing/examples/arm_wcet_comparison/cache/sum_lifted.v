(* Auto-generated from cache/cache.elf *)
From Stdlib Require Import NArith.
Require Import Picinae_armv6m.

Open Scope N.

Definition cache_sum_armv6m (a : addr) : N :=
    match a with
    (* <sum> *)
    | 0x8000000 => 0x2900 (* cmp r1, #0 *)
    | 0x8000002 => 0xd008 (* beq.n 8000016 <sum+0x16> *)
    | 0x8000004 => 0x0089 (* lsls r1, r1, #2 *)
    | 0x8000006 => 0x0003 (* movs r3, r0 *)
    | 0x8000008 => 0x1841 (* adds r1, r0, r1 *)
    | 0x800000a => 0x2000 (* movs r0, #0 *)
    | 0x800000c => 0xcb04 (* ldmia r3!, {r2} *)
    | 0x800000e => 0x1880 (* adds r0, r0, r2 *)
    | 0x8000010 => 0x428b (* cmp r3, r1 *)
    | 0x8000012 => 0xd1fb (* bne.n 800000c <sum+0xc> *)
    | 0x8000014 => 0x4770 (* bx lr *)
    | 0x8000016 => 0x2000 (* movs r0, #0 *)
    | 0x8000018 => 0xe7fc (* b.n 8000014 <sum+0x14> *)
    | _ => 0
    end.

Definition start_cache_sum_armv6m : N := 0x8000000.
Definition end_cache_sum_armv6m : N := 0x8000018.

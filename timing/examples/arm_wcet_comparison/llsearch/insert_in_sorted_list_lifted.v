(* Auto-generated from llsearch/linked_list.elf *)
From Stdlib Require Import NArith.
Require Import Picinae_armv6m.

Open Scope N.

Definition linked_list_insert_in_sorted_list_armv6m (a : addr) : N :=
    match a with
    (* <insert_in_sorted_list> *)
    | 0x8000044 => 0x680a (* ldr r2, [r1, #0] *)
    | 0x8000046 => 0x4b07 (* ldr r3, [pc, #28] @ (8000064 <insert_in_sorted_list+0x20>) *)
    | 0x8000048 => 0xb510 (* push {r4, lr} *)
    | 0x800004a => 0x429a (* cmp r2, r3 *)
    | 0x800004c => 0xd007 (* beq.n 800005e <insert_in_sorted_list+0x1a> *)
    | 0x800004e => 0x0004 (* movs r4, r0 *)
    | 0x8000050 => 0x6840 (* ldr r0, [r0, #4] *)
    | 0x8000052 => 0x6803 (* ldr r3, [r0, #0] *)
    | 0x8000054 => 0x429a (* cmp r2, r3 *)
    | 0x8000056 => 0xd2fa (* bcs.n 800004e <insert_in_sorted_list+0xa> *)
    | 0x8000058 => 0x6048 (* str r0, [r1, #4] *)
    | 0x800005a => 0x6061 (* str r1, [r4, #4] *)
    | 0x800005c => 0xbd10 (* pop {r4, pc} *)
    | 0x800005e => 0x0004 (* movs r4, r0 *)
    | 0x8000060 => 0x6840 (* ldr r0, [r0, #4] *)
    | 0x8000062 => 0xe7f9 (* b.n 8000058 <insert_in_sorted_list+0x14> *)
    | 0x8000064 => 0xffff (* .word 0x7fffffff *)
    | 0x8000066 => 0x7fff (* (high halfword) *)
    | _ => 0
    end.

Definition start_linked_list_insert_in_sorted_list_armv6m : N := 0x8000044.
Definition end_linked_list_insert_in_sorted_list_armv6m : N := 0x8000066.

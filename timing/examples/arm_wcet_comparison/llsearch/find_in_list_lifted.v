(* Auto-generated from llsearch/linked_list.elf *)
From Stdlib Require Import NArith.
Require Import Picinae_armv6m.

Open Scope N.

Definition linked_list_find_in_list_armv6m (a : addr) : N :=
    match a with
    (* <find_in_list> *)
    | 0x800002c => 0x2800 (* cmp r0, #0 *)
    | 0x800002e => 0xd006 (* beq.n 800003e <find_in_list+0x12> *)
    | 0x8000030 => 0x6803 (* ldr r3, [r0, #0] *)
    | 0x8000032 => 0x428b (* cmp r3, r1 *)
    | 0x8000034 => 0xd002 (* beq.n 800003c <find_in_list+0x10> *)
    | 0x8000036 => 0x6840 (* ldr r0, [r0, #4] *)
    | 0x8000038 => 0x2800 (* cmp r0, #0 *)
    | 0x800003a => 0xd1f9 (* bne.n 8000030 <find_in_list+0x4> *)
    | 0x800003c => 0x4770 (* bx lr *)
    | 0x800003e => 0x2000 (* movs r0, #0 *)
    | 0x8000040 => 0xe7fc (* b.n 800003c <find_in_list+0x10> *)
    | _ => 0
    end.

Definition start_linked_list_find_in_list_armv6m : N := 0x800002c.
Definition end_linked_list_find_in_list_armv6m : N := 0x8000040.

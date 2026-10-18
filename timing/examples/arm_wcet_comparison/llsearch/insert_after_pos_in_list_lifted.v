(* Auto-generated from llsearch/linked_list.elf *)
From Stdlib Require Import NArith.
Require Import Picinae_armv6m.

Open Scope N.

Definition linked_list_insert_after_pos_in_list_armv6m (a : addr) : N :=
    match a with
    (* <insert_after_pos_in_list> *)
    | 0x8000000 => 0xb510 (* push {r4, lr} *)
    | 0x8000002 => 0x2800 (* cmp r0, #0 *)
    | 0x8000004 => 0xd00e (* beq.n 8000024 <insert_after_pos_in_list+0x24> *)
    | 0x8000006 => 0x2900 (* cmp r1, #0 *)
    | 0x8000008 => 0xd00c (* beq.n 8000024 <insert_after_pos_in_list+0x24> *)
    | 0x800000a => 0x2300 (* movs r3, #0 *)
    | 0x800000c => 0x2a00 (* cmp r2, #0 *)
    | 0x800000e => 0xd103 (* bne.n 8000018 <insert_after_pos_in_list+0x18> *)
    | 0x8000010 => 0xe009 (* b.n 8000026 <insert_after_pos_in_list+0x26> *)
    | 0x8000012 => 0x3301 (* adds r3, #1 *)
    | 0x8000014 => 0x429a (* cmp r2, r3 *)
    | 0x8000016 => 0xd006 (* beq.n 8000026 <insert_after_pos_in_list+0x26> *)
    | 0x8000018 => 0x0004 (* movs r4, r0 *)
    | 0x800001a => 0x6840 (* ldr r0, [r0, #4] *)
    | 0x800001c => 0x2800 (* cmp r0, #0 *)
    | 0x800001e => 0xd1f8 (* bne.n 8000012 <insert_after_pos_in_list+0x12> *)
    | 0x8000020 => 0x6048 (* str r0, [r1, #4] *)
    | 0x8000022 => 0x6061 (* str r1, [r4, #4] *)
    | 0x8000024 => 0xbd10 (* pop {r4, pc} *)
    | 0x8000026 => 0x0004 (* movs r4, r0 *)
    | 0x8000028 => 0x6840 (* ldr r0, [r0, #4] *)
    | 0x800002a => 0xe7f9 (* b.n 8000020 <insert_after_pos_in_list+0x20> *)
    | _ => 0
    end.

Definition start_linked_list_insert_after_pos_in_list_armv6m : N := 0x8000000.
Definition end_linked_list_insert_after_pos_in_list_armv6m : N := 0x800002a.

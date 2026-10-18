(* Auto-generated from while_true_break/while_true_break.elf *)
From Stdlib Require Import NArith.
Require Import Picinae_armv6m.

Open Scope N.

Definition while_true_break_while_true_break_armv6m (a : addr) : N :=
    match a with
    (* <while_true_break> *)
    | 0x8000000 => 0x0002 (* movs r2, r0 *)
    | 0x8000002 => 0x4342 (* muls r2, r0 *)
    | 0x8000004 => 0x0043 (* lsls r3, r0, #1 *)
    | 0x8000006 => 0x429a (* cmp r2, r3 *)
    | 0x8000008 => 0xd905 (* bls.n 8000016 <while_true_break+0x16> *)
    | 0x800000a => 0x3801 (* subs r0, #1 *)
    | 0x800000c => 0x0003 (* movs r3, r0 *)
    | 0x800000e => 0x4343 (* muls r3, r0 *)
    | 0x8000010 => 0x0042 (* lsls r2, r0, #1 *)
    | 0x8000012 => 0x429a (* cmp r2, r3 *)
    | 0x8000014 => 0xd3f9 (* bcc.n 800000a <while_true_break+0xa> *)
    | 0x8000016 => 0x4770 (* bx lr *)
    | _ => 0
    end.

Definition start_while_true_break_while_true_break_armv6m : N := 0x8000000.
Definition end_while_true_break_while_true_break_armv6m : N := 0x8000016.

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8.
Require Import nops_o_tiny_nop_armv8.

Import ARM8Notations.
Open Scope N.

Definition tiny_nop_exit (t:trace) :=
  match t with (Addr a, _)::_ => match a with
  | 0x00100000 => true
  | _ => false end | _ => false end.

Definition tiny_nop_invs (s0:store) (t:trace) :=
  match t with (Addr a, s)::_ => match a with
  | 0x00100000 => Some (s = s0)
  | _ => None end | _ => None end.

Theorem tiny_nop_pc :
  forall s t x' s'
     (ENTRY: startof t (x',s') = (Addr 0x00100000,s))
     (MDL: models arm8typctx s),
     satisfies_all tiny_nop (tiny_nop_invs s) tiny_nop_exit ((x',s')::t).
Proof.
  Local Ltac step := time arm8_step.
  intros.
  (* Base case *)
  apply prove_invs. simpl. rewrite ENTRY. step. reflexivity.
  (* Inductive step *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply tinynop_welltyped).
  clear - PRE MDL. rename t1 into t. rename s into s0; rename s1 into s.
  destruct_inv 64 PRE.
Qed.
Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8_pcode.
Require Import nops_o_branch_nop_armv8.

Import ARM8Notations.
Open Scope N.

Definition branch_nop_exit (t:trace) :=
  match t with (Addr a, _)::_ => match a with
  | 0x0010002c => true
  | _ => false end | _ => false end.
  
Definition branch_nop_invs (s0:store) (t:trace) :=
  match t with (Addr a, s)::_ => match a with
  | 0x00100018 => Some (arm8equiv s s0)
  | 0x0010002c => Some (arm8equiv s s0)
  | _ => None end | _ => None end.
  
Theorem branch_nop_pc :
  forall s t x' s'
     (ENTRY: startof t (x',s') = (Addr 0x00100018,s))
     (MDL: models arm8typctx s),
     satisfies_all branch_nop (branch_nop_invs s) branch_nop_exit ((x',s')::t).
Proof.
  Local Ltac step := time arm8_step.
  intros. 
  (* Base case *)
  apply prove_invs. simpl. rewrite ENTRY. step. 
  unfold arm8equiv; intros; reflexivity.
  (* Inductive step *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply branchnop_welltyped).
  clear - PRE MDL. rename t1 into t. rename s into s0; rename s1 into s.
  destruct_inv 64 PRE.
  rename PRE into S0.
  
  repeat step; unfold arm8equiv in *; intros v SIG; specialize (S0 v SIG).
  * rewrite N.eqb_eq in BC; subst; symmetry in Hsv.
    destruct v;
      repeat (rewrite update_updated || rewrite update_frame); try easy.
      rewrite S0 in Hsv. easy.
  * destruct v;
      repeat (rewrite update_updated || rewrite update_frame); try easy.
      now rewrite <-S0.
 
Qed.
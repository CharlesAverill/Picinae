Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8.
Require Import nops_o_loop_nop_armv8.

Import ARM8Notations.
Open Scope N.

Definition loop_nop_exit (t:trace) :=
  match t with (Addr a, _)::_ => match a with
  | 0x00100040 => true
  | _ => false end | _ => false end.

Definition loop_nop_invs (s0:store) (t:trace) :=
  match t with (Addr a, s)::_ => match a with
  | 0x00100030 => Some (arm8equiv_or s s0 (fun v => match v with R_X0 => true | _ => false end))
  | 0x00100040 => Some (arm8equiv_or s s0 (fun v => match v with R_X0 => true | _ => false end))
  | _ => None end | _ => None end.

Theorem loop_nop_pc :
  forall s t x' s'
     (ENTRY: startof t (x',s') = (Addr 0x00100030,s))
     (MDL: models arm8typctx s),
     satisfies_all loop_nop (loop_nop_invs s) loop_nop_exit ((x',s')::t).
Proof.
  Local Ltac step := time arm8_step.
  intros.
  (* Base case *)
  apply prove_invs. simpl. rewrite ENTRY. step.
  unfold arm8equiv_or; intros. right; reflexivity.
  (* Inductive step *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply loopnop_welltyped).
  clear - PRE MDL. rename t1 into t. rename s into s0; rename s1 into s.
  destruct_inv 64 PRE.
  rename PRE into S0.

  repeat step; unfold arm8equiv in *; intros v SIG; specialize (S0 v SIG).
  * rewrite N.eqb_eq in BC; subst; symmetry in Hsv.
    destruct v; match goal with
    | [ |- context[or (eq true true) _] ] => now left
    | _ => right; repeat (rewrite update_updated || rewrite update_frame); try easy;
      match goal with | [ H: or (eq false true) _ |- _ ] => inversion H; [discriminate | easy]
      end
    end.
  * destruct v; match goal with
    | [ |- context[or (eq true true) _] ] => now left
    | _ => right; repeat (rewrite update_updated || rewrite update_frame); try easy;
      match goal with | [ H: or (eq false true) _ |- _ ] => inversion H; [discriminate | easy]
      end
    end.
Qed.

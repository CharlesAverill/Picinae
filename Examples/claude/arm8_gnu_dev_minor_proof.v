(* gnu_dev_minor (AArch64) -- glibc dev_t minor.  Spec (dev_minor) shared with amd64.  AArch64 port. *)
Require Import Picinae_armv8.
Require Import gnu_dev_minor_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.
Theorem gnu_dev_minor_nwc: forall s2 s1, gnu_dev_minor_arm8 s1 = gnu_dev_minor_arm8 s2.
Proof. reflexivity. Qed.
Theorem gnu_dev_minor_welltyped: welltyped_prog arm8typctx gnu_dev_minor_arm8.
Proof. Picinae_typecheck. Qed.
Theorem gnu_dev_minor_preserves_memory:
  forall_endstates gnu_dev_minor_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Definition gnu_dev_minor_exit (t:trace) := match t with (Addr 12,_)::_ => true | _ => false end.
Definition postcondition (d:N) (s:store) := s R_X0 = dev_minor d.
Definition gnu_dev_minor_invs (d:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_X0 = d)
  | 12 => Some (postcondition d s)
  | _ => None end | _ => None end.
Theorem gnu_dev_minor_correct:
  forall s t s' x' d
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s) (D: s R_X0 = d),
  satisfies_all gnu_dev_minor_arm8 (gnu_dev_minor_invs d) gnu_dev_minor_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply gnu_dev_minor_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  rename PRE into D.
  repeat arm8_step.
  unfold postcondition, dev_minor.
  change 255 with (N.ones 8). rewrite N.land_ones, N.lor_comm. reflexivity.
Qed.

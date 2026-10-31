(* pthread_equal (AArch64 / ARMv8)

   Returns 1 if the two thread IDs are equal, else 0.  On AArch64:
   `cmp x0,x1; cset w0,eq; ret`.

   PROVENANCE: aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
   (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
   symbol pthread_equal at 0x1812e0.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Specification shared with amd64_pthread_equal_proof.v; only the registers
   (X0/X1, AAPCS64) and the step tactic differ.  AArch64 glibc port.
 *)

Require Import Picinae_armv8.
Require Import pthread_equal_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith List.
Import ListNotations.
Open Scope N.

Theorem pthread_equal_nwc: forall s2 s1, pthread_equal_arm8 s1 = pthread_equal_arm8 s2.
Proof. reflexivity. Qed.

Theorem pthread_equal_welltyped: welltyped_prog arm8typctx pthread_equal_arm8.
Proof. Picinae_typecheck. Qed.

Theorem pthread_equal_preserves_memory:
  forall_endstates pthread_equal_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* Modular subtraction is zero exactly when the (in-range) operands are equal. *)
Lemma msub_eqb_0: forall a b, a < 2^64 -> b < 2^64 -> (msub 64 a b =? 0) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (N.eqb_spec a b) as [E|E].
  - subst. rewrite msub_diag. reflexivity.
  - apply N.eqb_neq. intro H. apply E.
    pose proof (add_msub 64 b a) as AM. rewrite H, N.add_0_r in AM.
    rewrite (N.mod_small b), (N.mod_small a) in AM by assumption. symmetry; exact AM.
Qed.

Definition pthread_equal_exit (t:trace) :=
  match t with (Addr 8,_)::_ => true | _ => false end.

Definition postcondition (tid1 tid2:N) (s:store) :=
  s R_X0 = (if tid1 =? tid2 then 1 else 0).

Definition pthread_equal_invs (tid1 tid2:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_X0 = tid1 /\ s R_X1 = tid2)
  | 8 => Some (postcondition tid1 tid2 s)
  | _ => None
  end | _ => None end.

Theorem pthread_equal_correct:
  forall s t s' x' tid1 tid2
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (T1: s R_X0 = tid1) (T2: s R_X1 = tid2),
  satisfies_all pthread_equal_arm8 (pthread_equal_invs tid1 tid2) pthread_equal_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply pthread_equal_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [T1 T2].
  assert (B1: tid1 < 2^64) by (rewrite <- T1; apply (MDL1 R_X0 64); reflexivity).
  assert (B2: tid2 < 2^64) by (rewrite <- T2; apply (MDL1 R_X1 64); reflexivity).
  repeat arm8_step.
  unfold postcondition. reflexivity.
Qed.

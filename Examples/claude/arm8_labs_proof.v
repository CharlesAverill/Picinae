(* labs (AArch64 / ARMv8) -- absolute value of a long

   On AArch64: `cmp x0,#0; cneg x0,x0,lt; ret` (negate if negative).

   PROVENANCE: aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
   (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
   symbol labs at 0x13d820.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Specification shared with amd64_labs_proof.v (RAX/X0 = |j| mod 2^64, exact
   |j| except at LONG_MIN).  AArch64 glibc port.
 *)

Require Import Picinae_armv8.
Require Import labs_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith List.
Import ListNotations.
Open Scope N.

Theorem labs_nwc: forall s2 s1, labs_arm8 s1 = labs_arm8 s2.
Proof. reflexivity. Qed.

Theorem labs_welltyped: welltyped_prog arm8typctx labs_arm8.
Proof. Picinae_typecheck. Qed.

Theorem labs_preserves_memory:
  forall_endstates labs_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* Arch-neutral: cneg produces |j| in both the negate and the keep branch. *)
Lemma labs_math: forall n, n < 2^64 ->
  (slt 64 n 0 = true  -> msub 64 0 n = ofZ 64 (Z.abs (toZ 64 n))) /\
  (slt 64 n 0 = false -> n = ofZ 64 (Z.abs (toZ 64 n))).
Proof.
  intros n Hn. set (j := toZ 64 n).
  assert (V: msub 64 0 n = ofZ 64 (- j)) by (rewrite msub_sbop; reflexivity).
  assert (N: ofZ 64 j = n) by (unfold j; rewrite ofZ_toZ; apply N.mod_small; exact Hn).
  unfold slt. change (toZ 64 0) with 0%Z. fold j.
  split; intro BC.
  - apply Z.ltb_lt in BC. rewrite V, Z.abs_neq by lia. reflexivity.
  - apply Z.ltb_ge in BC. rewrite Z.abs_eq by lia. symmetry; exact N.
Qed.

Definition labs_exit (t:trace) :=
  match t with (Addr 8,_)::_ => true | _ => false end.

Definition postcondition (j:Z) (s:store) :=
  s R_X0 = ofZ 64 (Z.abs j).

Definition labs_invs (j:Z) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (toZ 64 (s R_X0) = j)
  | 8 => Some (postcondition j s)
  | _ => None
  end | _ => None end.

Theorem labs_correct:
  forall s t s' x' j
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (J: toZ 64 (s R_X0) = j),
  satisfies_all labs_arm8 (labs_invs j) labs_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply labs_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into J.
  assert (B: s1 R_X0 < 2^64) by (apply (MDL1 R_X0 64); reflexivity).
  pose proof (labs_math (s1 R_X0) B) as [LM1 LM2]. rewrite J in LM1, LM2.
  assert (Z0: s1 R_X0 ⊖ 0 = s1 R_X0).
  { unfold msub. change (0 mod 2^64) with 0. rewrite N.sub_0_r.
    replace (s1 R_X0 + 2^64) with (s1 R_X0 + 1 * 2^64) by lia.
    rewrite N.mod_add by discriminate. apply N.mod_small; exact B. }
  repeat arm8_step.
  all: unfold postcondition; rewrite Z0 in *.
  - (* negate branch: slt true *)
    destruct (slt 64 (s1 R_X0) 0) eqn:SL; [ apply LM1; reflexivity | cbn in BC; discriminate ].
  - (* keep branch: slt false *)
    destruct (slt 64 (s1 R_X0) 0) eqn:SL; [ cbn in BC; discriminate | apply LM2; reflexivity ].
Qed.

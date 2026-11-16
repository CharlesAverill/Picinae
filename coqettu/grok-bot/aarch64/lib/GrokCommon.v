(* GrokCommon: shared definitions, lemmas and tactics for the Grok Bot
   (agent coqettu) proofs of musl-1.2.6-r6 aarch64 functions.

   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Debugging helpers                                                       *)

(* Print every hypothesis and the goal (reverts the context, so only use it
   on a branch that is then admitted while developing). *)
Ltac dump_ctx :=
  match goal with |- ?G => idtac "GOAL:" G end;
  repeat match goal with H: ?T |- _ => idtac H ":" T; revert H end.

(* ---------------------------------------------------------------------- *)
(* Syntactic tactics that never unfold memory (see correctness skill §3). *)

Ltac sassumption := match goal with H: ?T |- ?G => constr_eq T G; exact H end.
Ltac sreflexivity := match goal with |- ?a = ?b => constr_eq a b; reflexivity end.

(* ---------------------------------------------------------------------- *)
(* Bound facts                                                             *)

Lemma getmem_lt: ∀ w e len m a n, len * 8 <= n -> getmem w e len m a < 2^n.
Proof.
  intros. eapply N.lt_le_trans. apply getmem_bound. apply N.pow_le_mono_r. discriminate. assumption.
Qed.

Lemma byte_lt32: ∀ m a, m Ⓑ[a] < 2^32.
Proof. intros. apply getmem_lt. discriminate. Qed.
Lemma byte_lt64: ∀ m a, m Ⓑ[a] < 2^64.
Proof. intros. apply getmem_lt. discriminate. Qed.
Lemma dword_lt32: ∀ m a, m Ⓓ[a] < 2^32.
Proof. intros. apply getmem_lt. discriminate. Qed.
Lemma dword_lt64: ∀ m a, m Ⓓ[a] < 2^64.
Proof. intros. apply getmem_lt. discriminate. Qed.
Lemma qword_lt64: ∀ m a, m Ⓠ[a] < 2^64.
Proof. intros. apply getmem_lt. discriminate. Qed.

(* Get the bit-width bound of a register from a typing model. *)
Lemma reg64_lt: ∀ s r, models arm8typctx s -> arm8typctx r = Some 64 -> s r < 2^64.
Proof. intros s r MDL H. exact (MDL r 64 H). Qed.

(* ---------------------------------------------------------------------- *)
(* Branch-condition normalisation.  The lifter's cbz/cbnz on a W register
   produce conditions of the form  negb ((x >> 0) mod 2^32 =? 0) = b.       *)

Lemma cbnz32_true: ∀ x, x < 2^32 -> negb ((x >> 0) mod 2^32 =? 0) = true -> x ≠ 0.
Proof.
  intros x LT H. rewrite N.shiftr_0_r, N.mod_small in H by exact LT.
  apply Bool.negb_true_iff, N.eqb_neq in H. exact H.
Qed.

Lemma cbnz32_false: ∀ x, x < 2^32 -> negb ((x >> 0) mod 2^32 =? 0) = false -> x = 0.
Proof.
  intros x LT H. rewrite N.shiftr_0_r, N.mod_small in H by exact LT.
  apply Bool.negb_false_iff, N.eqb_eq in H. exact H.
Qed.

(* ---------------------------------------------------------------------- *)
(* Modular address arithmetic                                              *)

Lemma add_mod_r: ∀ a b, (a + b mod 2^64) mod 2^64 = (a + b) mod 2^64.
Proof. intros. rewrite N.Div0.add_mod_idemp_r. reflexivity. Qed.

Lemma add_mod_l: ∀ a b, (a mod 2^64 + b) mod 2^64 = (a + b) mod 2^64.
Proof. intros. rewrite N.Div0.add_mod_idemp_l. reflexivity. Qed.

(* Wrapping a scaled index: (p + c*k) where c*2^n = 2^64. *)
Lemma add_wrap_full: ∀ p, (p + 2^64) mod 2^64 = p mod 2^64.
Proof.
  intros. rewrite <- (N.mul_1_l (2^64)) at 1. rewrite N.Div0.mod_add. reflexivity.
Qed.

(* Arithmetic shift of a non-negative 64-bit value is a logical shift. *)
Lemma ashiftr64_small: ∀ x n, x < 2^63 -> ashiftr 64 x n = x >> n.
Proof.
  intros. rewrite ashiftr_nonneg; rewrite N.mod_small; try assumption; try reflexivity.
  1,2: eapply N.lt_trans; [eassumption|reflexivity].
Qed.

(* ---------------------------------------------------------------------- *)
(* AAPCS64 frame facts.                                                    *)

(* Registers that AAPCS64 requires a callee to preserve: X19-X28, the frame
   pointer X29, SP, and (the low 64 bits of) V8-V15, which Picinae models as
   R_Z8-R_Z15.  Memory and page permissions are added for leaf functions that
   write nothing. *)
Definition aapcs64_callee_saved : list arm8var :=
  R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 ::
  R_X27 :: R_X28 :: R_X29 :: R_SP ::
  R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil.

(* Prove  ∀ r, In r L -> forall_endstates p (fun _ s _ s' => s r = s' r)
   for a program that never assigns any register in L. *)
Ltac prove_regs_noassign :=
  let r := fresh "r" in let H := fresh "H" in
  intros r H; simpl in H;
  repeat (destruct H as [H|H]; [subst r; apply noassign_prog_same; prove_noassign|]);
  contradiction.

(* ---------------------------------------------------------------------- *)
(* Modular subtraction                                                     *)

Lemma msub_small: ∀ w x y, y <= x -> x < 2^w -> msub w x y = x - y.
Proof.
  intros w x y LE LT.
  assert (Y: y < 2^w) by (eapply N.le_lt_trans; eassumption).
  rewrite msub_nowrap; rewrite !(N.mod_small x), !(N.mod_small y); try assumption; reflexivity.
Qed.

(* The 32-bit difference of two bytes, read as a signed int, is the
   mathematical difference.  This is how "returns <0, 0, >0" is checked. *)
Lemma msub32_bytes_toZ:
  ∀ b1 b2, b1 < 2^8 -> b2 < 2^8 -> toZ 32 (msub 32 b1 b2) = (Z.of_N b1 - Z.of_N b2)%Z.
Proof.
  intros b1 b2 H1 H2.
  assert (H1': b1 < 2^32) by (eapply N.lt_le_trans; [eassumption|discriminate]).
  assert (H2': b2 < 2^32) by (eapply N.lt_le_trans; [eassumption|discriminate]).
  destruct (N.le_gt_cases b2 b1) as [LE|GT].
  - rewrite msub_small by assumption.
    rewrite (proj1 (toZ_nonneg _ _)); rewrite N.mod_small;
      try change (N.pred 32) with 31; try lia.
  - rewrite msub_wrap by (rewrite !N.mod_small by assumption; assumption).
    rewrite !(N.mod_small b1), !(N.mod_small b2) by assumption.
    rewrite (proj1 (toZ_neg _ _)); rewrite N.mod_small;
      try change (N.pred (N.pos 32)) with 31; try lia.
Qed.

(* Same for 32-bit words compared as *unsigned* values is not a difference;
   for byte-sized operands the sign of the result is the comparison. *)
Lemma msub32_bytes_sign:
  ∀ b1 b2, b1 < 2^8 -> b2 < 2^8 -> (toZ 32%N (msub 32%N b1 b2) ?= 0)%Z = (b1 ?= b2).
Proof.
  intros. rewrite msub32_bytes_toZ by assumption.
  rewrite <- Z.compare_sub. apply N2Z.inj_compare.
Qed.

Lemma byte_lt8: ∀ m a, m Ⓑ[a] < 2^8.
Proof. intros. apply getmem_lt. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Common memory predicates                                                *)

(* The first k bytes at p and q agree. *)
Definition mem_eq (m:memory) (p q:addr) (k:N) := ∀ i, i < k -> m Ⓑ[p + i] = m Ⓑ[q + i].

(* The first k bytes at p are all non-zero. *)
Definition nilfree (m:memory) (p:addr) (k:N) := ∀ i, i < k -> m Ⓑ[p + i] ≠ 0.

Lemma mem_eq_0: ∀ m p q, mem_eq m p q 0.
Proof. intros m p q i H. destruct i; discriminate. Qed.

Lemma mem_eq_succ: ∀ m p q k, mem_eq m p q k -> m Ⓑ[p + k] = m Ⓑ[q + k] -> mem_eq m p q (k+1).
Proof.
  intros m p q k H E i Hi. destruct (N.lt_ge_cases i k). apply H; assumption.
  replace i with k by lia. exact E.
Qed.

Lemma nilfree_0: ∀ m p, nilfree m p 0.
Proof. intros m p i H. destruct i; discriminate. Qed.

Lemma nilfree_succ: ∀ m p k, nilfree m p k -> m Ⓑ[p + k] ≠ 0 -> nilfree m p (k+1).
Proof.
  intros m p k H E i Hi. destruct (N.lt_ge_cases i k). apply H; assumption.
  replace i with k by lia. exact E.
Qed.

Lemma nilfree_mono: ∀ m p k k', k' <= k -> nilfree m p k -> nilfree m p k'.
Proof. intros m p k k' LE H i Hi. apply H. lia. Qed.

Lemma mem_eq_mono: ∀ m p q k k', k' <= k -> mem_eq m p q k -> mem_eq m p q k'.
Proof. intros m p q k k' LE H i Hi. apply H. lia. Qed.

(* Advancing a pointer register by c: X1 = p ⊕ k  ~>  c + p ⊕ k = p ⊕ ((k+c) mod 2^64). *)
Lemma ptr_adv: ∀ p k c, (c + p + k) mod 2^64 = (p + (k + c) mod 2^64) mod 2^64.
Proof. intros. rewrite add_mod_r. f_equal. lia. Qed.

Lemma mod64_le: ∀ k, k mod 2^64 <= k.
Proof. intros. apply N.Div0.mod_le. Qed.

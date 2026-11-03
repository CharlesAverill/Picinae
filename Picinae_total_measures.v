(* Picinae: Platform In Coq for INstruction Analysis of Executables
   Reusable termination measures for binary counters and string scans.

   These rules only establish well-foundedness and arithmetic decrease.
   Finite, enabled execution between checkpoints is still required by
   PicinaeTotal.prove_total_invs.
 *)

Require Export Picinae_theory.
From Stdlib Require Import NArith Lia Wellfounded Relation_Operators.
Open Scope N_scope.

(* The first component has priority.  A decrease there permits an arbitrary
   reset of the second component, as at the end of an inner wcsspn loop.
   Constructors left_slex and right_slex discharge individual decreases. *)
Definition Nlex := slexprod N N N.lt N.lt.
Definition Nlex3 := slexprod N (N*N) N.lt Nlex.

Theorem Nlex_wf: well_founded Nlex.
Proof. apply wf_slexprod; exact N.lt_wf_0. Qed.

Theorem Nlex3_wf: well_founded Nlex3.
Proof. apply wf_slexprod; [exact N.lt_wf_0|exact Nlex_wf]. Qed.

(* Turn increasing scan indices into decreasing distances.  The upper bound
   prevents truncated subtraction from concealing an exhausted counter. *)
Theorem Nremaining_decrease:
  forall bound i j, i < j <= bound -> bound - j < bound - i.
Proof. intros. lia. Qed.

(* Nested scans may reset the inner index whenever the outer index advances.
   The inner bound is needed only on an inner-loop transition. *)
Theorem Nlex_remaining_decrease:
  forall outer_bound inner_bound i j i' j',
  (i < i' <= outer_bound \/ (i = i' /\ j < j' <= inner_bound)) ->
  Nlex (outer_bound-i', inner_bound-j')
       (outer_bound-i, inner_bound-j).
Proof.
  intros outer_bound inner_bound i j i' j' [OUTER | [EQ INNER]].
    apply left_slex, Nremaining_decrease, OUTER.
    subst i'. apply right_slex, Nremaining_decrease, INNER.
Qed.

(* A bounded phase can be packed below a counter into one N rank.  This suits
   memset's sequential loops: decrease the counter within a phase, and decrease
   the phase when moving to the next loop.  Only the NEW phase needs a bound. *)
Definition Nphase_rank radix counter phase := radix * counter + phase.

Theorem Nphase_decrease:
  forall radix counter counter' phase phase',
  phase' < radix ->
  (counter' < counter \/ (counter' = counter /\ phase' < phase)) ->
  Nphase_rank radix counter' phase' < Nphase_rank radix counter phase.
Proof.
  unfold Nphase_rank. intros radix counter counter' phase phase' BOUND DEC.
  destruct DEC as [DEC | [EQ DEC]]; nia.
Qed.

(* A scan can advance its index and reset its phase, or keep its index and
   decrease its phase.  Positivity of radix follows from phase' < radix. *)
Theorem Nphase_remaining_decrease:
  forall radix bound i i' phase phase',
  i <= i' <= bound -> phase' < radix ->
  (i < i' \/ phase' < phase) ->
  Nphase_rank radix (bound-i') phase' <
  Nphase_rank radix (bound-i) phase.
Proof.
  intros radix bound i i' phase phase' RANGE BOUND DEC.
  apply Nphase_decrease; [exact BOUND|].
  destruct (N.eq_dec i i') as [EQ | NE].
    right. subst i'. split; [reflexivity|lia].
    left. apply Nremaining_decrease. lia.
Qed.

(* Picinae_theory already provides lt_msub_l for a modular countdown and
   msub_nowrap for ordinary subtraction.  Here the counter is instead a
   modular pointer and the rank is its distance to a fixed target.  The pointer
   itself may wrap; STEP forbids wrapping or passing the remaining distance. *)
Theorem msub_advance_exact:
  forall w target current step,
  step <= msub w target current ->
  msub w target ((current+step) mod 2^w) =
  msub w target current - step.
Proof.
  intros w target current step STEP.
  assert (STEPW: step < 2^w).
    eapply N.le_lt_trans; [exact STEP|apply msub_lt].
  rewrite msub_mod_r, msub_add_distr by reflexivity.
  rewrite msub_nowrap.
    rewrite N.mod_small by apply msub_lt.
    rewrite N.mod_small by exact STEPW. reflexivity.
    rewrite (N.mod_small step _ STEPW), N.mod_small by apply msub_lt.
    exact STEP.
Qed.

Theorem msub_advance_decrease:
  forall w target current step,
  0 < step <= msub w target current ->
  msub w target ((current+step) mod 2^w) < msub w target current.
Proof.
  intros w target current step [POS STEP].
  rewrite msub_advance_exact by exact STEP.
  apply N.sub_lt; assumption.
Qed.

(* Custom invariants in the examples describe non-nil prefixes differently
   (bytes, wide characters, or equal nonzero character pairs).  An arbitrary
   reader handles all of them, including strided or modular addresses.  A known
   terminator need not be the FIRST terminator and needs no address bound.
   For standard nilfree/wnilfree, the existing nilfree_le_zero/wnilfree_le_zero
   already give the corresponding prefix bound. *)
Theorem prefix_terminator_bound {A:Type}:
  forall (read:N -> A) zero bound k,
  read bound = zero ->
  (forall i, i < k -> read i <> zero) ->
  k <= bound.
Proof.
  intros read zero bound k NIL PREFIX.
  destruct (N.le_gt_cases k bound) as [LE | GT]; [exact LE|].
  exfalso. apply (PREFIX bound GT), NIL.
Qed.

(* The current nonzero character is what licenses another scan iteration. *)
Theorem prefix_terminator_progress {A:Type}:
  forall (read:N -> A) zero bound k,
  read bound = zero ->
  (forall i, i < k -> read i <> zero) ->
  read k <> zero -> k < bound.
Proof.
  intros read zero bound k NIL PREFIX NONZERO.
  assert (LE: k <= bound) by (eapply prefix_terminator_bound; eassumption).
  apply N.lt_eq_cases in LE. destruct LE as [LT | EQ]; [exact LT|].
  subst k. contradiction.
Qed.

(* In particular, successful byte/block scans strictly reduce the distance
   to a known terminator.  PREFIX must cover every newly skipped character;
   checking only the last character of a block is insufficient. *)
Theorem prefix_terminator_remaining_decrease {A:Type}:
  forall (read:N -> A) zero bound k step,
  read bound = zero ->
  (forall i, i < k+step -> read i <> zero) ->
  0 < step -> bound-(k+step) < bound-k.
Proof.
  intros read zero bound k step NIL PREFIX POS.
  assert (LE: k+step <= bound) by
    (eapply prefix_terminator_bound; eassumption).
  apply Nremaining_decrease. lia.
Qed.

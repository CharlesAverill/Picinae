From Stdlib Require Import Utf8 NArith ZArith Lia List Btauto.
Require Import Picinae_armv8.
From Grok.lifted Require Import ffsl_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl.
Import ARM8Notations.
Open Scope N.

Theorem ffsl_welltyped: welltyped_prog arm8typctx ffsl_armv8.
Proof. Picinae_typecheck. Qed.


Lemma lowest_bit: ∀ x, x ≠ 0 -> ∃ t, N.testbit x t = true /\ ∀ j, j < t -> N.testbit x j = false.
Proof.
  intro x. induction x as [x IH] using (well_founded_induction N.lt_wf_0). intro NZ.
  destruct (N.odd x) eqn:O.
  - exists 0. split. rewrite N.bit0_odd. exact O. intros j J. lia.
  - assert (H2: x / 2 ≠ 0).
    { intro Z. apply NZ. pose proof (N.div_mod x 2 ltac:(discriminate)) as D.
      rewrite Z in D. rewrite <- N.bit0_mod, N.bit0_odd, O in D. simpl in D. lia. }
    destruct (IH (x/2) ltac:(apply N.div_lt; lia) H2) as (t & T & L).
    exists (N.succ t). rewrite N.div2_bits in T. split. exact T.
    intros j J. destruct (N.eq_dec j 0) as [->|JN].
    + rewrite N.bit0_odd. exact O.
    + replace j with (N.succ (N.pred j)) by lia. rewrite <- N.div2_bits.
      apply L. lia.
Qed.

Lemma scast_low32: ∀ x j, j < 32 -> N.testbit (scast 32 64 x) j = N.testbit x j.
Proof.
  intros x j J.
  rewrite <- (N.mod_pow2_bits_low (scast 32 64 x) 32 j J), <- (N.mod_pow2_bits_low x 32 j J).
  f_equal. pose proof (ofZ_toZ_bitcast 32 32 x ltac:(reflexivity)) as E.
  unfold scast, ofZ in *. rewrite <- E. apply N2Z.inj.
  rewrite N2Z.inj_mod, !Z2N.id by (apply Z.mod_pos_bound; lia).
  change (Z.of_N (2^32)) with (2^32)%Z. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
  apply Z.mod_mod_divide; first [ (exists (2^32)%Z; reflexivity) | lia ].
Qed.

Lemma size_rev: ∀ e y t, (∀ j, N.testbit e j = (j <? 64) && N.testbit y (63 - j)) ->
  t < 64 -> N.testbit y t = true -> (∀ j, j < t -> N.testbit y j = false) -> N.size e = 64 - t.
Proof.
  intros e y t RB T Y L.
  assert (B: N.testbit e (63 - t) = true).
  { rewrite RB. replace (63 - (63 - t)) with t by lia. rewrite Y. apply N.ltb_lt in T.
    replace (63 - t <? 64) with true. reflexivity. symmetry. apply N.ltb_lt. lia. }
  assert (NZ: e ≠ 0) by (intro Z; rewrite Z, N.bits_0 in B; discriminate).
  rewrite N.size_log2 by exact NZ.
  rewrite (N.log2_bits_unique e (63 - t)). lia. exact B.
  intros m M. rewrite RB. destruct (m <? 64) eqn:MM; [|reflexivity].
  apply N.ltb_lt in MM. rewrite Bool.andb_true_l. apply L. lia.
Qed.

(* ffsl result: 0 if no bit of the long is set, else 1 + index of the lowest set bit. *)
Definition ffsl_spec (i r:N) :=
  (i = 0 /\ r = 0) \/
  (∃ t, t < 64 /\ N.testbit i t = true /\ (∀ j, j < t -> N.testbit i j = false) /\ r = t + 1).

Section Invariants.
  Variables (sp mem raddr i : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x13b2ac => Inv 0 (s R_X0 = i /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x13b2bc => Post 0 (ffsl_spec i (s R_X0 mod 2^32) /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ffsl_exits := make_exits 0 ffsl_armv8 invs.
  Definition ffsl_invs := make_invs 0 ffsl_armv8 invs.
End Invariants.

Theorem ffsl_partial_correctness:
  ∀ prog s sp mem raddr i t xs'
    (PROG: ffsl_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x13b2ac, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = i),
  satisfies_all prog (ffsl_invs sp mem raddr i) (ffsl_exits sp mem raddr i) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ffsl_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ffsl_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ffsl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  pose proof (MDL1 R_X0 64 eq_refl) as Y64. rewrite X0 in Y64. simpl in Y64.
  repeat arm8_step.
  all: try (apply N.eqb_eq in BC; splits; try assumption; left; split; [exact BC | reflexivity]).
  all: apply N.eqb_neq in BC.
  all: match goal with |- context [ N.size ?E ] =>
      let r := reify_bx i E in change E with (bden i r);
      pose proof (brev_check_ok r i Y64 ltac:(vm_compute; reflexivity)) as RB
    end.
  all: destruct (lowest_bit _ BC) as (b & T & L).
  all: assert (B64: b < 64) by (destruct (N.lt_ge_cases b 64); [assumption | rewrite testbit_big64 in T by assumption; discriminate]).
  all: rewrite (size_rev _ i b RB B64 T L).
  all: splits; try assumption; right; exists b; splits; try assumption.
  all: rewrite msub_small by lia; try rewrite N.mod_small by lia; lia.
Qed.

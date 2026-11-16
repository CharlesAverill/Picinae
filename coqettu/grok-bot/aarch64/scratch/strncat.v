From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strncat_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame.
From Grok.scratch Require Import strncat_base.
Import ARM8Notations.
Open Scope N.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Lemma first_zero_unique: ∀ (f g: N -> N) L1 L2,
  (∀ i, i < L1 -> f i ≠ 0) -> f L1 = 0 -> (∀ i, i < L2 -> g i ≠ 0) -> g L2 = 0 ->
  (∀ i, i <= L1 -> g i = f i) -> L1 = L2.
Proof.
  intros f g L1 L2 F1 F0 G1 G0 E.
  destruct (N.lt_trichotomy L1 L2) as [H|[H|H]]; [|exact H|].
  - exfalso. apply (G1 L1 H). rewrite E by lia. exact F0.
  - exfalso. apply (F1 L2 H). rewrite <- E by lia. exact G0.
Qed.

Lemma add_mod_inj: ∀ q k K, k < 2^64 -> K < 2^64 -> (q + k) mod 2^64 = (q + K) mod 2^64 -> k = K.
Proof.
  intros q k K Hk HK E.
  pose proof (N.div_mod (q+k) (2^64) ltac:(discriminate)) as A.
  pose proof (N.div_mod (q+K) (2^64) ltac:(discriminate)) as B.
  rewrite E in A. set (r := (q + K) mod 2^64) in *.
  set (a := (q+k)/2^64) in *. set (b := (q+K)/2^64) in *. change (2^64) with 18446744073709551616 in *. nia.
Qed.

Theorem strncat_partial_correctness:
  ∀ prog s sp mem raddr d q n x19 x20 x21 x29 Ld K t xs'
    (PRE0: strncat_pre sp mem d q n Ld K)
    (P1: strncat_armv8.strncat_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f0b4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n)
    (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X21: s R_X21 = x21) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr d q n x19 x20 x21 x29 Ld K) (exits1 sp mem raddr d q n x19 x20 x21 x29 Ld K) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X20 64 eq_refl) as W20. rewrite X20 in W20. simpl in W20.
  pose proof (MDL R_X21 64 eq_refl) as W21. rewrite X21 in W21. simpl in W21.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  assert (PP: strncat_prog ⊆2 prog) by (apply strncat_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=strncat_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X20 X21 X29 START PRE0 W19 W20 W21 W29 W30.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncat_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W19 W20 W21 W29 W30. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X20 & X21 & X29).
    do 8 arm8_step.
    set (s2 := update _ _ _).
    eapply models_after_steps. eassumption. apply strncat_prog_welltyped. intro MDL2.
    eapply (perform_call 0). reflexivity.
    intros. eapply strlen_correct_in_strncat with (q:=q) (n:=n) (Ld:=Ld) (K:=K); first [ exact (fun _ _ _ H => H) | eassumption ].
    reflexivity.
    intros.
    unfold s2 in PRE. psimpl in PRE.
    assert (MDL': models arm8typctx s').
      eapply preservation_exec_prog; try eassumption. apply strncat_prog_welltyped.
    clearbody s2.
    clear - PRE MDL' PRE0 W19 W20 W21 W29 W30.
    rename MDL' into MDL. rename s' into s0.
    destruct_inv 64 PRE.
    destruct PRE as (L & LLT & R0 & NF & ZL & MEM & SP & X30 & X29 & X19 & X20 & X21).
    destruct PRE0 as (NF0 & Z0 & KN & N64 & NFq & ZK & SP48 & SPlt & BD & BQ & DISJ).
    assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
    apply WW in W19, W20, W21, W29, W30. clear WW.
    change (2^64) with 18446744073709551616 in *.
    assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
    set (C := ncat_frame sp mem raddr x19 x20 x21 x29).
    assert (CB: ∀ a, a + 1 <= sp - 48 -> C Ⓑ[a] = mem Ⓑ[a]).
    { intros a A. unfold C, ncat_frame. memsimp. reflexivity. }
    assert (RD: ∀ i, i <= K -> bcp C (d+Ld) q (N.to_nat i) Ⓑ[q+i] = mem Ⓑ[q+i]).
    { intros i I. rewrite <- CB by lia. destruct DISJ as [DJ|DJ].
      - apply bcp_read_below; rewrite ?N2Nat.id; L64.
      - apply bcp_read_above; rewrite ?N2Nat.id; L64. }
    assert (FR: ∀ j v a, j <= K -> sp - 48 <= a -> a + 8 <= sp ->
       (setmem 64 LittleE 1 (bcp C (d+Ld) q (N.to_nat j)) (d+Ld+j) v) Ⓠ[a] = C Ⓠ[a]).
    { intros j v a J A1 A2. rewrite getmem_setmem_below by L64. apply bcp_read_above; rewrite ?N2Nat.id; L64. }
    assert (Q48: C Ⓠ[sp - 48] = x29) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q40: C Ⓠ[sp - 40] = raddr) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q32: C Ⓠ[sp - 32] = x19) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q24: C Ⓠ[sp - 24] = x20) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q16: C Ⓠ[sp - 16] = x21) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    rewrite !(MS sp) in * by lia.
    change (mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 16 := x21] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20]) with C in *.
    assert (LE: Ld = L).
    { apply (first_zero_unique (fun i => mem Ⓑ[d+i]) (fun i => C Ⓑ[d+i])); cbv beta; try assumption.
      intros i I. apply CB. lia. }
    subst L.
    repeat arm8_step.
    exists 0. splits; try reflexivity; try lia.
    all: first [ (rewrite N.add_0_r; first [assumption | apply N.mod_small; L64]) | (rewrite MEM; reflexivity) | assumption ].
  - destruct PRE as (k & KK & X0 & X2 & X19 & X20 & X21 & MEM & SP & X29).
    destruct PRE0 as (NF0 & Z0 & KN & N64 & NFq & ZK & SP48 & SPlt & BD & BQ & DISJ).
    assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
    apply WW in W19, W20, W21, W29, W30. clear WW.
    change (2^64) with 18446744073709551616 in *.
    assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
    set (C := ncat_frame sp mem raddr x19 x20 x21 x29).
    assert (CB: ∀ a, a + 1 <= sp - 48 -> C Ⓑ[a] = mem Ⓑ[a]).
    { intros a A. unfold C, ncat_frame. memsimp. reflexivity. }
    assert (RD: ∀ i, i <= K -> bcp C (d+Ld) q (N.to_nat i) Ⓑ[q+i] = mem Ⓑ[q+i]).
    { intros i I. rewrite <- CB by lia. destruct DISJ as [DJ|DJ].
      - apply bcp_read_below; rewrite ?N2Nat.id; L64.
      - apply bcp_read_above; rewrite ?N2Nat.id; L64. }
    assert (FR: ∀ j v a, j <= K -> sp - 48 <= a -> a + 8 <= sp ->
       (setmem 64 LittleE 1 (bcp C (d+Ld) q (N.to_nat j)) (d+Ld+j) v) Ⓠ[a] = C Ⓠ[a]).
    { intros j v a J A1 A2. rewrite getmem_setmem_below by L64. apply bcp_read_above; rewrite ?N2Nat.id; L64. }
    assert (Q48: C Ⓠ[sp - 48] = x29) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q40: C Ⓠ[sp - 40] = raddr) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q32: C Ⓠ[sp - 32] = x19) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q24: C Ⓠ[sp - 24] = x20) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    assert (Q16: C Ⓠ[sp - 16] = x21) by (unfold C, ncat_frame; memsimp; apply N.mod_small; L64).
    repeat grok_step.
    + (* k = n *)
      apply N.eqb_eq in BC. rewrite N.mod_small in BC by lia. assert (EK: k = K) by lia. clear BC. subst k.
      try unfold strncat_post. change (ncat_frame sp mem raddr x19 x20 x21 x29) with C.
      repeat match goal with |- context [(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x+y)) by L64 end.
      replace (16 + (sp - 48)) with (sp - 32) by lia.
      replace (24 + (sp - 48)) with (sp - 24) by lia.
      replace (32 + (sp - 48)) with (sp - 16) by lia.
      replace (8 + (sp - 48)) with (sp - 40) by lia.
      replace (48 + (sp - 48)) with sp by lia.
      rewrite !FR by L64. rewrite Q48, Q40, Q32, Q24, Q16.
      splits; reflexivity.
    + (* copy one more byte *)
      apply N.eqb_neq in BC. rewrite N.mod_small in BC by lia.
      apply cbnz32_true in BC0; [|apply byte_lt32]. rewrite RD in BC0 by lia.
      assert (KLT: k < K).
      { destruct (N.eq_dec k K) as [->|NE]; [|lia]. destruct ZK as [ZK|ZK]; [lia|contradiction]. }
      exists (k+1). splits; try reflexivity; try lia.
      all: first [ (rewrite N.mod_small by L64; lia) | (rewrite bcp_succ; reflexivity) ].
    + (* NUL found *)
      apply cbnz32_false in BC0; [|apply byte_lt32]. rewrite RD in BC0 by lia.
      assert (k = K).
      { destruct (N.lt_ge_cases k K) as [H|H]; [|lia]. exfalso. exact (NFq k H BC0). }
      subst k.
      try unfold strncat_post. change (ncat_frame sp mem raddr x19 x20 x21 x29) with C.
      repeat match goal with |- context [(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x+y)) by L64 end.
      replace (16 + (sp - 48)) with (sp - 32) by lia.
      replace (24 + (sp - 48)) with (sp - 24) by lia.
      replace (32 + (sp - 48)) with (sp - 16) by lia.
      replace (8 + (sp - 48)) with (sp - 40) by lia.
      replace (48 + (sp - 48)) with sp by lia.
      rewrite !FR by L64. rewrite Q48, Q40, Q32, Q24, Q16.
      splits; reflexivity.
Qed.

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strcat_armv8 strcpy_armv8 stpcpy_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame.
Import ARM8Notations.
Open Scope N.

From Grok.scratch Require Import strcat_base.

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

Theorem strcat_partial_correctness:
  ∀ prog s sp mem raddr d q x29 x19 Ld Lq t xs'
    (PRE0: strcat_pre sp mem d q Ld Lq)
    (P3: strcat_armv8.strcat_armv8 ⊆2 prog) (P2: strcpy_armv8.strcpy_armv8 ⊆2 prog)
    (P1: stpcpy_armv8.stpcpy_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eb98, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X29: s R_X29 = x29) (X19: s R_X19 = x19),
  satisfies_all prog (invs3 sp mem raddr d q x29 x19 Ld Lq) (exits3 sp mem raddr d q x29 x19 Ld Lq) (xs'::t).
Proof.
  intros.
  assert (PP: strcat_prog ⊆2 prog) by (apply strcat_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs3, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START PRE0. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as D64. rewrite X0 in D64. simpl in D64.
  pose proof (MDL1 R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL1 R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL1 R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL1 R_X1 64 eq_refl) as Q64. rewrite X1 in Q64. simpl in Q64.
  do 6 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcat_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply strlen_correct_in_strcat with (q := q) (Ld:=Ld) (Lq:=Lq); first [ exact (fun _ _ _ H => H) | eassumption ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcat_prog_welltyped.
  clearbody s2.
  clear - PRE MDL' SP64 D64 Q64 X0 PRE0 W29 W30 W19.
  rename MDL' into MDL. rename s' into s0.
  destruct_inv 64 PRE.
  destruct PRE as (L & LLT & R0 & NF & ZL & MEM & SP & X30 & X29 & X19).
  rename SP into SP1. rename MEM into MEM1.
  do 4 arm8_step.
  rewrite (N.mod_small q) by exact Q64.
  set (s3 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcat_prog_welltyped. intro MDL3.
  eapply (perform_call 2). reflexivity.
  intros. eapply strcpy_correct_in_strcat with (Ld:=Ld) (Lq:=Lq); first [ exact (fun _ _ _ H => H) | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s3 in PRE. unfold strcpy_post, frame_mem in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcat_prog_welltyped.
  clearbody s3.
  clear - PRE MDL' SP64 D64 Q64 NF ZL LLT SP1 MEM1 PRE0 W29 W30 W19.
  rename MDL' into MDL0. rename s' into s4.
  destruct_inv 64 PRE.
  destruct PRE as (k & NZ & Z & MEM & R0 & SP & X29 & X30 & X19).
  destruct PRE0 as (NF0 & Z0 & NFq & Zq & SP80 & SPlt & BD & BQ & DISJ).
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W29, W30, W19. clear WW SP64 D64 Q64.
  change (2^64) with 18446744073709551616 in *.
  assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
  unfold frame_mem in *.
  rewrite !(MS sp) in * by lia. rewrite !(MS (sp - 48)) in * by lia.
  replace (sp - 48 - 32) with (sp - 80) in * by lia.
  replace (sp - 48 - 24) with (sp - 72) in * by lia.
  replace (sp - 48 - 16) with (sp - 64) in * by lia.
  set (C := mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 32 := x19] [Ⓠ sp - 8 := q]) in *.
  set (F := C [Ⓠ sp - 80 := sp - 48] [Ⓠ sp - 72 := 1436604] [Ⓠ sp - 64 := d]) in *.
  assert (CB: ∀ a, a + 1 <= sp - 80 -> C Ⓑ[a] = mem Ⓑ[a]).
  { intros a A. unfold C. rewrite !getmem_setmem_above by L64. reflexivity. }
  assert (FB: ∀ a, a + 1 <= sp - 80 -> F Ⓑ[a] = mem Ⓑ[a]).
  { intros a A. unfold F. rewrite !getmem_setmem_above by L64. apply CB, A. }
  assert (LE: Ld = L).
  { apply (first_zero_unique (fun i => mem Ⓑ[d+i]) (fun i => C Ⓑ[d+i])); cbv beta; try assumption.
    intros i I. apply CB. lia. }
  subst L.
  assert (EQ: (d + Ld) mod 18446744073709551616 = d + Ld) by (apply N.mod_small; lia).
  rewrite EQ in *.
  assert (KE: Lq = k).
  { apply (first_zero_unique (fun i => mem Ⓑ[q+i]) (fun i => bcp F (d+Ld) q (N.to_nat i) Ⓑ[q+i])); cbv beta; try assumption.
    intros i I. rewrite <- FB by lia.
    destruct DISJ as [DJ|DJ].
    - apply bcp_read_below; rewrite ?N2Nat.id; L64.
    - apply bcp_read_above; rewrite ?N2Nat.id; L64. }
  subst k.
  set (M := bcp F (d + Ld) q (N.to_nat (Lq + 1))) in *.
  assert (MQ: ∀ a, sp - 80 <= a -> a + 8 <= sp -> M Ⓠ[a] = F Ⓠ[a]).
  { intros a A1 A2. unfold M. apply bcp_read_above; rewrite ?N2Nat.id; L64. }
  assert (R72: M Ⓠ[sp - 72] = 1436604).
  { rewrite MQ by lia. unfold F. rewrite getmem_setmem_above by L64. rewrite getmem_setmem by L64. reflexivity. }
  assert (R80: M Ⓠ[sp - 80] = sp - 48).
  { rewrite MQ by lia. unfold F. rewrite !getmem_setmem_above by L64. rewrite getmem_setmem by L64. apply N.mod_small. L64. }
  assert (R64: M Ⓠ[sp - 64] = d).
  { rewrite MQ by lia. unfold F. rewrite getmem_setmem by L64. apply N.mod_small. L64. }
  assert (R48: M Ⓠ[sp - 48] = x29).
  { rewrite MQ by lia. unfold F, C. memsimp. apply N.mod_small. L64. }
  assert (R40: M Ⓠ[sp - 40] = raddr).
  { rewrite MQ by lia. unfold F, C. memsimp. apply N.mod_small. L64. }
  assert (R32: M Ⓠ[sp - 32] = x19).
  { rewrite MQ by lia. unfold F, C. memsimp. apply N.mod_small. L64. }
  rewrite R72 in *. rewrite R80 in *. rewrite R64 in *.
  repeat arm8_step.
  unfold frame_mem, cat_frame. rewrite !(MS sp) by lia. rewrite !(MS (sp - 48)) by lia.
  replace (sp - 48 - 32) with (sp - 80) by lia.
  replace (sp - 48 - 24) with (sp - 72) by lia.
  replace (sp - 48 - 16) with (sp - 64) by lia.
  replace (8 + (sp - 48)) with (sp - 40) by lia.
  replace (16 + (sp - 48)) with (sp - 32) by lia.
  replace (48 + (sp - 48)) with sp by lia.
  splits; try assumption; reflexivity.
Qed.

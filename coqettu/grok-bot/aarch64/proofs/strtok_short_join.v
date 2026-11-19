(* strtok, short separator-set path: the join case.  Full header is in strtok_short_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strtok_armv8 strspn_armv8 strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCall GrokKeep.
From Grok.proofs Require Import strtok_defs strtok_callees strtok_join.
From Grok.proofs Require strcspn_defs strspn_defs strspn_proof.
From Grok.proofs Require Import strcspn_short_defs strcspn_short_proof.
From Grok.proofs Require Import strtok_short_defs strtok_short_callees.
Import ARM8Notations.
Open Scope N.

Lemma tks_post_A: ∀ sp mem raddr p c Ks Lc x19 x20 x21 x29 K (s:store),
  s R_SP = sp -> s R_X19 = x19 -> s R_X20 = x20 -> s R_X21 = x21 -> s R_X29 = x29 -> s R_X30 = raddr ->
  s R_X0 = 0 -> p <> 0 -> K = Ks -> (∀ i, i < K -> strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) ->
  tks_out sp s (mem [Ⓠ tk_G := 0]) -> tks_post sp mem raddr p c Ks Lc x19 x20 x21 x29 s.
Proof.
  intros. unfold tks_post. repeat (split; [assumption|]). right. split; [assumption|].
  exists K. split; [lia|]. split; [assumption|]. left. split; [assumption|]. split; assumption.
Qed.

Lemma tks_post_B1: ∀ sp mem raddr p c Ks Lc x19 x20 x21 x29 K K2 (s:store),
  s R_SP = sp -> s R_X19 = x19 -> s R_X20 = x20 -> s R_X21 = x21 -> s R_X29 = x29 -> s R_X30 = raddr ->
  s R_X0 = p + K -> p <> 0 -> K < Ks -> (∀ i, i < K -> strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) ->
  ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K]) -> K + K2 = Ks ->
  (∀ i, i < K2 -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K + i])) ->
  tks_out sp s (mem [Ⓠ tk_G := 0]) -> tks_post sp mem raddr p c Ks Lc x19 x20 x21 x29 s.
Proof.
  intros. unfold tks_post. repeat (split; [assumption|]). right. split; [assumption|].
  exists K. split; [lia|]. split; [assumption|]. right. split; [assumption|]. split; [assumption|]. split; [assumption|].
  exists K2. split; [lia|]. split; [assumption|]. left. split; assumption.
Qed.

Lemma tks_post_B2: ∀ sp mem raddr p c Ks Lc x19 x20 x21 x29 K K2 (s:store),
  s R_SP = sp -> s R_X19 = x19 -> s R_X20 = x20 -> s R_X21 = x21 -> s R_X29 = x29 -> s R_X30 = raddr ->
  s R_X0 = p + K -> p <> 0 -> K < Ks -> (∀ i, i < K -> strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) ->
  ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K]) -> K + K2 < Ks ->
  (∀ i, i < K2 -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K + i])) ->
  strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K + K2]) ->
  tks_out sp s (mem [Ⓠ tk_G := p + K + K2 + 1] [Ⓑ p + K + K2 := 0]) -> tks_post sp mem raddr p c Ks Lc x19 x20 x21 x29 s.
Proof.
  intros. unfold tks_post. repeat (split; [assumption|]). right. split; [assumption|].
  exists K. split; [lia|]. split; [assumption|]. right. split; [assumption|]. split; [assumption|]. split; [assumption|].
  exists K2. split; [lia|]. split; [assumption|]. right. split; [assumption|]. split; assumption.
Qed.

Lemma tks_case_join: ∀ sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 (s1:store) (t:list (exit*store)),
  tks_pre sp mem s0 p c Ks Lc ->
  x19 < 2^64 -> x20 < 2^64 -> x21 < 2^64 -> x29 < 2^64 -> raddr < 2^64 -> s0 < 2^64 -> c < 2^64 ->
  models arm8typctx s1 ->
  tks_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0 Prop (fun _ P => P) (fun _ P => P) True s1 0x15f7e0 ->
  nextinv tks_prog (tks_invs4 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0)
                  (tks_exits4 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0) false ((Addr 0x15f7e0, s1) :: t).
Proof.
  intros sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 s1 t PRE0 W19 W20 W21 W29 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (NZ & X19 & X1 & X21 & SP & X29 & MEM).
  destruct PRE0 as (SEL & GB & S2 & [PZ|(NFp & Zp & NFc & Zc & L2 & R1 & R2 & BP & BCl)]); [exfalso; exact (NZ PZ)|].
  clear SEL. unfold tk_G in GB.
  do 3 arm8_step.
  assert (FRA: ∀ a, a < sp - 176 -> tks_FR sp mem raddr x19 x20 x21 x29 Ⓑ[a] = mem Ⓑ[a]).
  { intros a A. unfold tks_FR, tk_frame. apply tk_FR_out; clear - A GB S2; L64. }
  assert (MRA: ∀ a, a < sp - 176 -> mem Ⓑ[a] = tks_FR sp mem raddr x19 x20 x21 x29 Ⓑ[a]).
  { intros a A. symmetry. apply FRA, A. }
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply tks_prog_welltyped. intro MDL2.
  set (TI := tks_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0).
  apply (perform_call 3 4 eq_refl TI TI).
  { intros tt xx EE.

    refine (strspn_correct_in_strtok_short sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0 s2 tt xx EE MDL2 _ _ _ _ _ _ _).
    { unfold strspn_defs.ss_pre. rewrite (msub_small 64 sp 64) by (clear - GB S2; L64).
      split. { apply (agree_nilfree mem _ p Ks (sp - 176) MRA); [clear - BP; L64 | exact NFp]. }
      split. { rewrite FRA by (clear - BP; L64). exact Zp. }
      split. { apply (agree_nilfree mem _ c Lc (sp - 176) MRA); [clear - BCl; L64 | exact NFc]. }
      split. { rewrite FRA by (clear - BCl; L64). exact Zc. }
      split. { rewrite (agree_X _ _ _ (sp - 176) FRA) by (clear - GB; L64). exact R1. }
      split. { rewrite (agree_X _ _ _ (sp - 176) FRA) by (clear - GB; L64). exact R2. }
      clear - GB S2 BP BCl. L64. }
    all: unfold s2; simpl_stores.
    exact SP. exact MEM. reflexivity. reflexivity. reflexivity.
    unfold keepl_st, tks_L. simpl fold_right. cbn [fst snd].
    exact (conj eq_refl (conj eq_refl (conj X21 (conj X29 I)))). }
  { reflexivity. }
  intros a' s' t2 ENTRY XP UT PRE.
  destruct_inv 64 PRE.
  destruct PRE as (((K & KK & R0 & CI & KE) & RSP & R30 & MO) & KL).
  unfold keepl_st, tks_L in KL. simpl fold_right in KL. cbn [fst snd] in KL.
  destruct KL as (K19 & K20 & K21 & K29 & _).
  clearbody s2. clear MDL2 X19 X1 X21 X29 SP MEM.
  rewrite app_assoc. eapply models_after_steps. exact MDL1. apply tks_prog_welltyped. intro MDL3. rewrite <- app_assoc.
  clear MDL1.
  assert (BY: s' V_MEM64 Ⓑ[p + K] = mem Ⓑ[p + K]).
  { rewrite MO; [apply FRA|..]; rewrite ?(msub_small 64 sp 64) by (clear - GB S2; L64); clear - BP KK S2 GB; L64. }
  assert (OUT3: ∀ a, a < 2^64 -> (a < sp - 176 \/ sp <= a) -> s' V_MEM64 Ⓑ[a] = mem Ⓑ[a]).
  { intros a A O. rewrite MO by (rewrite ?(msub_small 64 sp 64) by (clear - GB S2; L64); clear - A O GB S2; L64).
    unfold tks_FR, tk_frame. apply tk_FR_out; clear - A O GB S2; L64. }
  assert (FRM: ∀ a, sp - 64 <= a -> a < sp -> s' V_MEM64 Ⓑ[a] = tk_frame sp mem raddr x19 x20 x21 x29 Ⓑ[a]).
  { intros a A1 A2. apply MO; rewrite ?(msub_small 64 sp 64) by (clear - GB S2; L64); clear - A1 A2 GB S2; L64. }
  assert (PK: p ⊕ K = p + K) by (apply N.mod_small; clear - BP KK S2; L64). do 4 arm8_step.
  all: rewrite BY in BC.
  1: repeat arm8_step.
  1: match goal with |- context [tks_out _ ?st _] => apply (tks_post_A sp mem raddr p c Ks Lc x19 x20 x21 x29 K st) end.
  1-11: simpl_stores.
  1: reflexivity.
  1-5: pose proof (tk_FR_Q sp mem raddr x19 x20 x21 x29 (s' V_MEM64 [Ⓠ 1844704 := 0]) ltac:(clear - GB; L64) S2 W30 W19 W20 W21 W29) as QA.
  1-5: (destruct QA as (Q64 & Q56 & Q48 & Q40 & Q32);
        [intros a A1 A2; rewrite getmem_setmem_below by (clear - A1 A2 GB S2; L64); apply FRM; clear - A1 A2; lia|]).
  1: exact Q48. 1: exact Q40. 1: exact Q32. 1: exact Q64. 1: exact Q56.
  1: reflexivity.
  1: exact NZ.
  1: { apply N.eqb_eq in BC. destruct (N.lt_ge_cases K Ks) as [LT|GE]; [exfalso; exact (NFp K LT BC)|clear - KK GE; lia]. }
  1: { intros i I. specialize (CI i I). rewrite FRA in CI by (clear - I KK BP; L64).
       apply (agree_cs_in _ _ c Lc (sp - 176) _ FRA) in CI; [exact CI | clear - BCl; L64]. }
  1: { unfold tks_out. intros a A O. simpl_stores. apply setmem_agree_B. apply OUT3; assumption. }
  apply N.eqb_neq in BC.
  assert (LT: K < Ks) by (destruct (N.eqb_spec K Ks) as [E|E]; [rewrite E in BC; exfalso; exact (BC Zp)|clear - KK E; lia]).
  do 4 arm8_step.
  set (M1 := s' V_MEM64 [Ⓠ sp ⊖ 8 := p + K]).
  assert (AG1: ∀ a, a < sp - 176 -> M1 Ⓑ[a] = mem Ⓑ[a]).
  { intros a A. subst M1. rewrite (msub_small 64 sp 8) by (clear - GB S2; L64).
    rewrite getmem_setmem_above by (clear - A GB S2; L64). apply OUT3; clear - A S2; L64. }
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s4 := st) end.
  eapply models_after_steps. eassumption. apply tks_prog_welltyped. intro MDL4.
  set (TJ := tks_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K).
  apply (perform_call 2 4 eq_refl TI TJ).
  { intros tt xx EE.
    refine (strcspn_short_correct_in_strtok sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K s4 tt xx EE MDL4 _ _ _ _ _ _ _ _ _).
    { unfold css_pre. rewrite (msub_small 64 sp 64) by (clear - GB S2; L64).
      split. { intros i I. rewrite AG1 by (clear - I LT BP; L64). replace (p + K + i) with (p + (K + i)) by (clear; lia). apply NFp. clear - I LT; lia. }
      split. { rewrite AG1 by (clear - LT BP; L64). replace (p + K + (Ks - K)) with (p + Ks) by (clear - LT; lia). exact Zp. }
      split. { apply (agree_nilfree mem _ c Lc (sp - 176)); [intros a A; symmetry; apply AG1, A | clear - BCl; L64 | exact NFc]. }
      split. { rewrite AG1 by (clear - BCl; L64). exact Zc. }
      split. { exact L2. }
      clear - GB S2 BP BCl LT. L64. }
    all: unfold s4; simpl_stores.
    reflexivity. reflexivity. reflexivity. exact PK. reflexivity. reflexivity. exact K29. exact (conj K21 I). }
  { reflexivity. }
  clear MO.
  intros a5 s5 t5 ENTRY5 XP5 UT5 PRE5.
  destruct_inv 64 PRE5.
  destruct PRE5 as (((K2 & KK2 & R02 & NI2 & KE2) & RSP5 & R195 & R295 & R305 & MO5) & (K215 & _)).
  cbn [fst snd] in K215.
  rewrite (msub_small 64 sp 64) in MO5 by (clear - GB S2; L64).
  assert (OUT5: ∀ a, a < 2^64 -> (a < sp - 176 \/ sp <= a) -> s5 V_MEM64 Ⓑ[a] = mem Ⓑ[a]).
  { intros a A O. rewrite MO5 by (clear - A O GB S2; L64). destruct O as [O|O].
    - apply AG1, O.
    - subst M1. rewrite (msub_small 64 sp 8) by (clear - GB S2; L64).
      rewrite getmem_setmem_below by (clear - A O GB S2; L64). apply OUT3; [exact A | right; exact O]. }
  assert (FR5: ∀ a, sp - 64 <= a -> a < sp - 24 -> s5 V_MEM64 Ⓑ[a] = tk_frame sp mem raddr x19 x20 x21 x29 Ⓑ[a]).
  { intros a A1 A2. rewrite MO5 by (clear - A1 A2 GB S2; L64). subst M1. rewrite (msub_small 64 sp 8) by (clear - GB S2; L64).
    rewrite getmem_setmem_above by (clear - A1 A2 GB S2; L64). apply FRM; clear - A1 A2; lia. }
  assert (Q8: s5 V_MEM64 Ⓠ[sp ⊖ 8] = p + K).
  { transitivity (M1 Ⓠ[sp ⊖ 8]).
    - apply getmem_ext. intros i I. apply MO5; rewrite (msub_small 64 sp 8) by (clear - GB S2; L64); clear - I GB S2; L64.
    - subst M1. rewrite getmem_setmem by (clear; L64). apply N.mod_small. clear - LT BP S2. L64. }
  assert (BY5: s5 V_MEM64 Ⓑ[p + K + K2] = mem Ⓑ[p + K + K2]) by (apply OUT5; clear - KK2 LT BP S2; L64).
  clear MO5 FRM OUT3.
  (* facts about the strspn/strcspn results, transported to the caller's memory *)
  assert (CIm: ∀ i, i < K -> strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])).
  { intros i I. specialize (CI i I). rewrite FRA in CI by (clear - I KK BP; L64).
    apply (agree_cs_in _ _ c Lc (sp - 176) _ FRA) in CI; [exact CI | clear - BCl; L64]. }
  assert (NCK: ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K])).
  { destruct KE as [E|C]; [exfalso; clear - E LT; lia|]. intro C'. apply C.
    rewrite FRA by (clear - LT BP; L64). apply (agree_cs_in _ _ c Lc (sp - 176) _ FRA); [clear - BCl; L64 | exact C']. }
  assert (AG1': ∀ a, a < sp - 176 -> mem Ⓑ[a] = M1 Ⓑ[a]) by (intros a A; symmetry; apply AG1, A).
  assert (NI2m: ∀ i, i < K2 -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K + i])).
  { intros i I C. apply (NI2 i I). rewrite AG1 by (clear - I KK2 LT BP; L64).
    apply (agree_cs_in _ _ c Lc (sp - 176) _ AG1'); [clear - BCl; L64 | exact C]. }
  assert (PK2: (p + K) ⊕ K2 = p + K + K2) by (apply N.mod_small; clear - KK2 LT BP S2; L64).
  clear CI KE NI2 FRA MRA.
  do 5 arm8_step.
  all: rewrite !Q8 in *.
  all: rewrite !PK2 in *.
  1: rewrite ?BY5 in *. 2: rewrite ?BY5 in *.
  assert (PK3: (p + K + K2) ⊕ 1 = p + K + K2 + 1) by (apply N.mod_small; clear - KK2 LT BP S2; L64).
  all: repeat arm8_step.
  { (* token runs to end of string: static := 0 *)
    rewrite ?K215. apply N.eqb_eq in BC0.
    assert (E: K + K2 = Ks).
    { destruct (N.lt_ge_cases (K + K2) Ks) as [L|G]; [exfalso; apply (NFp (K + K2) L); rewrite N.add_assoc; exact BC0 | clear - G KK2 LT; lia]. }
    match goal with |- context [tks_out _ ?st _] => apply (tks_post_B1 sp mem raddr p c Ks Lc x19 x20 x21 x29 K K2 st) end.
    1-14: simpl_stores.
    1: reflexivity.
    1-5: pose proof (tk_FR_Q sp mem raddr x19 x20 x21 x29 (s5 V_MEM64 [Ⓠ 1504 + 1843200 := 0]) ltac:(clear - GB; L64) S2 W30 W19 W20 W21 W29) as QA.
    1-5: (destruct QA as (Q64 & Q56 & Q48 & Q40 & Q32);
          [intros a A1 A2; rewrite getmem_setmem_below by (clear - A1 A2 GB S2; L64); apply FR5; clear - A1 A2; lia|]).
    1: exact Q48. 1: exact Q40. 1: exact Q32. 1: exact Q64. 1: exact Q56.
    1: reflexivity.
    1: exact NZ. 1: exact LT. 1: exact CIm. 1: exact NCK. 1: exact E. 1: exact NI2m.
    unfold tks_out. intros a A O. simpl_stores. apply setmem_agree_B. apply OUT5; assumption. }
  { (* separator found: static := end+1, terminate token *)
    rewrite ?K215. apply N.eqb_neq in BC0. rewrite ?PK3.
    assert (L': K + K2 < Ks).
    { destruct (N.lt_ge_cases (K + K2) Ks) as [L|G]; [exact L | exfalso; apply BC0].
      replace (p + K + K2) with (p + Ks) by (clear - G KK2 LT; lia). exact Zp. }
    assert (CK2: strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K + K2])).
    { destruct KE2 as [E2|C]; [exfalso; clear - E2 L'; lia|].
      rewrite AG1 in C by (clear - L' BP; L64). apply (agree_cs_in _ _ c Lc (sp - 176) _ AG1) in C; [exact C | clear - BCl; L64]. }
    match goal with |- context [tks_out _ ?st _] => apply (tks_post_B2 sp mem raddr p c Ks Lc x19 x20 x21 x29 K K2 st) end.
    1-15: simpl_stores.
    1: reflexivity.
    1-5: pose proof (tk_FR_Q sp mem raddr x19 x20 x21 x29 (s5 V_MEM64 [Ⓠ 1844704 := 1 + p + K + K2] [Ⓑ p + K + K2 := 0])
                       ltac:(clear - GB; L64) S2 W30 W19 W20 W21 W29) as QA.
    1-5: (destruct QA as (Q64 & Q56 & Q48 & Q40 & Q32);
          [intros a A1 A2; rewrite !getmem_setmem_below by (clear - A1 A2 GB S2 BP L' KK2; L64); apply FR5; clear - A1 A2; lia|]).
    1: exact Q48. 1: exact Q40. 1: exact Q32. 1: exact Q64. 1: exact Q56.
    1: reflexivity.
    1: exact NZ. 1: exact LT. 1: exact CIm. 1: exact NCK. 1: exact L'. 1: exact NI2m. 1: exact CK2.
    unfold tks_out. intros a A O. simpl_stores.
    replace (1 + p + K + K2) with (p + K + K2 + 1) by (clear; lia).
    apply setmem_agree_B. apply setmem_agree_B. apply OUT5; assumption. }
Qed.

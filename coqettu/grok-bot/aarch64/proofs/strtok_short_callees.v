(* strtok, short separator-set path: program lemmas, the strspn / short-strcspn transfer
   theorems and the entry case.  Full header is in strtok_short_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strtok_armv8 strspn_armv8 strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCall GrokKeep.
From Grok.proofs Require Import strtok_defs strtok_callees.
From Grok.proofs Require strcspn_defs strspn_defs strspn_proof strchrnul_proof.
From Grok.proofs Require Import strcspn_short_defs strcspn_short_proof.
From Grok.proofs Require Import strtok_short_defs.
Import ARM8Notations.
Open Scope N.

Theorem tks_prog_welltyped: welltyped_prog arm8typctx tks_prog.
Proof.
  intros s a. unfold tks_prog, updateall2, updateall.
  destruct (css_prog s a) as [[sz q]|] eqn:T0.
    pose proof (css_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
  destruct (strspn_armv8.strspn_armv8 s a) as [[sz q]|] eqn:T1.
    pose proof (strspn_armv8.welltyped s a) as WT. rewrite T1 in WT. exact WT.
    apply strtok_armv8.welltyped.
Qed.

Lemma tks_sc_in_css: strchrnul_armv8.strchrnul_armv8 ⊆2 css_prog.
Proof. intros s a i H. apply sc_contains. apply strchrnul_proof.strchrnul_prog_contains. exact H. Qed.

Lemma tks_sl_in_css: strlen_armv8.strlen_armv8 ⊆2 css_prog.
Proof. intros s a i H. apply sc_contains. apply subset_updateall2. exact H. Qed.

Lemma css_in_tks: css_prog ⊆2 tks_prog.
Proof. apply subset_updateall2. Qed.

Ltac css_unf E := unfold css_prog, strchrnul_proof.strchrnul_prog, updateall2, updateall,
      strlen_armv8.strlen_armv8, strchrnul_armv8.strchrnul_armv8, strcspn_armv8.strcspn_armv8 in E.

Lemma ss_in_tks: strspn_armv8.strspn_armv8 ⊆2 tks_prog.
Proof.
  intros s a i H. unfold tks_prog, updateall2, updateall.
  destruct (css_prog s a) as [i'|] eqn:E.
  - exfalso. unfold strspn_armv8.strspn_armv8 in H. css_unf E.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H; try discriminate E).
  - rewrite H. reflexivity.
Qed.

Lemma tk_in_tks: strtok_armv8.strtok_armv8 ⊆2 tks_prog.
Proof.
  intros s a i H. unfold tks_prog, updateall2, updateall.
  destruct (css_prog s a) as [i'|] eqn:E.
  - exfalso. unfold strtok_armv8.strtok_armv8 in H. css_unf E.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H; try discriminate E).
  - unfold strspn_armv8.strspn_armv8. unfold strtok_armv8.strtok_armv8 in H.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H); exact H.
Qed.

Lemma tks_prog_mono: ∀ prog, strtok_armv8.strtok_armv8 ⊆2 prog -> strspn_armv8.strspn_armv8 ⊆2 prog ->
  strcspn_armv8.strcspn_armv8 ⊆2 prog -> strchrnul_armv8.strchrnul_armv8 ⊆2 prog ->
  strlen_armv8.strlen_armv8 ⊆2 prog -> tks_prog ⊆2 prog.
Proof.
  intros prog P4 P3 P2 P1 P0 s a insn H. unfold tks_prog, updateall2, updateall in H.
  destruct (css_prog s a) eqn:E0; [inversion H; subst; apply (css_prog_mono prog P2 P1 P0); exact E0|].
  destruct (strspn_armv8.strspn_armv8 s a) eqn:E1; [inversion H; subst; apply P3; exact E1|].
  apply P4; exact H.
Qed.

Section Calls.
  Variables (sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 : N).
  Let SSI := strspn_defs.ss_invs (sp ⊖ 64) (tks_FR sp mem raddr x19 x20 x21 x29) 0x15f7ec p c Ks Lc.
  Let CSI := css_invs (sp ⊖ 64) M1 0x15f808 (p + K1) c p (sp ⊖ 64) (Ks - K1) Lc.
  Let TI := tks_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1.
  Let TSS := tks_Fss sp mem raddr p c Ks Lc x19 x20 x21 x29.
  Let TCS := tks_Fcs sp p c Ks Lc M1 K1.

  Lemma tks_at_ss: ∀ s a i T Inv Post NoInv, strspn_armv8.strspn_armv8 s a = Some i ->
    TI T Inv Post NoInv s a = TSS T Inv Post NoInv s a.
  Proof.
    intros s a i T Inv Post NoInv H. unfold strspn_armv8.strspn_armv8 in H.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H); reflexivity.
  Qed.

  Lemma tks_at_cs: ∀ s a i T Inv Post NoInv, css_prog s a = Some i ->
    TI T Inv Post NoInv s a = TCS T Inv Post NoInv s a.
  Proof.
    intros s a i T Inv Post NoInv H. css_unf H.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H); reflexivity.
  Qed.

  Lemma tks_ss_shape: ∀ s a b m,
    SSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (b,m) ->
    m = 0 /\ (b = true -> a = 0x15f380) /\
    TSS (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (b,3) /\
    TSS Prop (fun _ P => P) (fun _ P => P) False s a = (SSI Prop (fun _ P => P) (fun _ P => P) False s a /\ keepl_st (tks_L sp p c) s).
  Proof.
    intros s a b m H. subst SSI TSS. unfold tks_Fss. unfold strspn_defs.ss_invs in *.
    destruct a as [|q]; [discriminate H|].
    repeat (destruct q as [q|q|]; try discriminate H);
    injection H as <- <-; (split; [reflexivity | split; [intros B; first [discriminate B | reflexivity] | split; reflexivity]]).
  Qed.

  Lemma tks_ss_none: ∀ s a,
    SSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = None ->
    TSS (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = None.
  Proof.
    intros s a H. subst SSI TSS. unfold tks_Fss. unfold strspn_defs.ss_invs in *.
    destruct a as [|q]; [reflexivity|].
    repeat (destruct q as [q|q|]; try discriminate H; try reflexivity).
  Qed.

  Lemma tks_cs_shape: ∀ s a b m,
    CSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (b,m) ->
    m <= 2 /\ (b = true -> m = 2 -> a = 0x15ed28) /\
    TCS Prop (fun _ P => P) (fun _ P => P) False s a = (CSI Prop (fun _ P => P) (fun _ P => P) False s a /\ keepl_st ((R_X21, 0x1c2000)::nil) s).
  Proof.
    intros s a b m H. subst CSI TCS. unfold tks_Fcs. unfold css_invs, css_F, strchrnul_proof.invs in *.
    destruct a as [|q]; [discriminate H|].
    repeat (destruct q as [q|q|]; try discriminate H);
    injection H as <- <-; (split; [lia | split; [intros B M; first [discriminate B | discriminate M | reflexivity] | reflexivity]]).
  Qed.

  Lemma tks_post_addr: ∀ s a m, TI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,m) ->
    (m = 3 -> a = 0x15f380) /\ (m = 2 -> a = 0x15ed28).
  Proof.
    intros s a m H. subst TI. unfold tks_invs in H.
    destruct (N.eqb_spec a 0x15f7c4); [discriminate H|].
    destruct (N.eqb_spec a 0x15f7e0); [discriminate H|].
    destruct (N.eqb_spec a 0x15f834); [injection H as <-; split; intro; discriminate|].
    destruct (N.eqb_spec a 0x15f2e8) as [E|]; [subst a; discriminate H|].
    destruct (N.eqb_spec a 0x15f380) as [E|]; [subst a; split; intro; [reflexivity | subst m; discriminate H]|].
    destruct (N.eqb_spec a 0x15f314) as [E|]; [subst a; discriminate H|].
    destruct (N.eqb_spec a 0x15f340) as [E|]; [subst a; discriminate H|].
    destruct (N.eqb_spec a 0x15f360) as [E|]; [subst a; discriminate H|].
    assert (H' : CSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,m)) by exact H.
    destruct (tks_cs_shape _ _ _ _ H') as (M & PA & _). split; intro E; [lia | exact (PA eq_refl E)].
  Qed.
End Calls.

Lemma tks_ss_noassign: ∀ sp p c vx, In vx (tks_L sp p c) -> prog_noassign (fst vx) strspn_armv8.strspn_armv8.
Proof.
  intros sp p c vx IN. simpl in IN.
  destruct IN as [<-|[<-|[<-|[<-|[]]]]]; simpl; prove_noassign.
Qed.

Lemma css_noassign_x21: ∀ vx, In vx ((R_X21, 0x1c2000)::nil) -> prog_noassign (fst vx) css_prog.
Proof.
  intros vx IN. destruct IN as [<-|[]]. simpl. prove_noassign.
Qed.

Theorem strspn_correct_in_strtok_short:
  ∀ sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 s t xs'
    (ENTRY: startof t xs' = (Addr 0x15f2e8, s)) (MDL: models arm8typctx s)
    (PRE: strspn_defs.ss_pre (sp ⊖ 64) (tks_FR sp mem raddr x19 x20 x21 x29) p c Ks Lc)
    (SP: s R_SP = sp ⊖ 64) (MEM: s V_MEM64 = tks_FR sp mem raddr x19 x20 x21 x29) (X30: s R_X30 = 0x15f7ec)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (KL: keepl_st (tks_L sp p c) s),
  satisfies_all tks_prog (tks_invs3 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1)
                         (tks_exits3 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1) (xs'::t).
Proof.
  intros.
  set (SSI := strspn_defs.ss_invs (sp ⊖ 64) (tks_FR sp mem raddr x19 x20 x21 x29) 0x15f7ec p c Ks Lc).
  assert (XE: tks_exits3 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 = make_exits 0 strspn_armv8.strspn_armv8 SSI).
  { extensionality tt. destruct tt as [|[[a|i] s1] t1]; try reflexivity.
    unfold tks_exits3, make_exits. destruct (strspn_armv8.strspn_armv8 s1 a) as [insn|] eqn:IL.
    - rewrite (ss_in_tks _ _ _ IL). rewrite (tks_at_ss sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ _ _ _ _ _ _ IL).
      destruct (SSI _ (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a) as [[b m]|] eqn:F.
      + destruct (tks_ss_shape sp mem raddr p c Ks Lc x19 x20 x21 x29 _ _ _ _ F) as (M0 & _ & EO & _).
        rewrite EO. subst m. destruct b; reflexivity.
      + rewrite (tks_ss_none sp mem raddr p c Ks Lc x19 x20 x21 x29 _ _ F). reflexivity.
    - destruct (tks_prog s1 a) eqn:IL2; [|reflexivity].
      destruct (tks_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a)
        as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 3); [|reflexivity]. subst m.
      apply tks_post_addr in F. destruct F as [F _]. rewrite (F eq_refl) in IL. vm_compute in IL. discriminate IL. }
  unfold tks_invs3. rewrite XE.
  apply satisfies_all_transfer with (p1 := strspn_armv8.strspn_armv8)
    (I1 := keepl_invs (make_invs 0 strspn_armv8.strspn_armv8 SSI) (tks_L sp p c)).
  - exact ss_in_tks.
  - intros a s1 t1 _ N0. unfold keepl_invs, make_invs. rewrite N0. reflexivity.
  - intros a s1 t1 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s1 t1 insn IL. unfold keepl_invs, make_invs. rewrite (ss_in_tks _ _ _ IL), IL.
    rewrite !(tks_at_ss sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ _ _ _ _ _ _ IL).
    destruct (SSI _ (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a) as [[b m]|] eqn:F.
    + destruct (tks_ss_shape sp mem raddr p c Ks Lc x19 x20 x21 x29 _ _ _ _ F) as (M0 & _ & EO & EQ). subst m.
      rewrite EO. simpl (3 ?= 3). simpl (0 ?= 0). rewrite EQ. reflexivity.
    + rewrite (tks_ss_none sp mem raddr p c Ks Lc x19 x20 x21 x29 _ _ F). reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (satisfies_all_keepl _ _ _ (tks_L sp p c) (tks_ss_noassign sp p c) xs' t).
    + match goal with |- keepl_st _ (snd ?x) => replace x with (Addr 0x15f2e8, s) by (symmetry; exact ENTRY) end. exact KL.
    + intros xs1 t1 START. assert (START2: startof t1 xs1 = (Addr 0x15f2e8, s)) by (rewrite START; exact ENTRY). clear START.
      eapply strspn_proof.strspn_partial_correctness; try eassumption.
      intros s2 a2 i2 H2. exact H2.
Qed.

Theorem strcspn_short_correct_in_strtok:
  ∀ sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 s t xs'
    (ENTRY: startof t xs' = (Addr 0x15ecf0, s)) (MDL: models arm8typctx s)
    (PRE: css_pre (sp ⊖ 64) M1 (p + K1) c (Ks - K1) Lc)
    (SP: s R_SP = sp ⊖ 64) (MEM: s V_MEM64 = M1) (X30: s R_X30 = 0x15f808)
    (X0: s R_X0 = p + K1) (X1: s R_X1 = c) (X19: s R_X19 = p) (X29: s R_X29 = sp ⊖ 64)
    (KL: keepl_st ((R_X21, 0x1c2000)::nil) s),
  satisfies_all tks_prog (tks_invs2 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1)
                         (tks_exits2 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1) (xs'::t).
Proof.
  intros.
  set (CSI := css_invs (sp ⊖ 64) M1 0x15f808 (p + K1) c p (sp ⊖ 64) (Ks - K1) Lc).
  assert (XE: tks_exits2 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 = make_exits 2 css_prog CSI).
  { extensionality tt. destruct tt as [|[[a|i] s1] t1]; try reflexivity.
    unfold tks_exits2, make_exits. destruct (css_prog s1 a) as [insn|] eqn:IL.
    - rewrite (css_in_tks _ _ _ IL). rewrite (tks_at_cs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ _ _ _ _ _ _ IL). reflexivity.
    - destruct (tks_prog s1 a) eqn:IL2; [|reflexivity].
      destruct (tks_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a)
        as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 2); [|reflexivity]. subst m.
      apply tks_post_addr in F. destruct F as [_ F]. rewrite (F eq_refl) in IL. vm_compute in IL. discriminate IL. }
  unfold tks_invs2. rewrite XE.
  apply satisfies_all_transfer with (p1 := css_prog)
    (I1 := keepl_invs (make_invs 2 css_prog CSI) ((R_X21, 0x1c2000)::nil)).
  - exact css_in_tks.
  - intros a s1 t1 _ N0. unfold keepl_invs, make_invs. rewrite N0. reflexivity.
  - intros a s1 t1 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s1 t1 insn IL. unfold keepl_invs, make_invs. rewrite (css_in_tks _ _ _ IL), IL.
    rewrite !(tks_at_cs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ _ _ _ _ _ _ IL).
    assert (EM: tks_Fcs sp p c Ks Lc M1 K1 (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a =
                CSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a) by reflexivity.
    rewrite EM.
    destruct (CSI _ _ _ _ s1 a) as [[b m]|] eqn:F; [|reflexivity].
    destruct (tks_cs_shape sp p c Ks Lc M1 K1 _ _ _ _ F) as (M0 & _ & EQ).
    destruct (N.compare_spec m 2) as [E|E|E]; [subst m; rewrite EQ; reflexivity | reflexivity | exfalso; lia].
  - reflexivity.
  - reflexivity.
  - apply (satisfies_all_keepl _ _ _ _ css_noassign_x21 xs' t).
    + match goal with |- keepl_st _ (snd ?x) => replace x with (Addr 0x15ecf0, s) by (symmetry; exact ENTRY) end. exact KL.
    + intros xs1 t1 START. assert (START2: startof t1 xs1 = (Addr 0x15ecf0, s)) by (rewrite START; exact ENTRY). clear START.
      eapply strcspn_short_partial_correctness; try eassumption.
      * apply css_contains.
      * apply tks_sc_in_css.
      * apply tks_sl_in_css.
Qed.

Lemma tks_case_entry: ∀ sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 (s1:store) (t:list (exit*store)),
  tks_pre sp mem s0 p c Ks Lc ->
  x19 < 2^64 -> x20 < 2^64 -> x21 < 2^64 -> x29 < 2^64 -> raddr < 2^64 -> s0 < 2^64 -> c < 2^64 ->
  models arm8typctx s1 ->
  tks_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0 Prop (fun _ P => P) (fun _ P => P) True s1 0x15f7c4 ->
  nextinv tks_prog (tks_invs4 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0)
                  (tks_exits4 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0) false ((Addr 0x15f7c4, s1) :: t).
Proof.
  intros sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 s1 t PRE0 W19 W20 W21 W29 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X20 & X21 & X29).
  pose proof PRE0 as (SEL & GB & S2 & PZ).
  unfold tk_G in GB, SEL.
  repeat arm8_step.
  all: pose proof (tk_FG sp mem raddr x19 x20 x21 x29 ltac:(clear - GB; lia) S2) as FG.
  1: apply N.eqb_eq in BC.
  1: apply Bool.negb_true_iff, N.eqb_neq in BC0.
  1: rewrite FG in BC0 |- *.
  1: destruct SEL as [[NZ _]|[_ E]]; [exfalso; exact (NZ BC)|].
  1: rewrite E in BC0 |- *.
  1: exact (conj BC0 (conj eq_refl (conj X1 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))).
  1: apply N.eqb_eq in BC.
  1: apply Bool.negb_false_iff, N.eqb_eq in BC0.
  1: rewrite FG in BC0.
  1: destruct SEL as [[NZ _]|[_ E]]; [exfalso; exact (NZ BC)|].
  1: rewrite E in BC0.
  1: refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (or_introl (conj BC0 (conj eq_refl _))))))))).
  1: intros a A O.
  1: apply (tk_FR_out sp mem raddr x19 x20 x21 x29 a); [clear - GB; lia | exact S2 | exact A | destruct O as [O|O]; [left; clear - O; lia | right; exact O]].
  1: apply N.eqb_neq in BC.
  1: destruct SEL as [[NZ E]|[Z _]]; [|exfalso; exact (BC Z)].
  1: subst p.
  1: (refine (conj NZ (conj eq_refl (conj X1 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))))).
Qed.

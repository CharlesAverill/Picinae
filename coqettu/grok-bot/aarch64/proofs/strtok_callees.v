(* strtok: program inclusion, the strspn/strcspn transfer theorems and the entry case.
   Full header is in strtok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strtok_armv8 strspn_armv8 strcspn_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCall.
From Grok.lib Require Import GrokKeep.
From Grok.proofs Require Import strtok_defs.
From Grok.proofs Require strcspn_defs strcspn_proof strspn_defs strspn_proof memset_proof.
Import ARM8Notations.
Open Scope N.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Ltac addr_tac IL := repeat first
  [ discriminate IL
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end
  | match type of IL with context [match ?n with _ => _ end] => is_var n; destruct n end ].

Theorem tk_prog_welltyped: welltyped_prog arm8typctx tk_prog.
Proof.
  intros s a. unfold tk_prog, updateall2, updateall.
  destruct (strcspn_defs.cs_prog s a) as [[sz q]|] eqn:T0.
    pose proof (strcspn_defs.cs_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
  destruct (strspn_armv8.strspn_armv8 s a) as [[sz q]|] eqn:T1.
    pose proof (strspn_armv8.welltyped s a) as WT. rewrite T1 in WT. exact WT.
    apply strtok_armv8.welltyped.
Qed.

Lemma cs_contains: strcspn_armv8.strcspn_armv8 ⊆2 strcspn_defs.cs_prog.
Proof.
  intros s a insn SC. unfold strcspn_defs.cs_prog, updateall2, updateall, memset_armv8.memset_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma cs_in_tk: strcspn_defs.cs_prog ⊆2 tk_prog.
Proof. apply subset_updateall2. Qed.

Lemma ss_in_tk: strspn_armv8.strspn_armv8 ⊆2 tk_prog.
Proof.
  intros s a i H. unfold tk_prog, updateall2, updateall.
  destruct (strcspn_defs.cs_prog s a) as [i'|] eqn:E.
  - exfalso. unfold strspn_armv8.strspn_armv8 in H. unfold strcspn_defs.cs_prog, updateall2, updateall,
      memset_armv8.memset_armv8, strcspn_armv8.strcspn_armv8 in E.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H; try discriminate E).
  - rewrite H. reflexivity.
Qed.

Lemma tk_in_tk: strtok_armv8.strtok_armv8 ⊆2 tk_prog.
Proof.
  intros s a i H. unfold tk_prog, updateall2, updateall.
  destruct (strcspn_defs.cs_prog s a) as [i'|] eqn:E.
  - exfalso. unfold strtok_armv8.strtok_armv8 in H. unfold strcspn_defs.cs_prog, updateall2, updateall,
      memset_armv8.memset_armv8, strcspn_armv8.strcspn_armv8 in E.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H; try discriminate E).
  - unfold strspn_armv8.strspn_armv8. unfold strtok_armv8.strtok_armv8 in H.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H); exact H.
Qed.

Lemma tk_prog_mono: ∀ prog, strtok_armv8.strtok_armv8 ⊆2 prog -> strspn_armv8.strspn_armv8 ⊆2 prog ->
  strcspn_armv8.strcspn_armv8 ⊆2 prog -> memset_armv8.memset_armv8 ⊆2 prog -> tk_prog ⊆2 prog.
Proof.
  intros prog P3 P2 P1 P0 s a insn H. unfold tk_prog, updateall2, updateall in H.
  destruct (strcspn_defs.cs_prog s a) eqn:E0; [inversion H; subst; apply (strcspn_defs.cs_prog_mono prog P1 P0); exact E0|].
  destruct (strspn_armv8.strspn_armv8 s a) eqn:E1; [inversion H; subst; apply P2; exact E1|].
  apply P3; exact H.
Qed.

Section Calls.
  Variables (sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 : N).
  Let SSI := strspn_defs.ss_invs (sp ⊖ 64) (tk_FR sp mem raddr x19 x20 x21 x29) 0x15f7ec p c Ks Lc.
  Let CSI := strcspn_defs.invs (sp ⊖ 64) M1 0x15f808 (p + K1) c p (sp ⊖ 64) (Ks - K1) Lc.
  Let TI := tk_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1.
  Let TSS := tk_Fss sp mem raddr p c Ks Lc x19 x20 x21 x29.
  Let TCS := tk_Fcs sp p c Ks Lc M1 K1.

  Lemma tk_at_ss: ∀ s a i T Inv Post NoInv, strspn_armv8.strspn_armv8 s a = Some i ->
    TI T Inv Post NoInv s a = TSS T Inv Post NoInv s a.
  Proof.
    intros s a i T Inv Post NoInv H. unfold strspn_armv8.strspn_armv8 in H.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H); reflexivity.
  Qed.

  Lemma tk_at_cs: ∀ s a i T Inv Post NoInv, strcspn_defs.cs_prog s a = Some i ->
    TI T Inv Post NoInv s a = TCS T Inv Post NoInv s a.
  Proof.
    intros s a i T Inv Post NoInv H.
    unfold strcspn_defs.cs_prog, updateall2, updateall, memset_armv8.memset_armv8, strcspn_armv8.strcspn_armv8 in H.
    destruct a as [|q]; [discriminate H|]. repeat (destruct q as [q|q|]; try discriminate H); reflexivity.
  Qed.

  Lemma ss_shape: ∀ s a b m,
    SSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (b,m) ->
    m = 0 /\ (b = true -> a = 0x15f380) /\
    TSS Prop (fun _ P => P) (fun _ P => P) False s a = (SSI Prop (fun _ P => P) (fun _ P => P) False s a /\ keepl_st (tk_L sp p c) s).
  Proof.
    intros s a b m H. subst SSI TSS. unfold tk_Fss. unfold strspn_defs.ss_invs in *.
    destruct a as [|q]; [discriminate H|].
    repeat (destruct q as [q|q|]; try discriminate H);
    injection H as <- <-; (split; [reflexivity | split; [intros B; first [discriminate B | reflexivity] | reflexivity]]).
  Qed.

  Lemma cs_shape: ∀ s a b m,
    CSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (b,m) ->
    m = 1 /\ (b = true -> a = 0x15ed28) /\
    TCS Prop (fun _ P => P) (fun _ P => P) False s a = (CSI Prop (fun _ P => P) (fun _ P => P) False s a /\ keepl_st ((R_X21, 0x1c2000)::nil) s).
  Proof.
    intros s a b m H. subst CSI TCS. unfold tk_Fcs. unfold strcspn_defs.invs in *.
    destruct a as [|q]; [discriminate H|].
    repeat (destruct q as [q|q|]; try discriminate H);
    injection H as <- <-; (split; [reflexivity | split; [intros B; first [discriminate B | reflexivity] | reflexivity]]).
  Qed.

  Lemma tk_post_addr: ∀ s a m, TI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,m) ->
    (m = 0 -> a = 0x15f380) /\ (m = 1 -> a = 0x15ed28).
  Proof.
    intros s a m H. subst TI. unfold tk_invs in H.
    destruct (N.eqb_spec a 0x15f7c4); [discriminate H|].
    destruct (N.eqb_spec a 0x15f7e0); [discriminate H|].
    destruct (N.eqb_spec a 0x15f834); [injection H as <-; split; intro; discriminate|].
    destruct (N.eqb_spec a 0x15f2e8) as [E|]; [subst a; discriminate H|].
    destruct (N.eqb_spec a 0x15f380) as [E|]; [subst a; split; intro; [reflexivity | subst m; discriminate H]|].
    destruct (N.eqb_spec a 0x15f314) as [E|]; [subst a; discriminate H|].
    destruct (N.eqb_spec a 0x15f340) as [E|]; [subst a; discriminate H|].
    destruct (N.eqb_spec a 0x15f360) as [E|]; [subst a; discriminate H|].
    assert (H' : CSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,m)) by exact H.
    destruct (cs_shape _ _ _ _ H') as (M & PA & _). subst m. split; intro E; [discriminate E | exact (PA eq_refl)].
  Qed.
End Calls.

Lemma ss_noassign: ∀ sp p c vx, In vx (tk_L sp p c) -> prog_noassign (fst vx) strspn_armv8.strspn_armv8.
Proof.
  intros sp p c vx IN. simpl in IN.
  destruct IN as [<-|[<-|[<-|[<-|[]]]]]; simpl; prove_noassign.
Qed.

Lemma cs_noassign_x21: ∀ vx, In vx ((R_X21, 0x1c2000)::nil) -> prog_noassign (fst vx) strcspn_defs.cs_prog.
Proof.
  intros vx IN. destruct IN as [<-|[]]. simpl. prove_noassign.
Qed.

Theorem strspn_correct_in_strtok:
  ∀ sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 s t xs'
    (ENTRY: startof t xs' = (Addr 0x15f2e8, s)) (MDL: models arm8typctx s)
    (PRE: strspn_defs.ss_pre (sp ⊖ 64) (tk_FR sp mem raddr x19 x20 x21 x29) p c Ks Lc)
    (SP: s R_SP = sp ⊖ 64) (MEM: s V_MEM64 = tk_FR sp mem raddr x19 x20 x21 x29) (X30: s R_X30 = 0x15f7ec)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (KL: keepl_st (tk_L sp p c) s),
  satisfies_all tk_prog (tk_invs0 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1)
                        (tk_exits0 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1) (xs'::t).
Proof.
  intros.
  set (SSI := strspn_defs.ss_invs (sp ⊖ 64) (tk_FR sp mem raddr x19 x20 x21 x29) 0x15f7ec p c Ks Lc).
  assert (XE: tk_exits0 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 = make_exits 0 strspn_armv8.strspn_armv8 SSI).
  { extensionality tt. destruct tt as [|[[a|i] s1] t1]; try reflexivity.
    unfold tk_exits0, make_exits. destruct (strspn_armv8.strspn_armv8 s1 a) as [insn|] eqn:IL.
    - rewrite (ss_in_tk _ _ _ IL). rewrite (tk_at_ss sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ _ _ _ _ _ _ IL). reflexivity.
    - destruct (tk_prog s1 a) eqn:IL2; [|reflexivity].
      destruct (tk_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a)
        as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 0); [|reflexivity]. subst m.
      apply tk_post_addr in F. destruct F as [F _]. rewrite (F eq_refl) in IL. vm_compute in IL. discriminate IL. }
  unfold tk_invs0. rewrite XE.
  apply satisfies_all_transfer with (p1 := strspn_armv8.strspn_armv8)
    (I1 := keepl_invs (make_invs 0 strspn_armv8.strspn_armv8 SSI) (tk_L sp p c)).
  - exact ss_in_tk.
  - intros a s1 t1 _ N0. unfold keepl_invs, make_invs. rewrite N0. reflexivity.
  - intros a s1 t1 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s1 t1 insn IL. unfold keepl_invs, make_invs. rewrite (ss_in_tk _ _ _ IL), IL.
    rewrite !(tk_at_ss sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ _ _ _ _ _ _ IL).
    assert (EM: tk_Fss sp mem raddr p c Ks Lc x19 x20 x21 x29 (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a =
                SSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a) by reflexivity.
    rewrite EM.
    destruct (SSI _ _ _ _ s1 a) as [[b m]|] eqn:F; [|reflexivity].
    destruct (ss_shape sp mem raddr p c Ks Lc x19 x20 x21 x29 _ _ _ _ F) as (M0 & _ & EQ). subst m.
    simpl (0 ?= 0). rewrite EQ. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (satisfies_all_keepl _ _ _ (tk_L sp p c) (ss_noassign sp p c) xs' t).
    + match goal with |- keepl_st _ (snd ?x) => replace x with (Addr 0x15f2e8, s) by (symmetry; exact ENTRY) end. exact KL.
    + intros xs1 t1 START. assert (START2: startof t1 xs1 = (Addr 0x15f2e8, s)) by (rewrite START; exact ENTRY). clear START.
      eapply strspn_proof.strspn_partial_correctness; try eassumption.
      intros s2 a2 i2 H2. exact H2.
Qed.

Theorem strcspn_correct_in_strtok:
  ∀ sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 s t xs'
    (ENTRY: startof t xs' = (Addr 0x15ecf0, s)) (MDL: models arm8typctx s)
    (PRE: strcspn_defs.cs_pre (sp ⊖ 64) M1 (p + K1) c (Ks - K1) Lc)
    (SP: s R_SP = sp ⊖ 64) (MEM: s V_MEM64 = M1) (X30: s R_X30 = 0x15f808)
    (X0: s R_X0 = p + K1) (X1: s R_X1 = c) (X19: s R_X19 = p) (X29: s R_X29 = sp ⊖ 64)
    (KL: keepl_st ((R_X21, 0x1c2000)::nil) s),
  satisfies_all tk_prog (tk_invs1 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1)
                        (tk_exits1 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1) (xs'::t).
Proof.
  intros.
  set (CSI := strcspn_defs.invs (sp ⊖ 64) M1 0x15f808 (p + K1) c p (sp ⊖ 64) (Ks - K1) Lc).
  assert (XE: tk_exits1 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 = make_exits 1 strcspn_defs.cs_prog CSI).
  { extensionality tt. destruct tt as [|[[a|i] s1] t1]; try reflexivity.
    unfold tk_exits1, make_exits. destruct (strcspn_defs.cs_prog s1 a) as [insn|] eqn:IL.
    - rewrite (cs_in_tk _ _ _ IL). rewrite (tk_at_cs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ _ _ _ _ _ _ IL). reflexivity.
    - destruct (tk_prog s1 a) eqn:IL2; [|reflexivity].
      destruct (tk_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a)
        as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 1); [|reflexivity]. subst m.
      apply tk_post_addr in F. destruct F as [_ F]. rewrite (F eq_refl) in IL. vm_compute in IL. discriminate IL. }
  unfold tk_invs1. rewrite XE.
  apply satisfies_all_transfer with (p1 := strcspn_defs.cs_prog)
    (I1 := keepl_invs (make_invs 1 strcspn_defs.cs_prog CSI) ((R_X21, 0x1c2000)::nil)).
  - exact cs_in_tk.
  - intros a s1 t1 _ N0. unfold keepl_invs, make_invs. rewrite N0. reflexivity.
  - intros a s1 t1 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s1 t1 insn IL. unfold keepl_invs, make_invs. rewrite (cs_in_tk _ _ _ IL), IL.
    rewrite !(tk_at_cs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 _ _ _ _ _ _ _ IL).
    assert (EM: tk_Fcs sp p c Ks Lc M1 K1 (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a =
                CSI (option (bool*N)) (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a) by reflexivity.
    rewrite EM.
    destruct (CSI _ _ _ _ s1 a) as [[b m]|] eqn:F; [|reflexivity].
    destruct (cs_shape sp p c Ks Lc M1 K1 _ _ _ _ F) as (M0 & _ & EQ). subst m.
    simpl (1 ?= 1). rewrite EQ. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (satisfies_all_keepl _ _ _ _ cs_noassign_x21 xs' t).
    + match goal with |- keepl_st _ (snd ?x) => replace x with (Addr 0x15ecf0, s) by (symmetry; exact ENTRY) end. exact KL.
    + intros xs1 t1 START. assert (START2: startof t1 xs1 = (Addr 0x15ecf0, s)) by (rewrite START; exact ENTRY). clear START.
      eapply strcspn_proof.strcspn_partial_correctness; try eassumption.
      * exact cs_contains.
      * apply subset_updateall2.
Qed.

Ltac nrm := repeat match goal with
  | H: negb ((?b >> 0) mod 2^32 =? 0) = true |- _ => apply cbnz32_true in H; [|apply byte_lt32]
  | H: negb ((?b >> 0) mod 2^32 =? 0) = false |- _ => apply cbnz32_false in H; [|apply byte_lt32]
  | H: negb (_ =? _) = true |- _ => apply Bool.negb_true_iff, N.eqb_neq in H
  | H: negb (_ =? _) = false |- _ => apply Bool.negb_false_iff, N.eqb_eq in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end.

Lemma tk_FG: ∀ sp mem raddr x19 x20 x21 x29, 1844704 + 8 + 144 <= sp -> sp < 2^64 ->
  (mem [Ⓠ sp ⊖ 64 := x29] [Ⓠ sp ⊖ 56 := raddr] [Ⓠ sp ⊖ 48 := x19] [Ⓠ sp ⊖ 40 := x20] [Ⓠ sp ⊖ 32 := x21]) Ⓠ[1844704] = mem Ⓠ[1844704].
Proof. intros. rewrite !(msub_small 64 sp) by L64. memsimp. reflexivity. Qed.

Lemma tk_FR_out: ∀ sp mem raddr x19 x20 x21 x29 a, 64 <= sp -> sp < 2^64 -> a < 2^64 -> (a < sp - 144 \/ sp <= a) ->
  (mem [Ⓠ sp ⊖ 64 := x29] [Ⓠ sp ⊖ 56 := raddr] [Ⓠ sp ⊖ 48 := x19] [Ⓠ sp ⊖ 40 := x20] [Ⓠ sp ⊖ 32 := x21]) Ⓑ[a] = mem Ⓑ[a].
Proof. intros. rewrite !(msub_small 64 sp) by L64. destruct H2; memsimp; reflexivity. Qed.

Lemma tk_case_entry: ∀ sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 (s1:store) (t:list (exit*store)),
  tk_pre sp mem s0 p c Ks Lc ->
  x19 < 2^64 -> x20 < 2^64 -> x21 < 2^64 -> x29 < 2^64 -> raddr < 2^64 -> s0 < 2^64 -> c < 2^64 ->
  models arm8typctx s1 ->
  tk_invs sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0 Prop (fun _ P => P) (fun _ P => P) True s1 0x15f7c4 ->
  nextinv tk_prog (tk_invs2 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0)
                  (tk_exits2 sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 mem 0) false ((Addr 0x15f7c4, s1) :: t).
Proof.
  intros sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 s1 t PRE0 W19 W20 W21 W29 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X20 & X21 & X29).
  pose proof PRE0 as (SEL & GB & S2 & PZ).
  unfold tk_G in GB, SEL.
  repeat arm8_step.
  all: pose proof (tk_FG sp mem raddr x19 x20 x21 x29 GB S2) as FG.
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
  1: exact (tk_FR_out sp mem raddr x19 x20 x21 x29 a ltac:(clear - GB; lia) S2 A O).
  1: apply N.eqb_neq in BC.
  1: destruct SEL as [[NZ E]|[Z _]]; [|exfalso; exact (BC Z)].
  1: subst p.
  1: (refine (conj NZ (conj eq_refl (conj X1 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))))).
Qed.


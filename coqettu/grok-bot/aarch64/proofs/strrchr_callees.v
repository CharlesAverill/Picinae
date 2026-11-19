(* strrchr callee lemmas: program containment/typing for rr_prog and strlen's proof
   transferred into the strrchr invariant family (GrokCall + GrokKeep).
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in strrchr_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require strrchr_armv8 memrchr_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCall GrokKeep.
From Grok.proofs Require Import strlen_proof memrchr_defs strrchr_defs.
Import ARM8Notations.
Open Scope N.

Ltac contains_tac SC :=
  repeat first
  [ exact SC | discriminate SC | (rewrite SC; reflexivity)
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].

Lemma rr_contains2: strrchr_armv8.strrchr_armv8 ⊆2 rr_prog.
Proof.
  intros s a insn SC. unfold rr_prog, updateall2, updateall, strlen_armv8.strlen_armv8, memrchr_armv8.memrchr_armv8.
  contains_tac SC.
Qed.
Lemma rr_contains1: memrchr_armv8.memrchr_armv8 ⊆2 rr_prog.
Proof.
  intros s a insn SC. unfold rr_prog, updateall2, updateall, strlen_armv8.strlen_armv8.
  contains_tac SC.
Qed.
Lemma rr_contains0: strlen_armv8.strlen_armv8 ⊆2 rr_prog.
Proof. apply subset_updateall2. Qed.

Theorem rr_prog_welltyped: welltyped_prog arm8typctx rr_prog.
Proof.
  intros s a. unfold rr_prog, updateall2, updateall.
  destruct (strlen_armv8.strlen_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (strlen_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
  destruct (memrchr_armv8.memrchr_armv8 s a) as [[sz q]|] eqn:TN.
    pose proof (memrchr_armv8.welltyped s a) as WT. rewrite TN in WT. exact WT.
    apply strrchr_armv8.welltyped.
Qed.

Lemma rr_prog_mono: ∀ prog, strrchr_armv8.strrchr_armv8 ⊆2 prog -> memrchr_armv8.memrchr_armv8 ⊆2 prog ->
  strlen_armv8.strlen_armv8 ⊆2 prog -> rr_prog ⊆2 prog.
Proof.
  intros prog P2 P1 P0. unfold rr_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono.
  rewrite <- (updateall2_subset _ _ P1). apply updateall2_mono. exact P2.
Qed.

Lemma strlen_post_addr: ∀ sp mem raddr p s a,
  strlen_proof.invs sp mem raddr p (option (bool*N))
    (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,0) -> a = 0x15f000.
Proof.
  intros sp mem raddr p s a H. unfold strlen_proof.invs in H.
  destruct a as [|q]; [discriminate H|].
  repeat (destruct q as [q|q|]; try discriminate H); first [reflexivity | discriminate H].
Qed.

Lemma mr_lv: ∀ lv sp mem raddr x19 x29 p c n s a b m,
  memrchr_defs.invs lv sp mem raddr x19 x29 p c n (option (bool*N))
    (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (b,m) -> m = lv.
Proof.
  intros lv sp mem raddr x19 x29 p c n s a b m H. unfold memrchr_defs.invs in H.
  destruct a as [|q]; [discriminate H|].
  repeat (destruct q as [q|q|]; try discriminate H); inversion H; reflexivity.
Qed.

Lemma rr_noassign_x19: prog_noassign R_X19 strlen_armv8.strlen_armv8.
Proof. prove_noassign. Qed.

Theorem strlen_correct_in_strrchr:
  ∀ s t xs' (ENTRY: startof t xs' = (Addr 0x15efa8, s)) (MDL: models arm8typctx s)
    sp mem raddr x19 x29 p c n
    (SP: s R_SP = sp ⊖ 48) (MEM: s V_MEM64 = rr_frame sp mem raddr x19 x29 c) (X30: s R_X30 = 0x15f240)
    (X0: s R_X0 = p) (X19: s R_X19 = p),
  satisfies_all rr_prog (invs0 sp mem raddr x19 x29 p c n) (exits0 sp mem raddr x19 x29 p c n) (xs'::t).
Proof.
  intros.
  assert (RNG: ∀ s0 a insn, strlen_armv8.strlen_armv8 s0 a = Some insn ->
            (a =? 0x15f228) = false /\ (a <? 0x15efa8) = false /\ (a <? 0x15f228) = true).
  { intros s0 a insn IL. unfold strlen_armv8.strlen_armv8 in IL.
    destruct a as [|q]; [discriminate IL|].
    repeat (destruct q as [q|q|]; try discriminate IL); split; first [reflexivity | discriminate IL | split; reflexivity]. }
  assert (XE: exits0 sp mem raddr x19 x29 p c n = make_exits 0 strlen_armv8.strlen_armv8
                 (strlen_proof.invs (sp ⊖ 48) (rr_frame sp mem raddr x19 x29 c) 0x15f240 p)).
  { extensionality tt. destruct tt as [|[[a|i] s0] t0]; try reflexivity.
    unfold exits0, make_exits. destruct (strlen_armv8.strlen_armv8 s0 a) as [insn|] eqn:IL.
    - rewrite (rr_contains0 _ _ _ IL). destruct (RNG _ _ _ IL) as (E1 & E2 & E3).
      unfold invs. rewrite E1, E2, E3. reflexivity.
    - destruct (rr_prog s0 a) eqn:IL2; [|reflexivity].
      unfold invs. destruct (a =? 0x15f228); [reflexivity|].
      destruct (a <? 0x15efa8).
      + match goal with |- context [memrchr_defs.invs ?l ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?T ?I ?P ?NI s0 a] =>
          destruct (memrchr_defs.invs l a1 a2 a3 a4 a5 a6 a7 a8 T I P NI s0 a) as [[b m]|] eqn:F end;
        [apply mr_lv in F; subst m; destruct b; reflexivity | reflexivity].
      + destruct (a <? 0x15f228); [|reflexivity].
        destruct (strlen_proof.invs _ _ _ _ _ _ _ _ s0 a) as [[[|] m]|] eqn:F; try reflexivity.
        destruct (N.eqb_spec m 0); [|reflexivity]. subst m.
        apply strlen_post_addr in F. subst a. vm_compute in IL. discriminate IL. }
  unfold invs0. rewrite XE.
  apply satisfies_all_transfer with (p1 := strlen_armv8.strlen_armv8)
    (I1 := keep_invs (make_invs 0 strlen_armv8.strlen_armv8 (strlen_proof.invs (sp ⊖ 48) (rr_frame sp mem raddr x19 x29 c) 0x15f240 p)) R_X19 p).
  - exact rr_contains0.
  - intros a s0 t0 _ N0. unfold keep_invs, make_invs. rewrite N0. reflexivity.
  - intros a s0 t0 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s0 t0 insn IL. unfold keep_invs, make_invs. rewrite (rr_contains0 _ _ _ IL), IL.
    destruct (RNG _ _ _ IL) as (E1 & E2 & E3). unfold invs. rewrite E1, E2, E3. cbv iota.
    clear - IL. unfold strlen_armv8.strlen_armv8 in IL.
    destruct a as [|q]; [discriminate IL|].
    repeat (destruct q as [q|q|]; try discriminate IL); reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (satisfies_all_keep _ _ _ R_X19 p rr_noassign_x19 xs' t).
    + match goal with |- snd ?x _ = _ => replace x with (Addr 0x15efa8, s) by (symmetry; exact ENTRY) end. exact X19.
    + intros xs1 t1 START. assert (START2: startof t1 xs1 = (Addr 0x15efa8, s)) by (rewrite START; exact ENTRY). clear START.
      eapply strlen_partial_correctness; try eassumption. apply pf2sub_refl.
Qed.

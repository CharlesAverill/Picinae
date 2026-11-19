(* getenv: __strchrnul (level 1) and strncmp (level 2) proofs transferred into the getenv invariant family (GrokCall + GrokKeep).
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in getenv_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require getenv_armv8 strncmp_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCall GrokKeep.
From Grok.proofs Require strchrnul_proof strncmp_proof.
From Grok.proofs Require Import getenv_defs.
Import ARM8Notations.
Open Scope N.

Lemma gv_post_lv: ∀ sp mem raddr x19 x20 x21 x29 name L q k19 s a m,
  invs sp mem raddr x19 x20 x21 x29 name L q k19 (option (bool*N))
    (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s a = Some (true,m) ->
  (m = 3 /\ a = 0x11ffd4) \/ (m = 2 /\ a = 0x15f140) \/ (m = 1 /\ (a = 0x15ec40 \/ a = 0x15eca0)) \/ (m = 0 /\ a = 0x15f000).
Proof.
  intros until m. intro H. unfold invs, strncmp_proof.invs, strchrnul_proof.invs in H.
  destruct a as [|q0]; [discriminate H|].
  repeat (destruct q0 as [q0|q0|]; try discriminate H); injection H as <-; tauto.
Qed.

Lemma sc_noassign: ∀ name vx, In vx (gv_KC name) -> prog_noassign (fst vx) strchrnul_proof.strchrnul_prog.
Proof. intros name vx IN. destruct IN as [<-|[]]. simpl. prove_noassign. Qed.

Lemma sn_noassign: ∀ name L k19 vx, In vx (gv_KS name L k19) -> prog_noassign (fst vx) strncmp_armv8.strncmp_armv8.
Proof. intros name L k19 vx IN. simpl in IN. destruct IN as [<-|[<-|[<-|[]]]]; simpl; prove_noassign. Qed.

Theorem strchrnul_correct_in_getenv:
  ∀ sp mem raddr x19 x20 x21 x29 name L q k19 s t xs'
    (ENTRY: startof t xs' = (Addr 0x15ebf4, s)) (MDL: models arm8typctx s)
    (SP: s R_SP = sp ⊖ 48) (MEM: s V_MEM64 = gv_M sp mem raddr x19 x20 x21 x29) (X30: s R_X30 = 0x11ffa4)
    (X0: s R_X0 = name) (X1: s R_X1 = 0x3d) (X29: s R_X29 = sp ⊖ 48) (X21: s R_X21 = name),
  satisfies_all gv_prog (gv_invs1 sp mem raddr x19 x20 x21 x29 name L q k19)
                        (gv_exits1 sp mem raddr x19 x20 x21 x29 name L q k19) (xs'::t).
Proof.
  intros.
  set (SCI := strchrnul_proof.invs (sp ⊖ 48) (gv_M sp mem raddr x19 x20 x21 x29) 0x11ffa4 name 0x3d (sp ⊖ 48)).
  assert (XE: gv_exits1 sp mem raddr x19 x20 x21 x29 name L q k19 = make_exits 1 strchrnul_proof.strchrnul_prog SCI).
  { extensionality tt. destruct tt as [|[[a|i] s1] t1]; try reflexivity.
    unfold gv_exits1, make_exits. destruct (strchrnul_proof.strchrnul_prog s1 a) as [insn|] eqn:IL.
    - rewrite (gv_contains1 _ _ _ IL). clear - IL.
      unfold strchrnul_proof.strchrnul_prog, updateall2, updateall, strlen_armv8.strlen_armv8, strchrnul_armv8.strchrnul_armv8 in IL.
      destruct a as [|q0]; [discriminate IL|]. repeat (destruct q0 as [q0|q0|]; try discriminate IL); reflexivity.
    - destruct (gv_prog s1 a) eqn:IL2; [|reflexivity].
      destruct (invs sp mem raddr x19 x20 x21 x29 name L q k19 _ (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a)
        as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 1); [|reflexivity]. subst m.
      apply gv_post_lv in F. destruct F as [(F&_)|[(F&_)|[(_&[F|F])|(F&_)]]]; try discriminate F; subst a; vm_compute in IL; discriminate IL. }
  unfold gv_invs1. rewrite XE.
  apply satisfies_all_transfer with (p1 := strchrnul_proof.strchrnul_prog)
    (I1 := keepl_invs (make_invs 1 strchrnul_proof.strchrnul_prog SCI) (gv_KC name)).
  - exact gv_contains1.
  - intros a s1 t1 _ N0. unfold keepl_invs, make_invs. rewrite N0. reflexivity.
  - intros a s1 t1 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s1 t1 insn IL. clear - IL.
    unfold strchrnul_proof.strchrnul_prog, updateall2, updateall, strlen_armv8.strlen_armv8, strchrnul_armv8.strchrnul_armv8 in IL.
    destruct a as [|q0]; [discriminate IL|]. repeat (destruct q0 as [q0|q0|]; try discriminate IL); reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (satisfies_all_keepl _ _ _ (gv_KC name) (sc_noassign name) xs' t).
    + match goal with |- keepl_st _ (snd ?x) => replace x with (Addr 0x15ebf4, s) by (symmetry; exact ENTRY) end.
      simpl. split; [exact X21 | exact I].
    + intros xs1 t1 START. assert (START2: startof t1 xs1 = (Addr 0x15ebf4, s)) by (rewrite START; exact ENTRY). clear START.
      eapply strchrnul_proof.strchrnul_partial_correctness; try eassumption.
      * exact strchrnul_proof.strchrnul_prog_contains.
      * apply subset_updateall2.
Qed.

Theorem strncmp_correct_in_getenv:
  ∀ sp mem raddr x19 x20 x21 x29 name L q k19 s t xs'
    (ENTRY: startof t xs' = (Addr 0x15f110, s)) (MDL: models arm8typctx s)
    (SP: s R_SP = sp ⊖ 48) (MEM: s V_MEM64 = gv_M sp mem raddr x19 x20 x21 x29) (X30: s R_X30 = 0x11fff0)
    (X0: s R_X0 = name) (X1: s R_X1 = q) (X2: s R_X2 = L)
    (X19: s R_X19 = k19) (X20: s R_X20 = L) (X21: s R_X21 = name),
  satisfies_all gv_prog (gv_invs2 sp mem raddr x19 x20 x21 x29 name L q k19)
                        (gv_exits2 sp mem raddr x19 x20 x21 x29 name L q k19) (xs'::t).
Proof.
  intros.
  set (SNI := strncmp_proof.invs (sp ⊖ 48) (gv_M sp mem raddr x19 x20 x21 x29) 0x11fff0 name q L).
  assert (XE: gv_exits2 sp mem raddr x19 x20 x21 x29 name L q k19 = make_exits 0 strncmp_armv8.strncmp_armv8 SNI).
  { extensionality tt. destruct tt as [|[[a|i] s1] t1]; try reflexivity.
    unfold gv_exits2, make_exits. destruct (strncmp_armv8.strncmp_armv8 s1 a) as [insn|] eqn:IL.
    - rewrite (gv_contains2 _ _ _ IL). clear - IL. unfold strncmp_armv8.strncmp_armv8 in IL.
      destruct a as [|q0]; [discriminate IL|]. repeat (destruct q0 as [q0|q0|]; try discriminate IL); reflexivity.
    - destruct (gv_prog s1 a) eqn:IL2; [|reflexivity].
      destruct (invs sp mem raddr x19 x20 x21 x29 name L q k19 _ (fun m _ => Some (false,m)) (fun m _ => Some (true,m)) None s1 a)
        as [[[|] m]|] eqn:F; try reflexivity.
      destruct (N.eqb_spec m 2); [|reflexivity]. subst m.
      apply gv_post_lv in F. destruct F as [(F&_)|[(_&F)|[(F&_)|(F&_)]]]; try discriminate F; subst a; vm_compute in IL; discriminate IL. }
  unfold gv_invs2. rewrite XE.
  apply satisfies_all_transfer with (p1 := strncmp_armv8.strncmp_armv8)
    (I1 := keepl_invs (make_invs 0 strncmp_armv8.strncmp_armv8 SNI) (gv_KS name L k19)).
  - exact gv_contains2.
  - intros a s1 t1 _ N0. unfold keepl_invs, make_invs. rewrite N0. reflexivity.
  - intros a s1 t1 H N0. unfold make_exits in H. rewrite N0 in H. discriminate H.
  - intros a s1 t1 insn IL. clear - IL. unfold strncmp_armv8.strncmp_armv8 in IL.
    destruct a as [|q0]; [discriminate IL|]. repeat (destruct q0 as [q0|q0|]; try discriminate IL); reflexivity.
  - reflexivity.
  - reflexivity.
  - apply (satisfies_all_keepl _ _ _ (gv_KS name L k19) (sn_noassign name L k19) xs' t).
    + match goal with |- keepl_st _ (snd ?x) => replace x with (Addr 0x15f110, s) by (symmetry; exact ENTRY) end.
      simpl. repeat split; assumption.
    + intros xs1 t1 START. assert (START2: startof t1 xs1 = (Addr 0x15f110, s)) by (rewrite START; exact ENTRY). clear START.
      eapply strncmp_proof.strncmp_partial_correctness; try eassumption. apply pf2sub_refl.
Qed.

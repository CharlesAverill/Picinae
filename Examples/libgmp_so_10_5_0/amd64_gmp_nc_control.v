Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
(* Entry, tail, and full-block control-flow verification conditions.
   Full-block store continuations use [abstract] to keep kernel checking fast. *)
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_proof.
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.


Lemma nc_cf_post_store_eq : forall sub m0 d u v n cin s s',
  s R_CF=s' R_CF -> s V_MEM64=s' V_MEM64 ->
  nc_cf_post sub m0 d u v n cin s -> nc_cf_post sub m0 d u v n cin s'.
Proof.
  intros sub m0 d u v n cin s s' CF MEM.
  unfold nc_cf_post. rewrite <-CF, <-MEM. exact (fun P => P).
Qed.

Lemma nc_vc_tail_store : forall sub a m0 d u v n cin s t,
  models x64typctx s -> 8*n<=2^64 ->
  (a=0x128521 \/ a=0x128536 \/ a=0x12854f) ->
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub a),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub a),s)::t).
Proof.
  intros sub a m0 d u v n cin s t MDL B CASE PRE.
  destruct CASE as [A|[A|A]]; subst a; destruct sub;
    cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k PRE]; unfold nc_stage,nc_ptrs in PRE; nc_conj.
  all: match goal with P : nc_prefix ?sub ?m0 ?d ?u ?v ?cin ?k ?q ?s,
         NK : ?n = ?k + ?count |- _ =>
    let q := eval vm_compute in q in
    pose proof (nc_commit_last sub m0 d u v n cin k q s MDL B NK P) as COMMIT end.
  all: cbn [nc_program nc_address]; nc_bigstep;
    split; [ | psimpl; assumption ].
  all: eapply nc_cf_post_store_eq; [ | | exact COMMIT ];
    cbn [nc_write_buffer]; nc_updates; psimpl;
    repeat match goal with H : ?s R_RDI = _ |- _ => progress rewrite H end;
    psimpl;
    try replace (8+d+8*k) with (d+8*k+8) by (clear; lia);
    try replace (16+d+8*k) with (d+8*k+16) by (clear; lia);
    reflexivity.
Qed.

Ltac nc_keep_prefix :=
  match goal with P : nc_prefix ?sub ?m0 ?d ?u ?v ?cin ?k ?q ?s
  |- nc_prefix ?sub ?m0 ?d ?u ?v ?cin ?k ?q _ =>
    eapply nc_prefix_store_eq; [ | | | exact P ];
    cbn [buffered]; nc_updates; reflexivity
  end.

Lemma nc_vc_tail_load1 : forall sub m0 d u v n cin s t,
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x128517),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x128517),s)::t).
Proof.
  intros sub m0 d u v n cin s t PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k [KN [REM [PTR [UN [PREFIX AX]]]]]];
    destruct PTR as [DI [SI DX]];
    pose proof (proj1 (unread_limb m0 (s V_MEM64) u v n k 0 UN ltac:(clear -KN; lia))) as U;
    rewrite N.add_0_r in U;
    change ((s V_MEM64) Ⓠ[u+8*k]=value m0 (u+8*k) 1) in U;
    assert (CASE : n-k=1 \/ n-k=2 \/ n-k=3) by (clear -KN REM; lia);
    destruct CASE as [E|[E|E]]; rewrite E in AX;
    cbn [nc_program nc_address]; nc_bigstep;
    rewrite ?AX in *; try discriminate;
    exists k; unfold nc_stage,nc_ptrs,preloaded; psimpl;
    rewrite ?DI,?SI,?DX,?U; psimpl; rewrite ?U;
    repeat first [assumption | reflexivity | solve [nc_keep_prefix] |
      match goal with |- _ /\ _ => split end |
      solve [rewrite E; reflexivity] |
      solve [intros; repeat split; intros; try assumption; try reflexivity;
        exfalso; match goal with H : ?a <= ?b |- _ => clear -H; lia end] |
      solve [intros; clear -KN E; lia] |
      solve [clear -KN E; lia] ].
Qed.

Lemma nc_vc_tail_load2 : forall sub m0 d u v n cin s t,
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x128527),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x128527),s)::t).
Proof.
  intros sub m0 d u v n cin s t PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k [KN [REM [PTR [UN [PREFIX [AX LOAD]]]]]]];
    destruct PTR as [DI [SI DX]];
    assert (L8 : s R_R8=value m0 (u+8*k) 1) by (apply (proj1 LOAD); vm_compute; easy);
    pose proof (proj1 (unread_limb m0 (s V_MEM64) u v n k 1 UN ltac:(clear -KN; lia))) as U;
    change ((s V_MEM64) Ⓠ[u+8*(k+1)]=value m0 (u+8*(k+1)) 1) in U;
    replace (u+8*(k+1)) with (8+u+8*k) in U at 1 by (clear; nia);
    assert (CASE : n-k=2 \/ n-k=3) by (clear -KN REM; lia);
    destruct CASE as [E|E]; rewrite E in AX;
    cbn [nc_program nc_address]; nc_bigstep;
    rewrite ?AX in *; try discriminate;
    exists k; unfold nc_stage,nc_ptrs,preloaded; psimpl;
    rewrite ?DI,?SI,?DX,?L8; psimpl; rewrite ?U;
    repeat first [assumption | reflexivity | solve [nc_keep_prefix] |
      match goal with |- _ /\ _ => split end |
      solve [rewrite E; reflexivity] |
      solve [intros; repeat split; intros; try assumption; try reflexivity;
        exfalso; match goal with H : ?a <= ?b |- _ => clear -H; lia end] |
      solve [clear -KN E; lia] ].
Qed.

Lemma nc_vc_tail_load3 : forall sub m0 d u v n cin s t,
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x128540),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x128540),s)::t).
Proof.
  intros sub m0 d u v n cin s t PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k [NK [PTR [UN [PREFIX [AX LOAD]]]]]];
    destruct PTR as [DI [SI DX]];
    assert (L8 : s R_R8=value m0 (u+8*k) 1) by (apply (proj1 LOAD); vm_compute; easy);
    assert (L9 : s R_R9=value m0 (u+8*(k+1)) 1) by (apply (proj1 (proj2 LOAD)); reflexivity);
    pose proof (proj1 (unread_limb m0 (s V_MEM64) u v n k 2 UN ltac:(clear -NK; lia))) as U;
    change ((s V_MEM64) Ⓠ[u+8*(k+2)]=value m0 (u+8*(k+2)) 1) in U;
    replace (u+8*(k+2)) with (16+u+8*k) in U at 1 by (clear; nia);
    cbn [nc_program nc_address]; nc_bigstep;
    exists k; unfold nc_stage,nc_ptrs; psimpl;
    rewrite ?DI,?SI,?DX,?AX; psimpl;
    repeat first [assumption | reflexivity | solve [nc_keep_prefix] |
      match goal with |- _ /\ _ => split end |
      solve [nc_inputs] | solve [clear -NK; lia] ].
  all: unfold remaining_inputs; intros i LO HI;
    assert (CASE : i=0 \/ i=1 \/ i=2) by (clear -HI; lia);
    destruct CASE as [E|[E|E]]; subst i; psimpl; nc_updates;
    rewrite ?N.add_0_r; assumption.
Qed.

Lemma nc_prefix_complete : forall sub m0 d u v n cin s,
  nc_prefix sub m0 d u v cin n 0 s -> nc_cf_post sub m0 d u v n cin s.
Proof.
  intros sub m0 d u v n cin s P.
  unfold nc_prefix in P. cbn [buffered] in P.
  rewrite N.mul_0_r, !N.add_0_r in P.
  exact (conj (proj1 P) (proj2 (proj2 P))).
Qed.

Lemma nc_vc_remainder_dispatch : forall sub m0 d u v n cin s t,
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x1285ca),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x1285ca),s)::t).
Proof.
  intros sub m0 d u v n cin s t PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k [KN [REM [KM [PTR [UN [PREFIX AX]]]]]]];
    destruct PTR as [DI [SI DX]];
    assert (CASE : n-k=0 \/ n-k=1 \/ n-k=2 \/ n-k=3) by (clear -REM; lia);
    destruct CASE as [E|[E|[E|E]]]; rewrite E in AX;
    cbn [nc_program nc_address]; nc_bigstep;
    rewrite ?AX in *; try discriminate;
    first [exists k | idtac]; unfold nc_ptrs; psimpl;
    rewrite ?DI,?SI,?DX; psimpl;
    repeat first [assumption | reflexivity | solve [nc_keep_prefix] |
      match goal with |- _ /\ _ => split end |
      solve [rewrite E; reflexivity] |
      solve [clear -KN E; lia] |
      solve [apply nc_prefix_complete;
        replace n with k by (clear -KN E; lia); nc_keep_prefix] ].
Qed.

Lemma nc_vc_block_dispatch : forall sub m0 d u v n cin s t,
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x128594),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x128594),s)::t).
Proof.
  intros sub m0 d u v n cin s t PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k [KN [KM [PTR [UN [PREFIX [AX [CX [ZF LOAD]]]]]]]]];
    destruct PTR as [DI [SI DX]];
    assert (L8 : s R_R8=value m0 (u+8*k) 1) by (apply (proj1 LOAD); vm_compute; easy);
    assert (L9 : s R_R9=value m0 (u+8*(k+1)) 1) by (apply (proj1 (proj2 LOAD)); vm_compute; easy);
    pose proof (proj1 (unread_limb m0 (s V_MEM64) u v n k 2 UN ltac:(clear -KN; lia))) as U2;
    pose proof (proj1 (unread_limb m0 (s V_MEM64) u v n k 3 UN ltac:(clear -KN; lia))) as U3;
    change ((s V_MEM64) Ⓠ[u+8*(k+2)]=value m0 (u+8*(k+2)) 1) in U2;
    change ((s V_MEM64) Ⓠ[u+8*(k+3)]=value m0 (u+8*(k+3)) 1) in U3;
    replace (u+8*(k+2)) with (16+u+8*k) in U2 at 1 by (clear; nia);
    replace (u+8*(k+3)) with (24+u+8*k) in U3 at 1 by (clear; nia);
    rewrite CX in ZF;
    destruct ((n-k)/4-1 =? 0) eqn:CZ;
    (apply N.eqb_eq in CZ || apply N.eqb_neq in CZ);
    pose proof (N.div_mod (n-k) 4 ltac:(discriminate)) as DIV;
    pose proof (N.mod_lt (n-k) 4 ltac:(discriminate)) as MOD;
    cbn [nc_program nc_address]; nc_bigstep;
    rewrite ?ZF in *; try discriminate;
    exists k; unfold nc_ptrs,preloaded; psimpl;
    rewrite ?DI,?SI,?DX,?AX,?CX,?L8,?L9; psimpl; rewrite ?U2,?U3;
    repeat first [assumption | reflexivity | solve [nc_keep_prefix] |
      match goal with |- _ /\ _ => split end |
      solve [intros; discriminate] |
      solve [intros; repeat split; intros; try reflexivity; try assumption;
        exfalso; match goal with H : ?a <= ?b |- _ => clear -H; lia end] |
      solve [clear -KN CZ DIV MOD; nia] ].
Qed.

Lemma nc_vc_final_advance : forall sub m0 d u v n cin s t,
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x12859e),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x12859e),s)::t).
Proof.
  intros sub m0 d u v n cin s t PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k [KN [REM [KM [PTR [UN [PREFIX [AX [CX [LOAD REST]]]]]]]]]];
    destruct PTR as [DI [SI DX]];
    specialize (LOAD eq_refl);
    cbn [nc_program nc_address]; nc_bigstep;
    exists k; unfold nc_stage,nc_ptrs; psimpl;
    rewrite ?DI,?SI,?DX,?AX,?CX; psimpl;
    replace (u+8*(k+4)) with (32+u+8*k) by (clear; nia);
    repeat first [assumption | reflexivity | solve [nc_keep_prefix] |
      match goal with |- _ /\ _ => split end | solve [clear -KN; lia] ].
  all: unfold remaining_inputs; intros i LO HI;
    assert (CASE : i=0 \/ i=1 \/ i=2 \/ i=3) by (clear -HI; lia);
    destruct CASE as [E|[E|[E|E]]]; subst i; psimpl; nc_updates; rewrite ?N.add_0_r;
    unfold preloaded in LOAD; nc_conj;
    match goal with H : _ -> ?x = ?y |- ?x = ?y => apply H; vm_compute; easy end.
Qed.

Lemma nc_div_next : forall n k,
  k+4<=n -> (n-(k+4))/4=(n-k)/4-1.
Proof.
  intros n k B.
  replace (n-k) with ((n-(k+4))+1*4) by lia.
  rewrite N.div_add by discriminate. lia.
Qed.
Lemma nc_mod_next : forall k, k mod 4=0 -> (k+4) mod 4=0.
Proof. intros k K. rewrite N.Div0.add_mod, K. reflexivity. Qed.
Lemma nc_remainder_after_block : forall n k,
  k+4<=n -> n-k<8 -> k mod 4=0 -> n mod 4=n-(k+4).
Proof.
  intros n k B R K.
  replace n with (k+4+(n-(k+4))) at 1 by lia.
  rewrite N.Div0.add_mod, nc_mod_next by exact K.
  rewrite N.add_0_l, N.Div0.mod_mod.
  apply N.mod_small. lia.
Qed.
Lemma nc_dec_zf : forall c,
  1<=c -> c<2^64 ->
  (if c mod 2^64 =? 1 then 1 else 0)=(if c-1 =? 0 then 1 else 0).
Proof.
  intros c C B. rewrite N.mod_small by exact B.
  destruct (c =? 1) eqn:E.
  - apply N.eqb_eq in E. subst c. reflexivity.
  - apply N.eqb_neq in E.
    assert (F : (c-1 =? 0)=false) by (apply N.eqb_neq; lia).
    rewrite F. reflexivity.
Qed.

Lemma nc_commit_block : forall sub m0 d u v n cin k s,
  models x64typctx s -> 8*n<=2^64 -> k+4<=n ->
  forward_safe d u n -> forward_safe d v n ->
  unread m0 (s V_MEM64) u v n k -> nc_prefix sub m0 d u v cin k 4 s ->
  let m1 := nc_write_buffer s (d+8*k) 4 in
  unread m0 m1 u v n (k+4) /\
  nc_prefix sub m0 d u v cin (k+4) 0 (s[V_MEM64:=m1]).
Proof.
  intros sub m0 d u v n cin k s MDL B KN SAFE_U SAFE_V UN P.
  cbn zeta. rewrite nc_write_buffer_eq by (try exact MDL; reflexivity).
  split.
  - eapply unread_commit; try eassumption.
    eapply unread_shrink; eassumption.
  - eapply nc_prefix_commit; eassumption.
Qed.

Lemma nc_eax_remainder : forall n,
  scast 32 64 ((n mod 2^32 >> 0) mod 2^32 .& 3) mod 2^32=n mod 4.
Proof.
  intros n. psimpl.
  change 3 with (N.ones 2).
  rewrite N.land_ones, mp2_mod_mod_min.
  change (N.min 32 2) with 2.
  rewrite N.shiftr_0_r, mp2_mod_mod_min.
  change (N.min 32 2) with 2. change (2^2) with 4.
  assert (B : n mod 4<4) by (apply N.mod_lt; discriminate).
  assert (CASE : n mod 4=0 \/ n mod 4=1 \/ n mod 4=2 \/ n mod 4=3) by lia.
  destruct CASE as [E|[E|[E|E]]]; rewrite E; reflexivity.
Qed.

Ltac nc_fold_store s d k :=
  replace (8+d+8*k) with (d+8*k+8) by (clear; nia);
  replace (16+d+8*k) with (d+8*k+16) by (clear; nia);
  replace (24+d+8*k) with (d+8*k+24) by (clear; nia);
  change ((s V_MEM64)[Ⓠd+8*k:=s R_R8][Ⓠd+8*k+8:=s R_R9]
    [Ⓠd+8*k+16:=s R_R10][Ⓠd+8*k+24:=s R_R11])
    with (nc_write_buffer s (d+8*k) 4).

Lemma nc_vc_cycle : forall sub m0 d u v n cin s t,
  models x64typctx s -> 8*n<=2^64 ->
  forward_safe d u n -> forward_safe d v n ->
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x12856f),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x12856f),s)::t).
Proof.
  intros sub m0 d u v n cin s t MDL B SAFE_U SAFE_V PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k [KN [KM [PTR [UN [PREFIX [AX [CX REST]]]]]]]];
    destruct PTR as [DI [SI DX]];
    pose proof (nc_commit_block _ m0 d u v n cin k s MDL B ltac:(clear -KN; lia)
      SAFE_U SAFE_V UN PREFIX) as [UN1 P1];
    set (m1 := nc_write_buffer s (d+8*k) 4) in *;
    pose proof (proj1 (unread_limb m0 m1 u v n (k+4) 0 UN1 ltac:(clear -KN; lia))) as U0;
    pose proof (proj1 (unread_limb m0 m1 u v n (k+4) 1 UN1 ltac:(clear -KN; lia))) as U1;
    rewrite N.add_0_r in U0;
    change (m1 Ⓠ[u+8*(k+4)]=value m0 (u+8*(k+4)) 1) in U0;
    change (m1 Ⓠ[u+8*(k+4+1)]=value m0 (u+8*(k+4+1)) 1) in U1;
    replace (u+8*(k+4)) with (32+u+8*k) in U0 at 1 by (clear; nia);
    replace (u+8*(k+4+1)) with (40+u+8*k) in U1 at 1 by (clear; nia);
    pose proof (N.div_mod (n-k) 4 ltac:(discriminate)) as DIV;
    pose proof (N.mod_lt (n-k) 4 ltac:(discriminate)) as MOD;
    assert (C1 : 1<=(n-k)/4-1) by (clear -KN DIV MOD; nia);
    assert (C64 : (n-k)/4-1<2^64) by (pose proof (N_div_le (n-k) 4); clear -B KN H; nia);
    assert (DEC : ((n-k)/4-1) ⊖ 1=(n-(k+4))/4-1) by
      (rewrite msub_sub by exact C1; rewrite N.mod_small by (clear -C64; lia);
       rewrite nc_div_next by (clear -KN; lia); lia);
    assert (ZT : (if ((n-k)/4-1) mod 2^64 =? 1 then 1 else 0)=
      (if (n-(k+4))/4-1 =? 0 then 1 else 0)) by
      (rewrite nc_dec_zf by assumption; rewrite nc_div_next by (clear -KN; lia);
       reflexivity);
    cbn [nc_program nc_address]; nc_bigstep;
    abstract (exists (k+4); unfold nc_ptrs,preloaded; psimpl;
    rewrite ?DI,?SI,?DX,?AX,?CX; psimpl;
    nc_fold_store s d k; fold m1;
    replace (4+k) with (k+4) by (clear; lia);
    rewrite ?DEC,?ZT,?U0,?U1;
    replace (d+8*(k+4)) with (32+d+8*k) by (clear; nia);
    replace (u+8*(k+4)) with (32+u+8*k) by (clear; nia);
    replace (v+8*(k+4)) with (32+v+8*k) by (clear; nia);
    repeat first [assumption | reflexivity | solve [nc_keep_prefix] |
      match goal with |- _ /\ _ => split end |
      solve [apply nc_mod_next; exact KM] |
      solve [intros; repeat split; intros; try assumption; try reflexivity;
        exfalso; match goal with H : ?a <= ?b |- _ => clear -H; lia end] |
      solve [clear -KN; lia] ]).
Qed.

Lemma nc_eax_inc_small : forall r,
  r<4 -> scast 32 64 (((r >> 0) mod 2^32+1) mod 2^32) mod 2^32=r+1.
Proof.
  intros r B. assert (CASE : r=0 \/ r=1 \/ r=2 \/ r=3) by lia.
  destruct CASE as [E|[E|[E|E]]]; subst r; reflexivity.
Qed.

Lemma nc_vc_final_store : forall sub m0 d u v n cin s t,
  models x64typctx s -> 8*n<=2^64 ->
  forward_safe d u n -> forward_safe d v n ->
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x1285b1),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x1285b1),s)::t).
Proof.
  intros sub m0 d u v n cin s t MDL B SAFE_U SAFE_V PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [k [KN [REM [KM [PTR [UN [PREFIX [AX [CX REST]]]]]]]]];
    destruct PTR as [DI [SI DX]];
    change (s R_RSI=(u+8*(k+4)) mod 2^64) in SI;
    pose proof (nc_commit_block _ m0 d u v n cin k s MDL B KN
      SAFE_U SAFE_V UN PREFIX) as [UN1 P1];
    set (m1 := nc_write_buffer s (d+8*k) 4) in *;
    pose proof (nc_remainder_after_block n k KN REM KM) as RM;
    cbn [nc_program nc_address]; nc_bigstep;
    abstract (exists (k+4); unfold nc_ptrs; psimpl;
    rewrite ?DI,?SI,?DX,?AX; psimpl;
    nc_fold_store s d k; fold m1;
    replace (4+k) with (k+4) by (clear; lia);
    replace (d+8*(k+4)) with (32+d+8*k) by (clear; nia);
    replace (v+8*(k+4)) with (32+v+8*k) by (clear; nia);
    repeat first [assumption | reflexivity | solve [nc_keep_prefix] |
      match goal with |- _ /\ _ => split end |
      solve [apply nc_mod_next; exact KM] |
      solve [rewrite nc_eax_inc_small by (apply N.mod_lt; discriminate); rewrite RM; clear; lia] |
      solve [clear -KN REM; lia] ]).
Qed.

Lemma nc_prefix_initial : forall sub m0 d u v cin s,
  cin<=1 -> s R_CF=cin -> nc_prefix sub m0 d u v cin 0 0 s.
Proof.
  intros sub m0 d u v cin s C CF.
  unfold nc_prefix,nc_equation. cbn [buffered].
  rewrite !value_zero, CF. change (radix 0) with 1. change (radix (0+0)) with 1.
  destruct sub; repeat split; lia.
Qed.
Lemma nc_input_bit : forall c,
  c<=1 -> (if negb (c >> (0 .& 63) .& 1 =? 0) then 1 else 0)=c.
Proof.
  intros c B. assert (CASE : c=0 \/ c=1) by lia.
  destruct CASE as [E|E]; subst c; reflexivity.
Qed.

Lemma nc_vc_entry : forall sub m0 d u v n cin s t,
  models x64typctx s -> 0<n -> cin<=1 ->
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub 0x1284e0),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x1284e0),s)::t).
Proof.
  intros sub m0 d u v n cin s t MDL POS C PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [MEM [DI [SI [DX [CX CI]]]]];
    assert (D64 : d<2^64) by (pose proof (models_var R_RDI MDL) as H; rewrite DI in H; exact H);
    assert (U64 : u<2^64) by (pose proof (models_var R_RSI MDL) as H; rewrite SI in H; exact H);
    assert (V64 : v<2^64) by (pose proof (models_var R_RDX MDL) as H; rewrite DX in H; exact H);
    assert (N64 : n<2^64) by (pose proof (models_var R_RCX MDL) as H; rewrite CX in H; exact H);
    assert (Q64 : n/4<2^64) by (pose proof (N_div_le n 4); clear -N64 H; lia);
    pose proof (N.div_mod n 4 ltac:(discriminate)) as DIV;
    pose proof (N.mod_lt n 4 ltac:(discriminate)) as MOD;
    cbn [nc_program nc_address]; nc_bigstep;
    rewrite ?MEM,?DI,?SI,?DX,?CX,?CI in *;
    rewrite ?nc_eax_remainder,?nc_input_bit by exact C;
    rewrite ?N.shiftr_div_pow2 in *;
    change (2^2) with 4 in *;
    exists 0; unfold nc_ptrs,unread,preloaded; psimpl;
    rewrite ?nc_eax_remainder,?nc_input_bit by exact C;
    repeat first [assumption | reflexivity |
      solve [apply nc_prefix_initial; [exact C | nc_updates; reflexivity]] |
      match goal with |- _ /\ _ => split end |
      solve [rewrite N.mod_small by assumption; reflexivity] |
      solve [intros; repeat split; intros; try reflexivity;
        exfalso; match goal with H : ?a <= ?b |- _ => clear -H; lia end] ].
  all: try solve [intros;
    try replace (u+8*0) with u by (clear; nia);
    try replace (u+8*(0+1)) with (8+u) by (clear; nia); reflexivity].
  all: try solve [match goal with H : (?n/4 =? 0)=true |- _ =>
    apply N.eqb_eq in H; clear -DIV MOD H; nia end].
  all: try solve [match goal with H : (?n/4 =? 0)=false |- _ =>
    apply N.eqb_neq in H;
    first [clear -DIV H; nia |
      rewrite N.sub_0_r, msub_sub by (clear -H; lia);
      apply N.mod_small; clear -Q64; lia] end].
Qed.

Lemma nc_vc_plain_entry : forall sub m0 d u v n s t,
  models x64typctx s -> 0<n ->
  true_inv (nc_invset sub m0 d u v n 0 ((Addr (nc_address sub 0x128500),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n 0) (nc_exit sub) false
    ((Addr (nc_address sub 0x128500),s)::t).
Proof.
  intros sub m0 d u v n s t MDL POS PRE.
  destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    destruct PRE as [MEM [DI [SI [DX [CX CZ]]]]];
    assert (C : 0<=1) by (vm_compute; easy);
    assert (D64 : d<2^64) by (pose proof (models_var R_RDI MDL) as H; rewrite DI in H; exact H);
    assert (U64 : u<2^64) by (pose proof (models_var R_RSI MDL) as H; rewrite SI in H; exact H);
    assert (V64 : v<2^64) by (pose proof (models_var R_RDX MDL) as H; rewrite DX in H; exact H);
    assert (N64 : n<2^64) by (pose proof (models_var R_RCX MDL) as H; rewrite CX in H; exact H);
    assert (Q64 : n/4<2^64) by (pose proof (N_div_le n 4); clear -N64 H; lia);
    pose proof (N.div_mod n 4 ltac:(discriminate)) as DIV;
    pose proof (N.mod_lt n 4 ltac:(discriminate)) as MOD;
    cbn [nc_program nc_address]; nc_bigstep;
    rewrite ?MEM,?DI,?SI,?DX,?CX in *;
    rewrite ?nc_eax_remainder,?nc_input_bit by exact C;
    rewrite ?N.shiftr_div_pow2 in *;
    change (2^2) with 4 in *;
    exists 0; unfold nc_ptrs,unread,preloaded; psimpl;
    rewrite ?nc_eax_remainder,?nc_input_bit by exact C;
    repeat first [assumption | reflexivity |
      solve [apply nc_prefix_initial; [exact C | nc_updates; reflexivity]] |
      match goal with |- _ /\ _ => split end |
      solve [rewrite N.mod_small by assumption; reflexivity] |
      solve [intros; repeat split; intros; try reflexivity;
        exfalso; match goal with H : ?a <= ?b |- _ => clear -H; lia end] ].
  all: try solve [intros;
    try replace (u+8*0) with u by (clear; nia);
    try replace (u+8*(0+1)) with (8+u) by (clear; nia); reflexivity].
  all: try solve [match goal with H : (?n/4 =? 0)=true |- _ =>
    apply N.eqb_eq in H; clear -DIV MOD H; nia end].
  all: try solve [match goal with H : (?n/4 =? 0)=false |- _ =>
    apply N.eqb_neq in H;
    first [clear -DIV H; nia |
      rewrite N.sub_0_r, msub_sub by (clear -H; lia);
      apply N.mod_small; clear -Q64; lia] end].
Qed.

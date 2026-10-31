(* Shared arithmetic verification conditions and buffered-store lemmas.
   The whole-function theorems are in amd64_gmp_nc_correctness.v. *)
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_proof.
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Ltac nc_conj := repeat match goal with H : ?T |- _ =>
  lazymatch T with ?f ?a ?b => constr_eq f and; destruct H end end.

Lemma nc_prefix_store_eq : forall sub m0 d u v cin k q s s',
  s R_CF=s' R_CF -> s V_MEM64=s' V_MEM64 ->
  buffered s q=buffered s' q ->
  nc_prefix sub m0 d u v cin k q s -> nc_prefix sub m0 d u v cin k q s'.
Proof.
  intros sub m0 d u v cin k q s s' CF MEM BUF.
  unfold nc_prefix. rewrite <-CF, <-MEM, <-BUF. exact (fun P => P).
Qed.

Ltac nc_updates := repeat (rewrite update_updated || rewrite update_frame by discriminate).
Ltac nc_prefix_arithmetic :=
  match goal with NP : context [nc_prefix _ _ _ _ _ _ _ _ _] |- nc_prefix _ _ _ _ _ _ _ ?qp _ =>
    cbv beta zeta in NP;
    eapply nc_prefix_store_eq; [ | | | exact NP ];
    cbn [buffered pending_reg]; nc_updates;
    unfold limb_result, limb_carry, adc_flag, sbb_flag;
    match goal with RD : ?m Ⓠ[?v+8*(?k+?q)] = _ |- _ =>
      let q := eval vm_compute in q in
      let off := eval vm_compute in (8*q) in
      try replace (off+v+8*k) with (v+8*(k+q)) by (clear; nia);
      rewrite ?N.add_0_r in RD; rewrite ?N.add_0_r; rewrite ?RD
    end;
    repeat match goal with H : ?s ?r = _ |- _ => progress rewrite H end;
    try reflexivity;
    try (try rewrite (N.add_comm (2^64)); rewrite <-msub_repr64 by apply value_bound; reflexivity)
  end.

Ltac nc_arith_prepare PRE :=
  destruct PRE as [k PRE];
  unfold nc_stage, nc_ptrs, preloaded in PRE;
  nc_conj;
  repeat match goal with H : ?x = ?y -> _ |- _ => specialize (H (eq_refl : x=y)) end;
  nc_conj;
  match goal with
  | MDL : models x64typctx ?s,
    PREFIX : nc_prefix ?sub ?m0 ?d ?u ?v ?cin ?k ?q ?s,
    UN : unread ?m0 (?s V_MEM64) ?u ?v ?n ?k |- _ =>
    let q := eval vm_compute in q in
    let X := fresh "INPUT" in
    assert (X : s (pending_reg q)=value m0 (u+8*(k+q)) 1) by
      (cbn [pending_reg]; first [assumption |
       match goal with R : remaining_inputs _ _ _ _ _ _ |- _ =>
         exact (R q ltac:(vm_compute; easy) ltac:(vm_compute; easy)) end |
       rewrite ?N.add_0_r;
       match goal with R : _ -> s _ = _ |- _ => apply R; vm_compute; easy end]);
    let NP := fresh "NEXT_PREFIX" in
    pose proof (nc_prefix_extend sub m0 d u v cin k q s MDL ltac:(vm_compute; easy) PREFIX X) as NP;
    let V := fresh "READ" in
    pose proof (proj2 (unread_limb m0 (s V_MEM64) u v n k q UN ltac:(first [
      match goal with B : n=k+?c |- _ => clear -B; lia end |
      match goal with B : k+?c<=n |- _ => clear -B; lia end]))) as V;
    change ((s V_MEM64) Ⓠ[v+8*(k+q)]=value m0 (v+8*(k+q)) 1) in V
  end.

Ltac nc_input_eq := first [assumption |
  match goal with H : _ -> ?x = ?y |- ?x = ?y => apply H; vm_compute; easy end |
  match goal with H : remaining_inputs _ _ _ _ _ _ |- _ =>
    first [exact (H 0 ltac:(vm_compute; easy) ltac:(vm_compute; easy)) |
           exact (H 1 ltac:(vm_compute; easy) ltac:(vm_compute; easy)) |
           exact (H 2 ltac:(vm_compute; easy) ltac:(vm_compute; easy)) |
           exact (H 3 ltac:(vm_compute; easy) ltac:(vm_compute; easy))] end].
Ltac nc_inputs :=
  unfold remaining_inputs;
  let i := fresh "i" in let LO := fresh "LO" in let HI := fresh "HI" in
  intros i LO HI;
  let CASES := fresh "CASES" in
  assert (CASES : i=0 \/ i=1 \/ i=2 \/ i=3) by (clear -HI; lia);
  destruct CASES as [CASES|[CASES|[CASES|CASES]]]; subst i;
  psimpl; nc_updates; try (exfalso; clear -LO HI; vm_compute in LO,HI; lia);
  nc_input_eq.

Ltac nc_arith_finish :=
  match goal with
  | P : nc_prefix _ _ _ _ _ _ ?k _ _ |- _ => exists k
  end;
  unfold nc_stage, nc_ptrs, preloaded;
  psimpl;
  repeat match goal with H : ?s ?r = _ |- _ => progress rewrite H end;
  psimpl;
  repeat first [assumption | reflexivity |
    solve [nc_prefix_arithmetic] |
    solve [nc_input_eq] |
    solve [unfold remaining_inputs; intros i LO HI; exfalso; clear -LO HI; lia] |
    solve [nc_inputs] |
    solve [intros; split; nc_input_eq] |
    match goal with |- _ /\ _ => split end |
    solve [intros; discriminate] |
    solve [match goal with H : ?n = ?k + ?q |- ?n = ?q + ?k => clear -H; lia end] |
    solve [match goal with H : ?k + ?q <= ?n |- _ => clear -H; lia end] |
    solve [match goal with H : ?n = ?k + ?q |- _ => clear -H; lia end] ];
  idtac.

(* Every arithmetic cut, including both final and nonfinal full blocks. *)
Lemma nc_vc_arithmetic : forall sub a m0 d u v n cin s t,
  models x64typctx s ->
  (a=0x12851e \/ a=0x12852f \/ a=0x128532 \/
   a=0x128544 \/ a=0x128547 \/ a=0x12854b \/
   a=0x128560 \/ a=0x128563 \/ a=0x128567 \/ a=0x12856b \/
   a=0x1285a2 \/ a=0x1285a5 \/ a=0x1285a9 \/ a=0x1285ad) ->
  true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub a),s)::t)) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub a),s)::t).
Proof.
  intros sub a m0 d u v n cin s t MDL CASE PRE.
  destruct CASE as [A|[A|[A|[A|[A|[A|[A|[A|[A|[A|[A|[A|[A|A]]]]]]]]]]]]];
    subst a; destruct sub;
    cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv] in PRE;
    nc_arith_prepare PRE;
    cbn [nc_program nc_address]; nc_bigstep;
    nc_arith_finish.
Qed.

(* Each tail writes its entire pending result before converting CF to RAX. *)
Definition nc_write_buffer (s : store) p q :=
  match q with
  | 0 => s V_MEM64
  | 1 => (s V_MEM64)[Ⓠp:=s R_R8]
  | 2 => (s V_MEM64)[Ⓠp:=s R_R8][Ⓠp+8:=s R_R9]
  | 3 => (s V_MEM64)[Ⓠp:=s R_R8][Ⓠp+8:=s R_R9][Ⓠp+16:=s R_R10]
  | _ => (s V_MEM64)[Ⓠp:=s R_R8][Ⓠp+8:=s R_R9][Ⓠp+16:=s R_R10][Ⓠp+24:=s R_R11]
  end.

Lemma nc_write_buffer_eq : forall s p q,
  models x64typctx s -> q<=4 ->
  nc_write_buffer s p q = setmem 64 LittleE (8*q) (s V_MEM64) p (buffered s q).
Proof.
  intros s p q MDL Q.
  assert (B8 := models_var R_R8 MDL). change (s R_R8<2^64) in B8.
  assert (B9 := models_var R_R9 MDL). change (s R_R9<2^64) in B9.
  assert (B10 := models_var R_R10 MDL). change (s R_R10<2^64) in B10.
  assert (B11 := models_var R_R11 MDL). change (s R_R11<2^64) in B11.
  assert (CASE : q=0 \/ q=1 \/ q=2 \/ q=3 \/ q=4) by lia.
  destruct CASE as [E|[E|[E|[E|E]]]]; subst q; cbn [nc_write_buffer buffered].
  - reflexivity.
  - reflexivity.
  - rewrite setmem_merge, N.mod_small by exact B8. reflexivity.
  - rewrite setmem_merge, N.mod_small by exact B8.
    change (s R_R8<radix 1) in B8. change (s R_R9<2^64) in B9.
    replace (p+16) with (p+(8+8)) by lia.
    rewrite setmem_merge, N.mod_small; [reflexivity | ].
    change (cbits (s R_R9) 64 (s R_R8)<2^(64+64)).
    apply cbits_bound_add; assumption.
  - rewrite setmem_merge, N.mod_small by exact B8.
    replace (p+16) with (p+(8+8)) by lia.
    rewrite setmem_merge, N.mod_small by (change (cbits (s R_R9) 64 (s R_R8)<2^(64+64)); apply cbits_bound_add; assumption).
    replace (p+24) with (p+(8+8+8)) by lia.
    rewrite setmem_merge, N.mod_small; [reflexivity | ].
    change (cbits (s R_R10) 128 (cbits (s R_R9) 64 (s R_R8))<2^(64+128)).
    apply cbits_bound_add; [exact B10|].
    change (cbits (s R_R9) 64 (s R_R8)<2^(64+64)).
    apply cbits_bound_add; assumption.
Qed.

Lemma nc_commit_last : forall sub m0 d u v n cin k q s,
  models x64typctx s -> 8*n<=2^64 -> n=k+q ->
  nc_prefix sub m0 d u v cin k q s ->
  nc_cf_post sub m0 d u v n cin
    (s[V_MEM64:=nc_write_buffer s (d+8*k) q]).
Proof.
  intros sub m0 d u v n cin k q s MDL B NK PRE.
  pose proof (nc_prefix_commit sub m0 d u v n cin k q s MDL B ltac:(lia) PRE) as P.
  rewrite nc_write_buffer_eq by (try exact MDL; exact (proj1 (proj2 PRE))).
  rewrite <-NK in P.
  unfold nc_prefix in P. cbn [buffered] in P.
  rewrite N.mul_0_r, !N.add_0_r in P.
  exact (conj (proj1 P) (proj2 (proj2 P))).
Qed.

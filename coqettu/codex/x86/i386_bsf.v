(* Semantics of the Codex-local bounded BSF32 adapter. The recognized p-code
   graph and rejection tests are in ../bsf_adapter.py and ../tests/. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_rep.
From Stdlib Require Import NArith Lia FunctionalExtensionality.
Import X86Notations.
Open Scope N.

Definition bit_prefix (n k : N) := forall i, i < k -> N.testbit n i = false.
Definition first_set (width n k : N) :=
  k < width /\ N.testbit n k = true /\ bit_prefix n k.
Definition first_set32 (n k : N) := first_set 32 n k.
Definition first_set64 (n k : N) := first_set 64 n k.

Lemma first_set_nonzero : forall width n k, first_set width n k -> n <> 0.
Proof.
  intros width n k (_ & HIT & _) ZERO. subst n. rewrite N.bits_0 in HIT. discriminate HIT.
Qed.
Definition bit_progress (n i k : N) :=
  k <= i /\ bit_prefix n k /\ (k < i -> N.testbit n k = true).

Lemma bit_progress_initial : forall n, bit_progress n 0 0.
Proof.
  intros n. split; [apply N.le_refl|]. split.
  - intros i I. clear - I. lia.
  - intros I. clear - I. lia.
Qed.

Lemma bit_progress_advance : forall n i k,
  bit_progress n i k ->
  bit_progress n (i+1) (if N.testbit n k then k else k+1).
Proof.
  intros n i k (K & PREFIX & FOUND). destruct (N.testbit n k) eqn:BIT.
  - split; [clear - K; lia|]. split; [exact PREFIX|]. intros _. exact BIT.
  - assert (EQ : k=i).
    { destruct (N.lt_ge_cases k i) as [LT|GE].
      - exfalso. discriminate (FOUND LT).
      - clear - K GE. lia. }
    split; [clear - K; lia|]. split.
    + intros j J. destruct (N.lt_ge_cases j k) as [LT|GE]; [exact (PREFIX j LT)|].
      replace j with k by (clear - J GE; lia). exact BIT.
    + intros LT. clear - EQ LT. lia.
Qed.

Lemma bit_progress_finished : forall n k,
  n < 2^32 -> n <> 0 -> bit_progress n 32 k -> first_set32 n k.
Proof.
  intros n k B NONZERO (K & PREFIX & FOUND).
  assert (LT : k < 32).
  { destruct (N.lt_ge_cases k 32) as [LT|GE]; [exact LT|].
    assert (EQ : k=32) by (clear - K GE; lia). subst k.
    exfalso. apply NONZERO. apply N.bits_inj_0. intro j.
    destruct (N.lt_ge_cases j 32) as [LO|HI]; [exact (PREFIX j LO)|].
    apply bits_above_pow2. eapply N.lt_le_trans; [exact B|].
    apply N.pow_le_mono_r; [discriminate|exact HI]. }
  repeat split; first [exact LT|exact (FOUND LT)|exact PREFIX].
Qed.

Lemma shifted_bit_word : forall n k,
  N.land (N.shiftr n k) 1 = N.b2n (N.testbit n k).
Proof.
  intros. change 1 with (N.ones 1). rewrite N.land_ones.
  change (2^1) with 2. rewrite <- N.bit0_mod, N.shiftr_spec', N.add_0_l.
  reflexivity.
Qed.

Definition BSF_COUNTER := V_TEMP 0x2c680.
Definition BSF_ZERO := V_TEMP 0x2c780.
Definition BSF_SHIFT := V_TEMP 0x2c800.
Definition BSF_LOW := V_TEMP 0x2c880.
Definition BSF_FOUND := V_TEMP 0x2c900.

Definition bsf_round (source : x86var) : stmt :=
  Move BSF_SHIFT (BinOp OP_RSHIFT (Var source) (Var BSF_COUNTER)) $;
  Move BSF_LOW (BinOp OP_AND (Var BSF_SHIFT) (Word 1 32)) $;
  Move BSF_FOUND (BinOp OP_NEQ (Var BSF_LOW) (Word 0 32)) $;
  If (Cast CAST_LOW 1 (Var BSF_FOUND)) Nop
    (Move BSF_COUNTER (BinOp OP_PLUS (Var BSF_COUNTER) (Word 1 32))).

Definition bsf_guard (source : x86var) : stmt :=
  If (Cast CAST_LOW 1 (Var BSF_ZERO)) Nop (Rep (Word 32 32) (bsf_round source)).

Definition bsf32_stmt (source destination : x86var) : stmt :=
  Move BSF_COUNTER (Word 0 32) $;
  Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var source) (Word 0 32))) $;
  Move BSF_ZERO (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 1 8))) $;
  bsf_guard source $;
  Move destination (Var BSF_COUNTER).

Definition bsf_round_context (c : typctx) :=
  c[BSF_SHIFT := Some 32][BSF_LOW := Some 32][BSF_FOUND := Some 1].
Definition bsf_round_store (source : x86var) (s : store) :=
  s[BSF_SHIFT := N.shiftr (s source) (s BSF_COUNTER)]
   [BSF_LOW := N.b2n (N.testbit (s source) (s BSF_COUNTER))]
   [BSF_FOUND := N.b2n (N.testbit (s source) (s BSF_COUNTER))].

Lemma bsf_round_execution : forall source c s,
  c source = Some 32 -> c BSF_COUNTER = Some 32 ->
  exec_stmt c s (bsf_round source)
    (if N.testbit (s source) (s BSF_COUNTER) then bsf_round_context c
     else (bsf_round_context c)[BSF_COUNTER := Some 32])
    (if N.testbit (s source) (s BSF_COUNTER) then bsf_round_store source s
     else (bsf_round_store source s)[BSF_COUNTER := (s BSF_COUNTER+1) mod 2^32]) None.
Proof.
  intros source c s SOURCE COUNTER.
  unfold bsf_round, bsf_round_context, bsf_round_store.
  eapply XSeq2 with
    (c2 := c[BSF_SHIFT := Some 32])
    (s2 := s[BSF_SHIFT := N.shiftr (s source) (s BSF_COUNTER)]).
  - apply XMove.
    change (eval_exp c s (BinOp OP_RSHIFT (Var source) (Var BSF_COUNTER))
      (eval_binop OP_RSHIFT 32 (s source) (s BSF_COUNTER)) 32).
    eapply EBinOp with (w:=32) (n1:=s source) (n2:=s BSF_COUNTER);
      apply EVar; assumption.
  - eapply XSeq2 with
      (c2 := c[BSF_SHIFT := Some 32][BSF_LOW := Some 32])
      (s2 := s[BSF_SHIFT := N.shiftr (s source) (s BSF_COUNTER)]
        [BSF_LOW := N.b2n (N.testbit (s source) (s BSF_COUNTER))]).
    + apply XMove.
      assert (E : eval_exp (c[BSF_SHIFT := Some 32])
        (s[BSF_SHIFT := N.shiftr (s source) (s BSF_COUNTER)])
        (BinOp OP_AND (Var BSF_SHIFT) (Word 1 32))
        (N.land (N.shiftr (s source) (s BSF_COUNTER)) 1) 32).
      { eapply EBinOp with (w:=32)
          (n1:=N.shiftr (s source) (s BSF_COUNTER)) (n2:=1);
          [apply EVar; reflexivity|constructor]. }
      rewrite shifted_bit_word in E. exact E.
    + eapply XSeq2 with
        (c2 := c[BSF_SHIFT := Some 32][BSF_LOW := Some 32][BSF_FOUND := Some 1])
        (s2 := s[BSF_SHIFT := N.shiftr (s source) (s BSF_COUNTER)]
          [BSF_LOW := N.b2n (N.testbit (s source) (s BSF_COUNTER))]
          [BSF_FOUND := N.b2n (N.testbit (s source) (s BSF_COUNTER))]).
      * apply XMove.
        assert (E : eval_exp
          (c[BSF_SHIFT := Some 32][BSF_LOW := Some 32])
          (s[BSF_SHIFT := N.shiftr (s source) (s BSF_COUNTER)]
             [BSF_LOW := N.b2n (N.testbit (s source) (s BSF_COUNTER))])
          (BinOp OP_NEQ (Var BSF_LOW) (Word 0 32))
          (eval_binop OP_NEQ 32 (N.b2n (N.testbit (s source) (s BSF_COUNTER))) 0) 1).
        { eapply EBinOp with (w:=32)
            (n1:=N.b2n (N.testbit (s source) (s BSF_COUNTER))) (n2:=0);
            [apply EVar; reflexivity|constructor]. }
        replace (eval_binop OP_NEQ 32 (N.b2n (N.testbit (s source) (s BSF_COUNTER))) 0)
          with (N.b2n (N.testbit (s source) (s BSF_COUNTER))) in E
          by (destruct N.testbit; reflexivity).
        exact E.
      * eapply XIf with (b := N.b2n (N.testbit (s source) (s BSF_COUNTER))).
        -- assert (E : eval_exp
             (c[BSF_SHIFT := Some 32][BSF_LOW := Some 32][BSF_FOUND := Some 1])
             (s[BSF_SHIFT := N.shiftr (s source) (s BSF_COUNTER)]
                [BSF_LOW := N.b2n (N.testbit (s source) (s BSF_COUNTER))]
                [BSF_FOUND := N.b2n (N.testbit (s source) (s BSF_COUNTER))])
             (Cast CAST_LOW 1 (Var BSF_FOUND))
             ((N.b2n (N.testbit (s source) (s BSF_COUNTER))) mod 2) 1).
           { eapply ECast with (w:=1)
               (n:=N.b2n (N.testbit (s source) (s BSF_COUNTER))).
             apply EVar. reflexivity. }
           replace ((N.b2n (N.testbit (s source) (s BSF_COUNTER))) mod 2)
             with (N.b2n (N.testbit (s source) (s BSF_COUNTER))) in E
             by (destruct N.testbit; reflexivity).
           exact E.
        -- destruct (N.testbit (s source) (s BSF_COUNTER)); [constructor|].
           apply XMove.
           eapply EBinOp with (w:=32) (n1:=s BSF_COUNTER) (n2:=1);
             [eapply eval_var_value; simpl_stores; first [exact COUNTER|reflexivity]
             |constructor].
Qed.

Lemma bsf_round_noassign : forall source v,
  x86typctx v <> None -> noassign v (bsf_round source).
Proof.
  intros source v TYPE. unfold bsf_round, noassign.
  repeat constructor; intros EQ; subst v; apply TYPE; reflexivity.
Qed.

Lemma bsf_round_effect : forall source c s c' s' x,
  x86typctx source = Some 32 ->
  c source = Some 32 -> c BSF_COUNTER = Some 32 -> s BSF_COUNTER <= 32 ->
  exec_stmt c s (bsf_round source) c' s' x ->
  x = None /\ c' source = Some 32 /\ c' BSF_COUNTER = Some 32 /\
  s' source = s source /\
  s' BSF_COUNTER = if N.testbit (s source) (s BSF_COUNTER)
    then s BSF_COUNTER else s BSF_COUNTER+1.
Proof.
  intros source c s c' s' x TYPE CS CC K XS.
  assert (TYPED : x86typctx source <> None) by (rewrite TYPE; discriminate).
  pose proof (noassign_stmt_same source (bsf_round source)
    (bsf_round_noassign source source TYPED) c s s' c' x XS) as FRAME.
  pose proof (f_equal fst FRAME) as VALUE.
  pose proof (f_equal snd FRAME) as CTX.
  cbn [fst] in VALUE. cbn [snd] in CTX.
  assert (CSOUT : c' source = Some 32) by (rewrite <- CTX; exact CS).
  assert (SOURCEOUT : s' source = s source) by (symmetry; exact VALUE).
  assert (NU : forall_exps_in_stmt not_unknown (bsf_round source))
    by (unfold bsf_round; repeat split).
  pose proof (exec_stmt_deterministic NU XS (bsf_round_execution source c s CS CC)) as EQ.
  inversion EQ; subst x c' s'.
  repeat split; try reflexivity; try exact CSOUT; try exact SOURCEOUT.
  all: unfold bsf_round_context, bsf_round_store.
  all: destruct (N.testbit (s source) (s BSF_COUNTER)); psimpl;
    try exact CC; try reflexivity.
  all: apply N.mod_small; change (1+s BSF_COUNTER < 2^32).
  all: set (k := s BSF_COUNTER) in *; clearbody k; clear - K; lia.
Qed.

Lemma bsf_repeat_effect : forall source c s c' s' x,
  x86typctx source = Some 32 ->
  c source = Some 32 -> c BSF_COUNTER = Some 32 -> s BSF_COUNTER = 0 ->
  s source < 2^32 -> s source <> 0 ->
  exec_stmt c s (Rep (Word 32 32) (bsf_round source)) c' s' x ->
  x = None /\ c' BSF_COUNTER = Some 32 /\
  exists k, first_set32 (s source) k /\ s' BSF_COUNTER = k.
Proof.
  intros source c s c' s' x TYPE CS CC ZERO B NONZERO XS.
  set (P := fun i (ctx : typctx) (state : store) =>
    ctx source = Some 32 /\ ctx BSF_COUNTER = Some 32 /\ state source = s source /\
    exists k, state BSF_COUNTER = k /\ bit_progress (s source) i k).
  assert (INIT : P 0 c s).
  { unfold P. repeat split; try assumption; try reflexivity.
    exists 0. split; [exact ZERO|apply bit_progress_initial]. }
  assert (STEP : forall i c0 s0 c1 s1 x1, i < 32 -> P i c0 s0 ->
    exec_stmt c0 s0 (bsf_round source) c1 s1 x1 -> x1 = None /\ P (i+1) c1 s1).
  { intros i c0 s0 c1 s1 x1 I (CS0 & CC0 & SRC0 & k & CT & PROGRESS) ROUND.
    assert (K : s0 BSF_COUNTER <= 32).
    { rewrite CT. destruct PROGRESS as [K _]. clear - K I. lia. }
    destruct (bsf_round_effect source c0 s0 c1 s1 x1 TYPE CS0 CC0 K ROUND)
      as (NO & CS1 & CC1 & SRC1 & CT1).
    split; [exact NO|]. unfold P. repeat split; try assumption.
    - rewrite SRC1. exact SRC0.
    - exists (if N.testbit (s source) k then k else k+1). split.
      + rewrite CT1, SRC0, CT. reflexivity.
      + exact (bit_progress_advance _ _ _ PROGRESS). }
  inversion XS; subst.
  match goal with E : eval_exp c s (Word 32 32) _ _ |- _ => inversion E; subst end.
  match goal with ITER : exec_stmt c s (N.iter 32 (Seq (bsf_round source)) Nop) c' s' x |- _ =>
    destruct (iter_exec_indexed 32 (bsf_round source) P STEP 32 0 c s c' s' x
      ltac:(reflexivity) INIT ITER) as [NO POST]
  end.
  destruct POST as (CSOUT & CCOUT & SRCOUT & k & CT & PROGRESS).
  split; [exact NO|]. split; [exact CCOUT|]. exists k. split; [|exact CT].
  exact (bit_progress_finished _ _ B NONZERO PROGRESS).
Qed.

Lemma typed32_not_temp : forall v n,
  x86typctx v = Some 32 -> v <> V_TEMP n.
Proof. intros v n TYPE EQ. subst v. discriminate TYPE. Qed.
Lemma typed32_not_zf : forall v,
  x86typctx v = Some 32 -> v <> R_ZF.
Proof. intros v TYPE EQ. subst v. discriminate TYPE. Qed.
Lemma b2n_mod2 : forall b, N.b2n b mod 2 = N.b2n b.
Proof. intros []; reflexivity. Qed.
Lemma b2n_eq_one : forall b, N.b2n (N.b2n b =? 1) = N.b2n b.
Proof. intros []; reflexivity. Qed.

Definition bsf_prefix_context (c : typctx) :=
  c[BSF_COUNTER := Some 32][R_ZF := Some 1][BSF_ZERO := Some 1].
Definition bsf_prefix_store (source : x86var) (s : store) :=
  s[BSF_COUNTER := 0][R_ZF := N.b2n (s source =? 0)]
   [BSF_ZERO := N.b2n (s source =? 0)].

Lemma bsf_prepare : forall source destination c s c' s' x,
  x86typctx source = Some 32 -> c source = Some 32 ->
  exec_stmt c s (bsf32_stmt source destination) c' s' x ->
  exec_stmt (bsf_prefix_context c) (bsf_prefix_store source s)
    (bsf_guard source $; Move destination (Var BSF_COUNTER)) c' s' x.
Proof.
  intros source destination c s c' s' x TYPE CS XS.
  assert (NE : source <> BSF_COUNTER) by (apply (typed32_not_temp _ _ TYPE)).
  set (c1 := c[BSF_COUNTER := Some 32]). set (s1 := s[BSF_COUNTER := 0]).
  set (flag := N.b2n (s source =? 0)).
  set (c2 := c1[R_ZF := Some 1]). set (s2 := s1[R_ZF := flag]).
  set (c3 := c2[BSF_ZERO := Some 1]). set (s3 := s2[BSF_ZERO := flag]).
  assert (F0 : exec_stmt c s (Move BSF_COUNTER (Word 0 32)) c1 s1 None).
  { apply XMove. constructor. }
  unfold bsf32_stmt in XS.
  pose proof (exec_seq_prefix _ _ _ _ _ _ _ _ _ F0 XS ltac:(repeat split)) as X1.
  assert (E1 : eval_exp c1 s1 (BinOp OP_EQ (Var source) (Word 0 32)) flag 1).
  { unfold flag. eapply EBinOp with (w:=32) (n1:=s source) (n2:=0).
    - eapply eval_var_value.
      + unfold c1. rewrite update_frame by exact NE. exact CS.
      + unfold s1. rewrite update_frame by exact NE. reflexivity.
    - constructor. }
  assert (E2 : eval_exp c1 s1
    (Cast CAST_LOW 1 (BinOp OP_EQ (Var source) (Word 0 32))) (flag mod 2) 1).
  { eapply ECast with (w:=1) (n:=flag). exact E1. }
  unfold flag in E2. rewrite b2n_mod2 in E2. fold flag in E2.
  assert (F1 : exec_stmt c1 s1
    (Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var source) (Word 0 32)))) c2 s2 None).
  { apply XMove. exact E2. }
  pose proof (exec_seq_prefix _ _ _ _ _ _ _ _ _ F1 X1 ltac:(repeat split)) as X2.
  assert (E3 : eval_exp c2 s2
    (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 1 8)))
    (N.b2n (flag =? 1)) 1).
  { eapply EBinOp with (w:=1) (n1:=flag) (n2:=1).
    - eapply eval_var_value; unfold c2, s2; rewrite update_updated; reflexivity.
    - eapply ECast with (w:=8) (n:=1). constructor. }
  unfold flag in E3. rewrite b2n_eq_one in E3. fold flag in E3.
  assert (F2 : exec_stmt c2 s2
    (Move BSF_ZERO (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 1 8)))) c3 s3 None).
  { apply XMove. exact E3. }
  exact (exec_seq_prefix _ _ _ _ _ _ _ _ _ F2 X2 ltac:(repeat split)).
Qed.

Lemma bsf_prefix_source : forall source c s,
  x86typctx source = Some 32 -> c source = Some 32 ->
  bsf_prefix_context c source = Some 32 /\ bsf_prefix_store source s source = s source.
Proof.
  intros source c s TYPE CS. split.
  - unfold bsf_prefix_context. rewrite !update_frame by
      first [eapply typed32_not_temp; exact TYPE | apply typed32_not_zf; exact TYPE].
    exact CS.
  - unfold bsf_prefix_store. rewrite !update_frame by
      first [eapply typed32_not_temp; exact TYPE | apply typed32_not_zf; exact TYPE].
    reflexivity.
Qed.

Lemma bsf_prefix_guard : forall source c s,
  eval_exp (bsf_prefix_context c) (bsf_prefix_store source s)
    (Cast CAST_LOW 1 (Var BSF_ZERO)) (N.b2n (s source =? 0)) 1.
Proof.
  intros source c s.
  assert (E : eval_exp (bsf_prefix_context c) (bsf_prefix_store source s)
    (Cast CAST_LOW 1 (Var BSF_ZERO)) ((N.b2n (s source =? 0)) mod 2) 1).
  { eapply ECast with (w:=1) (n:=N.b2n (s source =? 0)).
    eapply eval_var_value; unfold bsf_prefix_context, bsf_prefix_store;
      rewrite update_updated; reflexivity. }
  rewrite b2n_mod2 in E. exact E.
Qed.

Lemma bsf_guard_fallthrough : forall source c s c' s' x,
  exec_stmt c s (bsf_guard source) c' s' x -> x=None.
Proof.
  intros source c s c' s' x XS. eapply stmt_xnone; [exact XS| |];
    unfold bsf_guard, bsf_round, forall_stmts_in_stmt;
    cbn; repeat split; intros e EQ; discriminate EQ.
Qed.

Lemma bsf32_effect : forall source destination c s c' s' x,
  x86typctx source = Some 32 -> x86typctx destination = Some 32 ->
  c source = Some 32 -> s source < 2^32 ->
  exec_stmt c s (bsf32_stmt source destination) c' s' x ->
  x=None /\ exists k,
    ((s source=0 /\ k=0) \/ first_set32 (s source) k) /\
    s' destination=k /\ s' R_ZF=N.b2n (s source =? 0).
Proof.
  intros source destination c s c' s' x SOURCE DEST CS B XS.
  pose proof (bsf_prepare _ _ _ _ _ _ _ SOURCE CS XS) as PREP.
  pose proof (bsf_prefix_guard source c s) as GUARD.
  destruct (bsf_prefix_source source c s SOURCE CS) as [CS0 SRC0].
  assert (CC0 : bsf_prefix_context c BSF_COUNTER = Some 32).
  { unfold bsf_prefix_context. simpl_stores. reflexivity. }
  assert (CT0 : bsf_prefix_store source s BSF_COUNTER = 0).
  { unfold bsf_prefix_store. simpl_stores. reflexivity. }
  assert (ZF0 : bsf_prefix_store source s R_ZF = N.b2n (s source =? 0)).
  { unfold bsf_prefix_store. simpl_stores. reflexivity. }
  assert (NE : R_ZF <> destination).
  { intro EQ. apply (typed32_not_zf destination DEST). symmetry. exact EQ. }
  inversion PREP; subst.
  - match goal with H : exec_stmt _ _ (bsf_guard source) _ _ (Some _) |- _ =>
      pose proof (bsf_guard_fallthrough _ _ _ _ _ _ H) as NO; discriminate NO end.
  - match goal with H : exec_stmt (bsf_prefix_context c) (bsf_prefix_store source s)
                        (bsf_guard source) ?cm ?sm None,
                    LAST : exec_stmt ?cm ?sm (Move destination (Var BSF_COUNTER)) c' s' x |- _ =>
      pose proof (exec_if_guard _ _ _ _ _ _ _ _ _ GUARD H ltac:(repeat split)) as BODY
    end.
    destruct (s source =? 0) eqn:ZERO.
    + apply N.eqb_eq in ZERO. cbn [N.b2n] in BODY.
      inversion BODY; subst.
      match goal with LAST : exec_stmt _ _ (Move destination (Var BSF_COUNTER)) c' s' x |- _ =>
        destruct (exec_move_var _ _ _ _ 0 32 _ _ _ CC0 CT0 LAST) as [NO OUT]
      end.
      split; [exact NO|]. exists 0. split; [left; split; [exact ZERO|reflexivity]|].
      rewrite OUT. split; [apply update_updated|]. rewrite update_frame by exact NE. exact ZF0.
    + apply N.eqb_neq in ZERO.
      cbn [N.b2n] in BODY.
      assert (B0 : bsf_prefix_store source s source < 2^32) by (rewrite SRC0; exact B).
      assert (NZ0 : bsf_prefix_store source s source <> 0) by (rewrite SRC0; exact ZERO).
      match type of BODY with exec_stmt _ _ _ ?cm ?sm _ =>
        destruct (bsf_repeat_effect source _ _ cm sm None SOURCE CS0 CC0 CT0 B0 NZ0 BODY)
          as [_ [CC1 [k [FIRST VALUE]]]];
        rewrite SRC0 in FIRST;
        assert (NA : noassign R_ZF (Rep (Word 32 32) (bsf_round source)))
          by (constructor; apply bsf_round_noassign; discriminate);
        pose proof (noassign_stmt_same R_ZF _ NA _ _ sm cm None BODY) as FRAME
      end.
      pose proof (f_equal fst FRAME) as FLAG. cbn [fst] in FLAG. rewrite ZF0 in FLAG.
      match goal with LAST : exec_stmt _ _ (Move destination (Var BSF_COUNTER)) c' s' x |- _ =>
        destruct (exec_move_var _ _ _ _ k 32 _ _ _ CC1 VALUE LAST) as [NO OUT]
      end.
      split; [exact NO|]. exists k. split; [right; exact FIRST|].
      rewrite OUT. split; [apply update_updated|].
      rewrite update_frame by exact NE. symmetry. exact FLAG.
Qed.

Lemma bsf32_noassign : forall source destination v,
  x86typctx v <> None -> v <> destination -> v <> R_ZF ->
  noassign v (bsf32_stmt source destination).
Proof.
  intros source destination v TYPE ND NZ.
  unfold bsf32_stmt, bsf_guard, bsf_round, noassign.
  repeat constructor; intros EQ; subst v;
    first [apply ND; reflexivity | apply NZ; reflexivity | apply TYPE; reflexivity].
Qed.

Lemma bsf32_machine_effect : forall source destination s c' s' x,
  x86typctx source = Some 32 -> x86typctx destination = Some 32 ->
  s source < 2^32 ->
  exec_stmt x86typctx s (bsf32_stmt source destination) c' s' x ->
  x=None /\ exists k,
    ((s source=0 /\ k=0) \/ first_set32 (s source) k) /\
    reset_temps s s' = s[R_ZF := N.b2n (s source =? 0)][destination := k].
Proof.
  intros source destination s c' s' x SOURCE DEST B XS.
  destruct (bsf32_effect source destination x86typctx s c' s' x SOURCE DEST SOURCE B XS)
    as [NO [k [SPEC [VALUE FLAG]]]].
  split; [exact NO|]. exists k. split; [exact SPEC|].
  apply functional_extensionality. intro v.
  unfold reset_temps, reset_vars.
  change ((match x86typctx v with None => s | Some _ => s' end) v =
    (s[R_ZF := N.b2n (s source =? 0)][destination := k]) v).
  destruct (x86typctx v) eqn:TYPE.
  - destruct (v == destination) as [EQ|ND].
    + subst v. rewrite update_updated. exact VALUE.
    + destruct (v == R_ZF) as [EQ|NZ].
      * subst v. rewrite update_frame by exact ND. rewrite update_updated. exact FLAG.
      * rewrite !update_frame by assumption.
        assert (TYPED : x86typctx v <> None) by (rewrite TYPE; discriminate).
        pose proof (noassign_stmt_same v _
          (bsf32_noassign source destination v TYPED ND NZ) _ _ _ _ _ XS) as FRAME.
        symmetry. exact (f_equal fst FRAME).
  - assert (ND : v <> destination).
    { intros EQ. subst v. rewrite DEST in TYPE. discriminate TYPE. }
    assert (NZ : v <> R_ZF) by (intros EQ; subst v; discriminate TYPE).
    rewrite !update_frame by assumption. reflexivity.
Qed.

Definition ffs_result32 (n result : N) : Prop :=
  (n=0 /\ result=0) \/ exists k, first_set32 n k /\ result=k+1.

Lemma ffs_result32_range : forall n result,
  ffs_result32 n result -> result <= 32.
Proof.
  intros n result [[_ ZERO]|(k & FIRST & VALUE)]; subst result; [lia|].
  destruct FIRST as [K _]. clear - K. lia.
Qed.

Lemma bsf_increment_small : forall k, k < 32 -> (1+k) mod 2^32 = k+1.
Proof. intros k K. rewrite N.mod_small by lia. lia. Qed.

Lemma first_set64_low : forall lo hi k,
  first_set32 lo k -> first_set64 (N.lor (N.shiftl hi 32) lo) k.
Proof.
  intros lo hi k (K & HIT & PREFIX). split; [clear - K; lia|]. split.
  - rewrite N.lor_spec, N.shiftl_spec_low by exact K. exact HIT.
  - intros i I. rewrite N.lor_spec, N.shiftl_spec_low by (clear - I K; lia).
    exact (PREFIX i I).
Qed.

Lemma first_set64_high : forall hi k,
  first_set32 hi k -> first_set64 (N.shiftl hi 32) (32+k).
Proof.
  intros hi k (K & HIT & PREFIX). split; [clear - K; lia|]. split.
  - rewrite N.shiftl_spec_high' by lia.
    replace (32+k-32) with k by lia. exact HIT.
  - intros i I. destruct (N.lt_ge_cases i 32) as [LO|HI].
    + apply N.shiftl_spec_low. exact LO.
    + rewrite N.shiftl_spec_high' by exact HI. apply PREFIX. clear - I HI. lia.
Qed.

Definition ffs_result64 (n result : N) : Prop :=
  (n=0 /\ result=0) \/ exists k, first_set64 n k /\ result=k+1.

Lemma ffs_result64_range : forall n result,
  ffs_result64 n result -> result <= 64.
Proof.
  intros n result [[_ ZERO]|(k & FIRST & VALUE)]; subst result; [lia|].
  destruct FIRST as [K _]. clear - K. lia.
Qed.

Lemma bsf_increment64_small : forall k, k < 64 -> (1+k) mod 2^32 = k+1.
Proof. intros k K. rewrite N.mod_small by lia. lia. Qed.


(* Instruction-level lemmas for the AVX2 instructions of the lifted glibc
   string functions (VPCMPEQB, VPMINUB, VPMOVMSKB).

   Stepping one of these instructions symbolically produces a term with 32
   byte lanes (and VPMOVMSKB executes about 200 moves), which is slow to
   build and slow to check at Qed.  Instead, each lemma below describes the
   whole lifted statement once: the statement is produced by a Coq generator
   that is convertible to what the lifter emits (the lifter numbers
   temporaries per instruction, so every occurrence of an instruction lifts to
   the same statement), and the lemma is proved by induction over the lanes.

   A proof uses one of these lemmas by stepping the instruction by hand:
     eapply NIStep; [reflexivity|reflexivity|]. intros c1 s1 x1 XS.
     destruct (vpmovmskb_exec ... XS) as [-> [r [R ->]]].
   which leaves the next state as s[dst := r] with r abstract. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia FunctionalExtensionality.
Require Import amd64_common amd64_simd.
Open Scope N.

(** * Generic helpers *)

Lemma seq_move_inv: forall c s v e q c' s' x,
  exec_stmt c s (Move v e $; q) c' s' x ->
  exists n w, eval_exp c s e n w /\ exec_stmt (update c v (Some w)) (update s v n) q c' s' x.
Proof.
  intros c s v e q c' s' x X. inversion X; subst.
  - match goal with H: exec_stmt _ _ (Move _ _) _ _ (Some _) |- _ => inversion H end.
  - match goal with H: exec_stmt _ _ (Move _ _) _ _ None |- _ => inversion H; subst end.
    eexists. eexists. split. eassumption. eassumption.
Qed.

Lemma move_inv: forall c s v e c' s' x,
  exec_stmt c s (Move v e) c' s' x ->
  exists n w, eval_exp c s e n w /\ c' = update c v (Some w) /\ s' = update s v n /\ x = None.
Proof. intros c s v e c' s' x X. inversion X; subst. eexists. eexists. repeat split. eassumption. Qed.

(* Temporaries are untyped in archtyps, so reset_temps forgets them. *)
Lemma reset_one: forall s s1 d y,
  archtyps d <> None -> s1 d = y ->
  (forall v, v <> d -> archtyps v <> None -> s1 v = s v) ->
  reset_temps s s1 = update s d y.
Proof.
  intros s s1 d y D Y F. extensionality v. unfold reset_temps, reset_vars, update.
  destruct (v == d) as [->|NE].
  - destruct (archtyps d) eqn:A. exact Y. exfalso. apply D. reflexivity.
  - destruct (archtyps v) eqn:A. apply F. exact NE. rewrite A. discriminate. reflexivity.
Qed.

Definition not_temp (v:var) := forall k, v <> V_TEMP k.

Lemma archtyps_not_temp: forall v, archtyps v <> None -> not_temp v.
Proof. intros v A k E. subst v. apply A. reflexivity. Qed.

(* Inversion lemmas for expression evaluation (plain inversion would also
   normalize arithmetic such as 8*i in the indices). *)
Lemma ev_var: forall c s v n w, eval_exp c s (Var v) n w -> n = s v /\ c v = Some w.
Proof. intros. inversion H; subst. split. reflexivity. assumption. Qed.
Lemma ev_word: forall c s k w0 n w, eval_exp c s (Word k w0) n w -> n = k /\ w = w0.
Proof. intros. inversion H; subst. split; reflexivity. Qed.
Lemma ev_binop: forall c s op e1 e2 n w, eval_exp c s (BinOp op e1 e2) n w ->
  exists n1 n2 w', eval_exp c s e1 n1 w' /\ eval_exp c s e2 n2 w' /\
                   n = eval_binop op w' n1 n2 /\ w = widthof_binop op w'.
Proof. intros. inversion H; subst. do 3 eexists. repeat split; eassumption. Qed.
Lemma ev_cast: forall c s ct w' e n w, eval_exp c s (Cast ct w' e) n w ->
  exists n1 w1, eval_exp c s e n1 w1 /\ n = cast ct w1 w' n1 /\ w = w'.
Proof. intros. inversion H; subst. do 2 eexists. repeat split; eassumption. Qed.
Lemma ev_extract: forall c s hi lo e n w, eval_exp c s (Extract hi lo e) n w ->
  exists n1 w1, eval_exp c s e n1 w1 /\ n = xbits n1 lo (N.succ hi) /\ w = N.succ hi - lo.
Proof. intros. inversion H; subst. do 2 eexists. repeat split; eassumption. Qed.
Lemma ev_concat: forall c s e1 e2 n w, eval_exp c s (Concat e1 e2) n w ->
  exists n1 w1 n2 w2, eval_exp c s e1 n1 w1 /\ eval_exp c s e2 n2 w2 /\
                      n = cbits n1 w2 n2 /\ w = w1 + w2.
Proof. intros. inversion H; subst. do 4 eexists. repeat split; eassumption. Qed.
Lemma ev_ite: forall c s e1 e2 e3 n w, eval_exp c s (Ite e1 e2 e3) n w ->
  exists n1 w1 n2 n3, eval_exp c s e1 n1 w1 /\ eval_exp c s e2 n2 w /\ eval_exp c s e3 n3 w /\
                      n = match n1 with N0 => n3 | _ => n2 end.
Proof. intros. inversion H; subst. do 4 eexists. repeat split; eassumption. Qed.

Ltac subst_eq T :=
  match type of T with
  | ?a = ?b => first [ is_var a; subst a | is_var b; subst b | clear T ]
  end.

(* Fully invert an expression evaluation. *)
Ltac inv_exp E :=
  let n := fresh "n" in let w := fresh "w" in let n' := fresh "n" in let w' := fresh "w" in
  let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
  let T := fresh "T" in let N1 := fresh "N" in let W1 := fresh "W" in
  lazymatch type of E with
  | eval_exp _ _ (Var _) _ _ => apply ev_var in E; destruct E as [N1 T]; subst_eq N1
  | eval_exp _ _ (Word _ _) _ _ => apply ev_word in E; destruct E as [N1 W1]; subst_eq N1; subst_eq W1
  | eval_exp _ _ (BinOp _ _ _) _ _ =>
      apply ev_binop in E; destruct E as [n [n' [w [E1 [E2 [N1 W1]]]]]]; subst_eq N1; subst_eq W1; inv_exp E1; inv_exp E2
  | eval_exp _ _ (Cast _ _ _) _ _ =>
      apply ev_cast in E; destruct E as [n [w [E1 [N1 W1]]]]; subst_eq N1; subst_eq W1; inv_exp E1
  | eval_exp _ _ (Extract _ _ _) _ _ =>
      apply ev_extract in E; destruct E as [n [w [E1 [N1 W1]]]]; subst_eq N1; subst_eq W1; inv_exp E1
  | eval_exp _ _ (Concat _ _) _ _ =>
      apply ev_concat in E; destruct E as [n [w [n' [w' [E1 [E2 [N1 W1]]]]]]]; subst_eq N1; subst_eq W1; inv_exp E1; inv_exp E2
  | eval_exp _ _ (Ite _ _ _) _ _ =>
      let n'' := fresh "n" in
      apply ev_ite in E; destruct E as [n [w [n' [n'' [E1 [E2 [E3 N1]]]]]]]; subst_eq N1;
      inv_exp E1; inv_exp E2; inv_exp E3
  | _ => idtac
  end.

(* Unfold operator semantics without touching the arithmetic. *)
Ltac ev := unfold eval_binop, cast, widthof_binop; cbv beta iota.
Ltac ev_in H := unfold eval_binop, cast, widthof_binop in H; cbv beta iota in H.

(* Simplify reads of updated stores. *)
Ltac vneq NT :=
  let H := fresh in intro H;
  first [ discriminate H
        | injection H; clear H; intro H; lia
        | exact (NT _ H)
        | exact (NT _ (eq_sym H))
        | match goal with N: not_temp _ |- _ => first [exact (N _ H) | exact (N _ (eq_sym H))] end
        | match goal with N: ?a <> ?b |- _ => first [exact (N H) | exact (N (eq_sym H))] end ].
Ltac upd NT :=
  repeat match goal with
  | |- context [update ?s ?x ?v ?x] => rewrite (update_updated s x v)
  | |- context [update ?s ?x ?v ?z] => rewrite (update_frame s x v z) by vneq NT
  end.
Ltac upd_in NT H :=
  repeat match type of H with
  | context [update ?s ?x ?v ?x] => rewrite (update_updated s x v) in H
  | context [update ?s ?x ?v ?z] => rewrite (update_frame s x v z) in H by vneq NT
  end.

(* Simplify typing-context lookups and identify the widths they give. *)
Ltac typs NT :=
  repeat match goal with T: update _ _ _ _ = Some _ |- _ => progress upd_in NT T end;
  repeat match goal with
  | T: Some _ = Some _ |- _ => injection T; clear T; intro T; subst_eq T
  | T1: ?c ?v = Some ?a, T2: ?c ?v = Some ?b |- _ =>
      rewrite T1 in T2; injection T2; clear T2; intro T2; subst_eq T2
  end.

(** * Byte lanes *)

Lemma byte_testbit: forall v i j, N.testbit (byte v i) j = (j <? 8) && N.testbit v (j + 8*i).
Proof.
  intros v i j. unfold byte. rewrite xbits_spec, Bool.andb_comm. f_equal.
  destruct (N.ltb_spec j 8); destruct (N.ltb_spec (j + 8*i) (8*i+8)); try reflexivity; lia.
Qed.

Lemma byte_small: forall a, a < 256 -> byte a 0 = a.
Proof.
  intros a A. unfold byte, xbits. rewrite N.shiftr_0_r. apply N.mod_small. exact A.
Qed.

Lemma cbits_testbit: forall a W b j, b < 2^W ->
  N.testbit (cbits a W b) j = if j <? W then N.testbit b j else N.testbit a (j - W).
Proof.
  intros a W b j B. unfold cbits. rewrite N.lor_spec.
  destruct (N.ltb_spec j W).
  - rewrite N.shiftl_spec_low by exact H. reflexivity.
  - rewrite N.shiftl_spec_high by lia. rewrite (bound_hibits_zero W b j B H). apply Bool.orb_false_r.
Qed.

Lemma byte_cbits_lo: forall a W b i, b < 2^(8*W) -> i < W -> byte (cbits a (8*W) b) i = byte b i.
Proof.
  intros a W b i B I. apply N.bits_inj. intro j. rewrite !byte_testbit.
  destruct (N.ltb_spec j 8); [|reflexivity]. rewrite cbits_testbit by exact B.
  replace (j + 8*i <? 8*W) with true by (symmetry; apply N.ltb_lt; lia). reflexivity.
Qed.

Lemma byte_cbits_hi: forall a W b, b < 2^(8*W) -> a < 256 -> byte (cbits a (8*W) b) W = a.
Proof.
  intros a W b B A. apply N.bits_inj. intro j. rewrite byte_testbit.
  destruct (N.ltb_spec j 8).
  - rewrite cbits_testbit by exact B.
    replace (j + 8*W <? 8*W) with false by (symmetry; apply N.ltb_ge; lia).
    cbn [andb]. f_equal. lia.
  - cbn [andb]. symmetry. apply (bound_hibits_zero 8). exact A. exact H.
Qed.

(* A Concat chain of 8-bit lanes k, k-1, ..., 0 (lane k in the high bits). *)
Fixpoint lane_chain (f: N -> exp) (k: nat) : exp :=
  match k with O => f 0 | S k' => Concat (f (N.of_nat k)) (lane_chain f k') end.

Lemma lane_chain_eval: forall c s f (g: N -> N) k v w,
  (forall i v w, i <= N.of_nat k -> eval_exp c s (f i) v w -> v = g i /\ w = 8) ->
  (forall i, g i < 256) ->
  eval_exp c s (lane_chain f k) v w ->
  w = 8 * N.succ (N.of_nat k) /\ v < 2^w /\ (forall i, i <= N.of_nat k -> byte v i = g i).
Proof.
  intros c s f g k. induction k as [|k IH]; intros v w F G E.
  - cbn [lane_chain] in E. destruct (F 0 v w (N.le_refl _) E) as [-> ->].
    split. reflexivity. split. apply G.
    intros i I. cbn in I. replace i with 0 by lia. apply byte_small, G.
  - cbn [lane_chain] in E. inversion E; subst.
    destruct (F _ _ _ (N.le_refl _) E1) as [-> ->].
    destruct (IH n2 w2) as [W2 [B2 BY]]; [|exact G|exact E2|].
    { intros i v w I E'. apply (F i v w); [rewrite Nat2N.inj_succ; lia | exact E']. }
    subst w2. rewrite Nat2N.inj_succ in *. split. lia. split.
    + unfold cbits. apply concat_bound. apply G. exact B2.
    + intros i I. destruct (N.eq_dec i (N.succ (N.of_nat k))) as [->|NE].
      * apply byte_cbits_hi. exact B2. apply G.
      * rewrite byte_cbits_lo by (exact B2 || lia). apply BY. lia.
Qed.

(** * VPCMPEQB *)

Definition cmpeq_lane (ra rb: var) (i: N) : exp :=
  BinOp OP_TIMES (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract (8*i+7) (8*i) (Var ra))
                                                    (Extract (8*i+7) (8*i) (Var rb))))
                 (Word 0xff 8).

Lemma extract_byte: forall n i, xbits n (8*i) (N.succ (8*i+7)) = byte n i.
Proof. intros. unfold byte. f_equal. lia. Qed.

Lemma byte_lt: forall n i, byte n i < 256.
Proof. intros. unfold byte, xbits. replace (8*i+8-8*i) with 8 by lia. apply N.mod_lt. discriminate. Qed.

Lemma cmpeq_lane_eval: forall c s ra rb i v w,
  eval_exp c s (cmpeq_lane ra rb i) v w ->
  v = (if byte (s ra) i =? byte (s rb) i then 255 else 0) /\ w = 8.
Proof.
  intros c s ra rb i v w E. unfold cmpeq_lane in E. inv_exp E.
  split; [|reflexivity]. rewrite !extract_byte. ev.
  destruct (_ =? _); reflexivity.
Qed.

(* The VPCMPEQB result statement: compare src against R_YMM0 into the
   temporary tv, then copy it to dst. *)
Definition vpcmpeqb_tail (src tv dst: var) : stmt :=
  Move tv (lane_chain (cmpeq_lane R_YMM0 src) 31) $;
  Move dst (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var tv))).

Lemma vpcmpeqb_tail_exec: forall c s src tv dst c' s' x,
  s R_YMM0 = 0 -> tv <> dst ->
  exec_stmt c s (vpcmpeqb_tail src tv dst) c' s' x ->
  x = None /\ exists y, y < 2^256 /\ cmpz_spec 32 y (s src) /\ s' = update (update s tv y) dst y.
Proof.
  intros c s src tv dst c' s' x Y0 NE X. unfold vpcmpeqb_tail in X.
  apply seq_move_inv in X. destruct X as [n [w [E X]]].
  apply move_inv in X. destruct X as [n2 [w2 [E2 [-> [-> ->]]]]].
  destruct (lane_chain_eval c s (cmpeq_lane R_YMM0 src) (fun i => if byte (s R_YMM0) i =? byte (s src) i then 255 else 0) 31 n w)
    as [W [B BY]]; [intros i v w' _ E'; exact (cmpeq_lane_eval _ _ _ _ _ _ _ E')
                   | intro i; destruct (_ =? _); [reflexivity|reflexivity] | exact E |].
  change (8 * N.succ (N.of_nat 31)) with 256 in W. subst w.
  inv_exp E2. rewrite update_updated. ev. rewrite N.mod_small by exact B.
  split. reflexivity. exists n. split. exact B. split; [|reflexivity].
  intros i I. rewrite BY by (cbn; lia). rewrite Y0. unfold zbyte.
  replace (byte 0 i) with 0 by (unfold byte, xbits; rewrite N.shiftr_0_l; reflexivity).
  rewrite N.eqb_sym. reflexivity.
Qed.

(** * VPMINUB *)

Definition pmin_lane (ra rb: var) (i: N) : exp :=
  Ite (BinOp OP_LT (Extract (8*i+7) (8*i) (Var ra)) (Extract (8*i+7) (8*i) (Var rb)))
      (Extract (8*i+7) (8*i) (Var ra)) (Extract (8*i+7) (8*i) (Var rb)).

Lemma pmin_lane_eval: forall c s ra rb i v w,
  eval_exp c s (pmin_lane ra rb i) v w ->
  v = N.min (byte (s ra) i) (byte (s rb) i) /\ w = 8.
Proof.
  intros c s ra rb i v w E. unfold pmin_lane in E. inv_exp E.
  rewrite !extract_byte. split; [|lia].
  ev. destruct (N.ltb_spec (byte (s ra) i) (byte (s rb) i)).
  - cbn. symmetry. apply N.min_l. lia.
  - cbn. symmetry. apply N.min_r. lia.
Qed.

Definition vpminub_tail (ra rb tv dst: var) : stmt :=
  Move tv (lane_chain (pmin_lane ra rb) 31) $;
  Move dst (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var tv))).

Definition pmin_spec (L y a b: N) :=
  forall i, i < L -> byte y i = N.min (byte a i) (byte b i).

Lemma vpminub_tail_exec: forall c s ra rb tv dst c' s' x,
  tv <> dst ->
  exec_stmt c s (vpminub_tail ra rb tv dst) c' s' x ->
  x = None /\ exists y, y < 2^256 /\ pmin_spec 32 y (s ra) (s rb) /\ s' = update (update s tv y) dst y.
Proof.
  intros c s ra rb tv dst c' s' x NE X. unfold vpminub_tail in X.
  apply seq_move_inv in X. destruct X as [n [w [E X]]].
  apply move_inv in X. destruct X as [n2 [w2 [E2 [-> [-> ->]]]]].
  destruct (lane_chain_eval c s (pmin_lane ra rb) (fun i => N.min (byte (s ra) i) (byte (s rb) i)) 31 n w)
    as [W [B BY]]; [intros i v w' _ E'; exact (pmin_lane_eval _ _ _ _ _ _ _ E')
                   | intro i; pose proof (byte_lt (s ra) i); lia | exact E |].
  change (8 * N.succ (N.of_nat 31)) with 256 in W. subst w.
  inv_exp E2. rewrite update_updated. ev. rewrite N.mod_small by exact B.
  split. reflexivity. exists n. split. exact B. split; [|reflexivity].
  intros i I. apply BY. cbn; lia.
Qed.

(** * VPMOVMSKB *)

(* Lane i >= 1 of the lifted VPMOVMSKB (lane 0 has no shift and uses
   temporaries 1-5); the accumulator is V_TEMP 0. *)
Fixpoint msk_lanes (y d: var) (n: nat) (i: N) : stmt :=
  match n with
  | O => Move d (Concat (Extract 63 32 (Var d)) (Var (V_TEMP 0))) $;
         Move d (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var d)))
  | S n' =>
    Move (V_TEMP (6*i)) (BinOp OP_AND (Var (V_TEMP 0)) (Word (N.lxor 4294967295 (2^i)) 32)) $;
    Move (V_TEMP (6*i+1)) (BinOp OP_RSHIFT (Var y) (Word (8*i+7) 256)) $;
    Move (V_TEMP (6*i+2)) (Extract 7 0 (Var (V_TEMP (6*i+1)))) $;
    Move (V_TEMP (6*i+3)) (BinOp OP_AND (Var (V_TEMP (6*i+2))) (Word 0x1 8)) $;
    Move (V_TEMP (6*i+4)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP (6*i+3)))) $;
    Move (V_TEMP (6*i+5)) (BinOp OP_LSHIFT (Var (V_TEMP (6*i+4))) (Word i 32)) $;
    Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP (6*i))) (Var (V_TEMP (6*i+5)))) $;
    msk_lanes y d n' (N.succ i)
  end.

Definition vpmovmskb_stmt (y d: var) : stmt :=
  Move (V_TEMP 0) (Word 0x0 32) $;
  Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xfffffffe 32)) $;
  Move (V_TEMP 2) (BinOp OP_RSHIFT (Var y) (Word 7 256)) $;
  Move (V_TEMP 3) (Extract 7 0 (Var (V_TEMP 2))) $;
  Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
  Move (V_TEMP 5) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 4))) $;
  Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 1)) (Var (V_TEMP 5))) $;
  msk_lanes y d 31 1.

Definition movmsk_spec (L r y: N) :=
  r < 2^L /\ forall j, j < L -> N.testbit r j = N.testbit y (8*j+7).

(* bit 0 of the lane value used by lane i *)
Lemma lane_bit: forall Y i, N.land (xbits (N.shiftr Y (8*i+7)) 0 8) 1 = N.b2n (N.testbit Y (8*i+7)).
Proof.
  intros Y i. apply N.bits_inj. intro j. rewrite N.land_spec.
  destruct (N.eq_dec j 0) as [->|J].
  - rewrite xbits_spec, N.shiftr_spec', !N.add_0_l.
    change (N.testbit 1 0) with true. change (0 <? 8) with true. rewrite !Bool.andb_true_r.
    destruct (N.testbit Y _); reflexivity.
  - replace (N.testbit 1 j) with false by (symmetry; apply (bound_hibits_zero 1); [reflexivity|lia]).
    rewrite Bool.andb_false_r. symmetry. apply (bound_hibits_zero 1). destruct (N.testbit Y _); cbn; lia. lia.
Qed.

Lemma msk_lane_step: forall acc Y i, acc < 2^i -> i < 32 ->
  let acc' := N.lor (N.land acc (N.lxor 4294967295 (2^i)))
                    (N.shiftl (N.b2n (N.testbit Y (8*i+7))) i mod 2^32) in
  acc' < 2^N.succ i /\ forall j, j < N.succ i ->
    N.testbit acc' j = if j =? i then N.testbit Y (8*i+7) else N.testbit acc j.
Proof.
  intros acc Y i A I acc'. subst acc'.
  assert (BITS: forall j, N.testbit (N.lor (N.land acc (N.lxor 4294967295 (2^i)))
                    (N.shiftl (N.b2n (N.testbit Y (8*i+7))) i mod 2^32)) j =
                  (if j <? i then N.testbit acc j else false) ||
                  ((j =? i) && N.testbit Y (8*i+7))).
  { intro j. rewrite N.lor_spec, N.land_spec, N.lxor_spec, Nmod_pow2_bits.
    destruct (N.ltb_spec j i).
    - rewrite N.shiftl_spec_low by lia. rewrite (N.pow2_bits_false i j) by lia.
      replace (N.eqb j i) with false by (symmetry; apply N.eqb_neq; lia).
      replace (N.testbit 4294967295 j) with true. destruct (N.testbit acc j); cbn; rewrite ?Bool.andb_false_r; reflexivity.
      change 4294967295 with (N.ones 32). symmetry. apply N.ones_spec_low. lia.
    - rewrite (bound_hibits_zero i acc j A H). cbn [andb orb].
      rewrite N.shiftl_spec_high by lia.
      destruct (N.eqb_spec j i) as [->|NE].
      + rewrite N.sub_diag. replace (i <? 32) with true by (symmetry; apply N.ltb_lt; exact I).
        destruct (N.testbit Y (8*i+7)); reflexivity.
      + replace (N.testbit (N.b2n _) (j - i)) with false.
        apply Bool.andb_false_r.
        symmetry. apply (bound_hibits_zero 1). destruct (N.testbit Y _); cbn; lia. lia. }
  split.
  - apply hibits_zero_bound. intros b B. rewrite BITS.
    replace (b <? i) with false by (symmetry; apply N.ltb_ge; lia).
    replace (b =? i) with false by (symmetry; apply N.eqb_neq; lia). reflexivity.
  - intros j J. rewrite BITS. destruct (N.eqb_spec j i) as [->|NE].
    + rewrite N.ltb_irrefl. reflexivity.
    + replace (j <? i) with true by (symmetry; apply N.ltb_lt; lia). apply Bool.orb_false_r.
Qed.

Lemma msk_lanes_exec: forall y d, not_temp y -> not_temp d -> forall n i c s c' s' x acc,
  i + N.of_nat n = 32 -> 1 <= i -> c (V_TEMP 0) = Some 32 ->
  s (V_TEMP 0) = acc -> acc < 2^i ->
  (forall j, j < i -> N.testbit acc j = N.testbit (s y) (8*j+7)) ->
  exec_stmt c s (msk_lanes y d n i) c' s' x ->
  x = None /\ movmsk_spec 32 (s' d) (s y) /\
  (forall v, v <> d -> not_temp v -> s' v = s v).
Proof.
  intros y d NY ND n. induction n as [|n IH]; intros i c s c' s' x acc IN I1 CT ACC AB AS X.
  - cbn [msk_lanes] in X. cbn in IN. rewrite N.add_0_r in IN. subst i.
    apply seq_move_inv in X. destruct X as [n1 [w1 [E1 X]]].
    apply move_inv in X. destruct X as [n2 [w2 [E2 [-> [-> ->]]]]].
    inv_exp E1. inv_exp E2. typs NY.
    split. reflexivity. rewrite update_updated, update_updated. split.
    + assert (CB: xbits (cbits (xbits (s d) 32 (N.succ 63)) 32 (s (V_TEMP 0))) 0 (N.succ 31) = acc).
      { rewrite ACC. apply N.bits_inj. intro j. rewrite xbits_spec, cbits_testbit by exact AB.
        rewrite N.add_0_r. destruct (N.ltb_spec j 32). change (N.succ 31) with 32.
        replace (j <? 32) with true by (symmetry; apply N.ltb_lt; exact H).
        apply Bool.andb_true_r.
        change (N.succ 31) with 32. replace (j <? 32) with false by (symmetry; apply N.ltb_ge; exact H).
        rewrite Bool.andb_false_r. symmetry. exact (bound_hibits_zero 32 acc j AB H). }
      ev. rewrite CB. split. exact AB. exact AS.
    + intros v V NT. rewrite update_frame, update_frame by exact V. reflexivity.
  - cbn [msk_lanes] in X.
    do 7 (apply seq_move_inv in X; destruct X as [?n [?w [?E X]]]).
    inv_exp E. inv_exp E0. inv_exp E1. inv_exp E2. inv_exp E3. inv_exp E4. inv_exp E5.
    rewrite Nat2N.inj_succ in IN. typs NY.
    match type of X with exec_stmt ?c2 ?s2 _ _ _ _ =>
      assert (SY: s2 y = s y) by (upd NY; reflexivity);
      edestruct (IH (N.succ i) c2 s2 c' s' x) as [X1 [MS FR]];
        [lia|lia|upd NY; reflexivity|upd NY; reflexivity| | |exact X|]
    end.
    + ev. upd NY. rewrite ACC. rewrite lane_bit.
      apply (msk_lane_step acc (s y) i AB). lia.
    + ev. upd NY. rewrite ACC, lane_bit. intros j J.
      destruct (msk_lane_step acc (s y) i AB ltac:(lia)) as [_ BJ]. rewrite BJ by exact J.
      destruct (N.eqb_spec j i) as [->|NE]. reflexivity. apply AS. lia.
    + rewrite SY in MS. split. exact X1. split. exact MS.
      intros v V NT. rewrite FR by assumption. upd NT. reflexivity.
Qed.

Lemma vpmovmskb_exec: forall y d c s c' s' x,
  not_temp y -> not_temp d ->
  exec_stmt c s (vpmovmskb_stmt y d) c' s' x ->
  x = None /\ movmsk_spec 32 (s' d) (s y) /\ (forall v, v <> d -> not_temp v -> s' v = s v).
Proof.
  intros y d c s c' s' x NY ND X. unfold vpmovmskb_stmt in X.
  do 7 (apply seq_move_inv in X; destruct X as [?n [?w [?E X]]]).
  inv_exp E. inv_exp E0. inv_exp E1. inv_exp E2. inv_exp E3. inv_exp E4. inv_exp E5.
  typs NY.
  match type of X with exec_stmt ?c2 ?s2 _ _ _ _ =>
    assert (SY: s2 y = s y) by (upd NY; reflexivity);
    edestruct (msk_lanes_exec y d NY ND 31 1 c2 s2 c' s' x) as [X1 [MS FR]];
      [reflexivity|reflexivity|upd NY; reflexivity|upd NY; reflexivity| | |exact X|]
  end.
  - ev. upd NY. pose proof (lane_bit (s y) 0) as L. change (8*0+7) with 7 in L. change (N.succ 7) with 8. rewrite L.
    destruct (N.testbit _ _); reflexivity.
  - ev. upd NY. intros j J. replace j with 0 by lia.
    pose proof (lane_bit (s y) 0) as L. change (8*0+7) with 7 in L. change (N.succ 7) with 8. rewrite L.
    change (8*0+7) with 7. destruct (N.testbit (s y) 7); reflexivity.
  - rewrite SY in MS. split. exact X1. split. exact MS.
    intros v V NT. rewrite FR by assumption. upd NT. reflexivity.
Qed.

(* After VPCMPEQB(0, x), the VPMOVMSKB mask says which bytes of x are zero. *)
Lemma movmsk_cmpz: forall r y x, movmsk_spec 32 r y -> cmpz_spec 32 y x -> msk_spec 32 r x.
Proof.
  intros r y x [_ M] C j J. rewrite M by exact J. apply (cmpz_bit 32); assumption.
Qed.

(** * TZCNT *)

(* Two moves repeated n times, given inversion-style descriptions of the two
   right-hand sides (the second may read only its own variable). *)
Lemma iter_move2_inv:
  forall c v1 v2 e1 e2 w1 w2 (F1: N -> N -> N) (F2: N -> N),
  v1 <> v2 -> c v1 = Some w1 -> c v2 = Some w2 ->
  (forall s n w, eval_exp c s e1 n w -> n = F1 (s v1) (s v2) /\ w = w1) ->
  (forall s n w, eval_exp c s e2 n w -> n = F2 (s v2) /\ w = w2) ->
  forall n s c' s' x,
  exec_stmt c s (N.iter n (Seq (Move v1 e1 $; Move v2 e2)) Nop) c' s' x ->
  let G := fun p : N * N => (F1 (fst p) (snd p), F2 (snd p)) in
  x = None /\ c' = c /\ s' v1 = fst (N.iter n G (s v1, s v2)) /\ s' v2 = snd (N.iter n G (s v1, s v2)) /\
  (forall v, v <> v1 -> v <> v2 -> s' v = s v).
Proof.
  intros c v1 v2 e1 e2 w1 w2 F1 F2 NE C1 C2 EV1 EV2 n.
  assert (NE': v2 <> v1) by (intro EQ; apply NE; symmetry; exact EQ).
  assert (CU1: update c v1 (Some w1) = c)
    by (extensionality z; unfold update; destruct (z == v1); [subst; symmetry; assumption | reflexivity]).
  assert (CU2: update c v2 (Some w2) = c)
    by (extensionality z; unfold update; destruct (z == v2); [subst; symmetry; assumption | reflexivity]).
  induction n as [|n IH] using N.peano_ind; intros s c' s' x XS G.
  - inversion XS; subst. repeat split.
  - rewrite N.iter_succ in XS. inversion XS; subst.
    + match goal with H: exec_stmt _ _ (Seq (Move _ _) (Move _ _)) _ _ (Some _) |- _ =>
        apply seq_move_inv in H; destruct H as [? [? [_ H]]]; inversion H end.
    + match goal with
        H1: exec_stmt _ _ (Seq (Move _ _) (Move _ _)) _ _ None,
        H2: exec_stmt _ _ (N.iter _ _ _) _ _ _ |- _ => rename H1 into XB; rename H2 into XR end.
      apply seq_move_inv in XB. destruct XB as [n1 [u1 [E1 XB]]].
      apply move_inv in XB. destruct XB as [n2 [u2 [E2 [-> [-> _]]]]].
      destruct (EV1 _ _ _ E1) as [-> ->]. rewrite CU1 in *.
      destruct (EV2 _ _ _ E2) as [-> ->]. rewrite CU2 in XR.
      destruct (IH _ _ _ _ XR) as [X1 [C1' [S1 [S2 SO]]]]. subst.
      rewrite update_updated in S1, S2. rewrite (update_frame s v1 _ v2 NE') in S1, S2.
      rewrite (update_frame _ v2 _ v1 NE), update_updated in S1, S2.
      repeat split.
      * rewrite S1, N.iter_succ, <- Niter_swap. reflexivity.
      * rewrite S2, N.iter_succ, <- Niter_swap. reflexivity.
      * intros v V1 V2. rewrite SO by assumption. rewrite !update_frame by assumption. reflexivity.
Qed.

Definition tz_cond (W:N) : exp :=
  Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8
    (BinOp OP_NEQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 W)) (Word 0x0 W))).
Definition tz_body (W:N) : stmt :=
  Move (V_TEMP 0) (Ite (tz_cond W) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 W))) $;
  Move (V_TEMP 1) (Ite (tz_cond W) (Var (V_TEMP 1))
                       (BinOp OP_OR (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 W)) (Word (2^(W-1)) W))).

(* TZCNT EAX,EAX and TZCNT RAX,RAX as lifted *)
Definition tzcnt32_stmt : stmt :=
  Move (V_TEMP 0) (Word 0x0 32) $;
  Move (V_TEMP 1) (Extract 31 0 (Var R_RAX)) $;
  Rep (Word 33 32) (tz_body 32) $;
  Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
  Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
  Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0))) $;
  Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))).

Definition tzcnt64_stmt : stmt :=
  Move (V_TEMP 0) (Word 0x0 64) $;
  Move (V_TEMP 1) (Var R_RAX) $;
  Rep (Word 65 64) (tz_body 64) $;
  Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)))) $;
  Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
  Move R_RAX (Var (V_TEMP 0)).

Lemma land1_b2n: forall b, N.land b 1 = N.b2n (N.testbit b 0).
Proof.
  intro b. apply N.bits_inj. intro j. rewrite N.land_spec.
  destruct (N.eq_dec j 0) as [->|J].
  - destruct (N.testbit b 0); reflexivity.
  - replace (N.testbit 1 j) with false by (symmetry; apply (bound_hibits_zero 1); [reflexivity|lia]).
    rewrite Bool.andb_false_r. symmetry. apply (bound_hibits_zero 1). destruct (N.testbit b 0); cbn; lia. lia.
Qed.

Lemma tz_cond_val: forall b (n2 n3:N),
  match N.b2n (negb (N.b2n (N.testbit b 0) =? 0)) mod 2^1 with N0 => n3 | _ => n2 end =
  if N.testbit b 0 then n2 else n3.
Proof. intros. destruct (N.testbit b 0); reflexivity. Qed.

Lemma tz_e1_eval: forall W c s n w, c (V_TEMP 0) = Some W -> c (V_TEMP 1) = Some W ->
  eval_exp c s (Ite (tz_cond W) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 W))) n w ->
  n = fst (tz_step W (s (V_TEMP 0), s (V_TEMP 1))) /\ w = W.
Proof.
  intros W c s n w C0 C1 E. unfold tz_cond in E. inv_exp E. typs C0. ev.
  rewrite land1_b2n, tz_cond_val. cbn [tz_step]. destruct (N.testbit _ 0); split; reflexivity.
Qed.

Lemma tz_e2_eval: forall W c s n w, c (V_TEMP 0) = Some W -> c (V_TEMP 1) = Some W ->
  eval_exp c s (Ite (tz_cond W) (Var (V_TEMP 1))
                    (BinOp OP_OR (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 W)) (Word (2^(W-1)) W))) n w ->
  n = snd (tz_step W (0, s (V_TEMP 1))) /\ w = W.
Proof.
  intros W c s n w C0 C1 E. unfold tz_cond in E. inv_exp E. typs C0. ev.
  rewrite land1_b2n, tz_cond_val. cbn [tz_step]. destruct (N.testbit _ 0); split; reflexivity.
Qed.

Lemma tz_pair: forall W n p,
  N.iter n (fun p : N * N => (fst (tz_step W (fst p, snd p)), snd (tz_step W (0, snd p)))) p =
  N.iter n (tz_step W) p.
Proof.
  intros W n. induction n as [|n IH] using N.peano_ind; intro p. reflexivity.
  rewrite !N.iter_succ, IH. destruct (N.iter n (tz_step W) p) as [c t]. cbn [fst snd tz_step].
  destruct (N.testbit t 0); reflexivity.
Qed.

Lemma tz_rep_exec: forall W c s c' s' x, 1 <= W ->
  c (V_TEMP 0) = Some W -> c (V_TEMP 1) = Some W ->
  exec_stmt c s (Rep (Word (N.succ W) W) (tz_body W)) c' s' x ->
  x = None /\ c' = c /\
  s' (V_TEMP 0) = fst (N.iter (N.succ W) (tz_step W) (s (V_TEMP 0), s (V_TEMP 1))) /\
  (forall v, not_temp v -> s' v = s v).
Proof.
  intros W c s c' s' x W1 C0 C1 X. inversion X; subst. apply ev_word in E. destruct E as [-> ->].
  unfold tz_body in XS.
  edestruct (iter_move2_inv c (V_TEMP 0) (V_TEMP 1)
               (Ite (tz_cond W) (Var (V_TEMP 0)) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x1 W)))
               (Ite (tz_cond W) (Var (V_TEMP 1))
                    (BinOp OP_OR (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 1 W)) (Word (2^(W-1)) W))) W W
               (fun a b => fst (tz_step W (a, b))) (fun b => snd (tz_step W (0, b)))) as [X1 [C' [S0 [_ SO]]]];
    [discriminate | exact C0 | exact C1
    | intros s0 n w E; exact (tz_e1_eval W c s0 n w C0 C1 E)
    | intros s0 n w E; exact (tz_e2_eval W c s0 n w C0 C1 E) | eassumption |].
  split. exact X1. split. exact C'. split.
  - rewrite S0. cbv beta. rewrite tz_pair. reflexivity.
  - intros v NT. apply SO; apply NT.
Qed.

Lemma reset_eq: forall s s' s'',
  (forall v, archtyps v <> None -> s' v = s'' v) -> (forall v, archtyps v = None -> s v = s'' v) ->
  reset_temps s s' = s''.
Proof.
  intros s s' s'' A B. extensionality v. unfold reset_temps, reset_vars.
  destruct (archtyps v) eqn:T. apply A. rewrite T. discriminate. apply B. exact T.
Qed.

Lemma regs_not_temp: forall v, archtyps v <> None -> not_temp v.
Proof. exact archtyps_not_temp. Qed.

Lemma tzcnt32_exec: forall s c' s' x,
  exec_stmt archtyps s tzcnt32_stmt c' s' x ->
  let X := xbits (s R_RAX) 0 32 in
  let r := fst (N.iter 33 (tz_step 32) (0, X)) in
  x = None /\ reset_temps s s' = s[R_ZF := N.b2n (r =? 0)][R_CF := N.b2n (X =? 0)][R_RAX := r].
Proof.
  intros s c' s' x XS X r. unfold tzcnt32_stmt in XS.
  do 2 (apply seq_move_inv in XS; destruct XS as [?n [?w [?E XS]]]).
  inv_exp E. inv_exp E0. ev_in XS.
  inversion XS; subst; [ match goal with H: exec_stmt _ _ (Rep _ _) _ _ (Some _) |- _ =>
    apply (tz_rep_exec 32) in H; [destruct H as [H _]; discriminate|lia|upd regs_not_temp; reflexivity|upd regs_not_temp; reflexivity] end |].
  match goal with H: exec_stmt _ _ (Rep _ _) _ _ None, H2: exec_stmt _ _ _ _ _ _ |- _ =>
    apply (tz_rep_exec 32) in H; [destruct H as [_ [-> [R0 RO]]]|lia|upd regs_not_temp; reflexivity|upd regs_not_temp; reflexivity];
    rename H2 into XT end.
  do 3 (apply seq_move_inv in XT; destruct XT as [?n [?w [?E XT]]]).
  apply move_inv in XT. destruct XT as [?n [?w [?E [-> [-> ->]]]]].
  repeat match goal with H: eval_exp _ _ _ _ _ |- _ => inv_exp H end. typs regs_not_temp. ev.
  split. reflexivity.
  assert (RX: s2 R_RAX = s R_RAX)
    by (rewrite RO by (apply regs_not_temp; discriminate); upd regs_not_temp; reflexivity).
  upd regs_not_temp. rewrite RX, R0. upd regs_not_temp. change (N.succ 31) with 32. change (N.succ 63) with 64.
  change (N.succ 32) with 33. fold X. fold r.
  assert (RB: r < 2^32).
  { destruct (tz_result 32 X ltac:(lia) (xbits_bound (s R_RAX) 0 32)) as [Z NZ]. change (N.succ 32) with 33 in Z, NZ. fold r in Z, NZ.
    destruct (N.eq_dec X 0) as [X0|X0]. rewrite (Z X0). reflexivity.
    destruct (NZ X0) as [R _]. eapply N.lt_trans. exact R. reflexivity. }
  replace (xbits (cbits (xbits (s R_RAX) 32 64) 32 r) 0 32) with r.
  2:{ symmetry. apply N.bits_inj. intro j. rewrite xbits_spec, cbits_testbit by exact RB. rewrite N.add_0_r.
      destruct (N.ltb_spec j 32). apply Bool.andb_true_r.
      rewrite Bool.andb_false_r. symmetry; exact (bound_hibits_zero 32 r j RB H). }
  replace (N.b2n (r =? 0) mod 2^1) with (N.b2n (r =? 0)) by (destruct (r =? 0); reflexivity).
  replace (N.b2n (X =? 0) mod 2^1) with (N.b2n (X =? 0)) by (destruct (X =? 0); reflexivity).
  apply reset_eq.
  - intros v V. unfold update.
    destruct (v == R_RAX); [reflexivity|]. destruct (v == R_CF); [reflexivity|]. destruct (v == R_ZF); [reflexivity|].
    rewrite RO by (apply regs_not_temp; exact V). unfold update.
    destruct (v == V_TEMP 1) as [->|]; [exfalso; apply V; reflexivity|].
    destruct (v == V_TEMP 0) as [->|]; [exfalso; apply V; reflexivity|]. reflexivity.
  - intros v V. unfold update.
    destruct (v == R_RAX) as [->|]; [discriminate|]. destruct (v == R_CF) as [->|]; [discriminate|].
    destruct (v == R_ZF) as [->|]; [discriminate|]. reflexivity.
Qed.


(* TZCNT EDX, ECX (strcmp's variant): reads ECX, writes EDX. *)
Definition tzcnt32_dc_stmt : stmt :=
  Move (V_TEMP 0) (Word 0x0 32) $;
  Move (V_TEMP 1) (Extract 31 0 (Var R_RCX)) $;
  Rep (Word 33 32) (tz_body 32) $;
  Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
  Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
  Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0))) $;
  Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))).

Lemma tzcnt32_dc_exec: forall s c' s' x,
  exec_stmt archtyps s tzcnt32_dc_stmt c' s' x ->
  let X := xbits (s R_RCX) 0 32 in
  let r := fst (N.iter 33 (tz_step 32) (0, X)) in
  x = None /\ reset_temps s s' = s[R_ZF := N.b2n (r =? 0)][R_CF := N.b2n (X =? 0)][R_RDX := r].
Proof.
  intros s c' s' x XS X r. unfold tzcnt32_dc_stmt in XS.
  do 2 (apply seq_move_inv in XS; destruct XS as [?n [?w [?E XS]]]).
  inv_exp E. inv_exp E0. ev_in XS.
  inversion XS; subst; [ match goal with H: exec_stmt _ _ (Rep _ _) _ _ (Some _) |- _ =>
    apply (tz_rep_exec 32) in H; [destruct H as [H _]; discriminate|lia|upd regs_not_temp; reflexivity|upd regs_not_temp; reflexivity] end |].
  match goal with H: exec_stmt _ _ (Rep _ _) _ _ None, H2: exec_stmt _ _ _ _ _ _ |- _ =>
    apply (tz_rep_exec 32) in H; [destruct H as [_ [-> [R0 RO]]]|lia|upd regs_not_temp; reflexivity|upd regs_not_temp; reflexivity];
    rename H2 into XT end.
  do 3 (apply seq_move_inv in XT; destruct XT as [?n [?w [?E XT]]]).
  apply move_inv in XT. destruct XT as [?n [?w [?E [-> [-> ->]]]]].
  repeat match goal with H: eval_exp _ _ _ _ _ |- _ => inv_exp H end. typs regs_not_temp. ev.
  split. reflexivity.
  assert (RS: s2 R_RCX = s R_RCX)
    by (rewrite RO by (apply regs_not_temp; discriminate); upd regs_not_temp; reflexivity).
  assert (RD: s2 R_RDX = s R_RDX)
    by (rewrite RO by (apply regs_not_temp; discriminate); upd regs_not_temp; reflexivity).
  upd regs_not_temp. rewrite RS, RD, R0. upd regs_not_temp. change (N.succ 31) with 32.
  change (N.succ 63) with 64. change (N.succ 32) with 33. fold X. fold r.
  assert (RB: r < 2^32).
  { destruct (tz_result 32 X ltac:(lia) (xbits_bound (s R_RCX) 0 32)) as [Z NZ]. change (N.succ 32) with 33 in Z, NZ. fold r in Z, NZ.
    destruct (N.eq_dec X 0) as [X0|X0]. rewrite (Z X0). reflexivity.
    destruct (NZ X0) as [R _]. eapply N.lt_trans. exact R. reflexivity. }
  replace (xbits (cbits (xbits (s R_RDX) 32 64) 32 r) 0 32) with r.
  2:{ symmetry. apply N.bits_inj. intro j. rewrite xbits_spec, cbits_testbit by exact RB. rewrite N.add_0_r.
      destruct (N.ltb_spec j 32). apply Bool.andb_true_r.
      rewrite Bool.andb_false_r. symmetry; exact (bound_hibits_zero 32 r j RB H). }
  replace (N.b2n (r =? 0) mod 2^1) with (N.b2n (r =? 0)) by (destruct (r =? 0); reflexivity).
  replace (N.b2n (X =? 0) mod 2^1) with (N.b2n (X =? 0)) by (destruct (X =? 0); reflexivity).
  apply reset_eq.
  - intros v V. unfold update.
    destruct (v == R_RDX); [reflexivity|]. destruct (v == R_CF); [reflexivity|]. destruct (v == R_ZF); [reflexivity|].
    rewrite RO by (apply regs_not_temp; exact V). unfold update.
    destruct (v == V_TEMP 1) as [->|]; [exfalso; apply V; reflexivity|].
    destruct (v == V_TEMP 0) as [->|]; [exfalso; apply V; reflexivity|]. reflexivity.
  - intros v V. unfold update.
    destruct (v == R_RDX) as [->|]; [discriminate|]. destruct (v == R_CF) as [->|]; [discriminate|].
    destruct (v == R_ZF) as [->|]; [discriminate|]. reflexivity.
Qed.
Lemma tzcnt64_exec: forall s c' s' x,
  exec_stmt archtyps s tzcnt64_stmt c' s' x ->
  let X := s R_RAX in
  let r := fst (N.iter 65 (tz_step 64) (0, X)) in
  x = None /\ reset_temps s s' = s[R_ZF := N.b2n (r =? 0)][R_CF := N.b2n (X =? 0)][R_RAX := r].
Proof.
  intros s c' s' x XS X r. unfold tzcnt64_stmt in XS.
  do 2 (apply seq_move_inv in XS; destruct XS as [?n [?w [?E XS]]]).
  inv_exp E. inv_exp E0. ev_in XS.
  match goal with T: _ R_RAX = Some _ |- _ => vm_compute in T; injection T; clear T; intro T; subst_eq T end.
  inversion XS; subst; [ match goal with H: exec_stmt _ _ (Rep _ _) _ _ (Some _) |- _ =>
    apply (tz_rep_exec 64) in H; [destruct H as [H _]; discriminate|lia|upd regs_not_temp; reflexivity|upd regs_not_temp; reflexivity] end |].
  match goal with H: exec_stmt _ _ (Rep _ _) _ _ None, H2: exec_stmt _ _ _ _ _ _ |- _ =>
    apply (tz_rep_exec 64) in H; [destruct H as [_ [-> [R0 RO]]]|lia|upd regs_not_temp; reflexivity|upd regs_not_temp; reflexivity];
    rename H2 into XT end.
  do 2 (apply seq_move_inv in XT; destruct XT as [?n [?w [?E XT]]]).
  apply move_inv in XT. destruct XT as [?n [?w [?E [-> [-> ->]]]]].
  repeat match goal with H: eval_exp _ _ _ _ _ |- _ => inv_exp H end. typs regs_not_temp. ev.
  split. reflexivity.
  assert (RX: s2 R_RAX = s R_RAX)
    by (rewrite RO by (apply regs_not_temp; discriminate); upd regs_not_temp; reflexivity).
  upd regs_not_temp. rewrite RX, R0. upd regs_not_temp.
  change (N.succ 64) with 65. fold X. fold r.
  replace (N.b2n (r =? 0) mod 2^1) with (N.b2n (r =? 0)) by (destruct (r =? 0); reflexivity).
  replace (N.b2n (X =? 0) mod 2^1) with (N.b2n (X =? 0)) by (destruct (X =? 0); reflexivity).
  apply reset_eq.
  - intros v V. unfold update.
    destruct (v == R_RAX); [reflexivity|]. destruct (v == R_CF); [reflexivity|]. destruct (v == R_ZF); [reflexivity|].
    rewrite RO by (apply regs_not_temp; exact V). unfold update.
    destruct (v == V_TEMP 1) as [->|]; [exfalso; apply V; reflexivity|].
    destruct (v == V_TEMP 0) as [->|]; [exfalso; apply V; reflexivity|]. reflexivity.
  - intros v V. unfold update.
    destruct (v == R_RAX) as [->|]; [discriminate|]. destruct (v == R_CF) as [->|]; [discriminate|].
    destruct (v == R_ZF) as [->|]; [discriminate|]. reflexivity.
Qed.

(** * Whole instructions, in the form the next state takes *)

Lemma ev_load: forall c s e1 e2 en len n w, eval_exp c s (Load e1 e2 en len) n w ->
  exists m a w', eval_exp c s e1 m (2^w'*8) /\ eval_exp c s e2 a w' /\
                 n = getmem w' en len m a /\ w = len * 8.
Proof. intros. inversion H; subst. do 3 eexists. repeat split; eassumption. Qed.

Lemma archtyps_ymm: forall v, archtyps v = Some 256 -> archtyps v <> None.
Proof. intros v H. rewrite H. discriminate. Qed.

(* After a statement that writes only temporaries and dst, the next state
   is s[dst := y]. *)
Lemma reset_dst: forall s s1 d y,
  archtyps d <> None -> s1 d = y -> (forall v, v <> d -> not_temp v -> s1 v = s v) ->
  reset_temps s s1 = update s d y.
Proof.
  intros s s1 d y D Y F. apply reset_one; [exact D | exact Y |].
  intros v V A. apply F. exact V. apply archtyps_not_temp. exact A.
Qed.

(* VPCMPEQB dst, YMM0, [r] *)
Lemma vpcmpeqb_ld_exec: forall s r dst c' s' x,
  s R_YMM0 = 0 -> archtyps r = Some 64 -> archtyps dst = Some 256 -> not_temp r ->
  exec_stmt archtyps s (Move (V_TEMP 0) (Load (Var V_MEM64) (Var r) LittleE 32) $;
                        vpcmpeqb_tail (V_TEMP 0) (V_TEMP 1) dst) c' s' x ->
  x = None /\ exists y, cmpz_spec 32 y (getmem 64 LittleE 32 (s V_MEM64) (s r)) /\
             reset_temps s s' = update s dst y.
Proof.
  intros s r dst c' s' x Y0 TR TD NR X.
  apply seq_move_inv in X. destruct X as [n0 [w0 [E X]]].
  apply ev_load in E. destruct E as [mm [a [w' [E1 [E2 [-> ->]]]]]].
  apply ev_var in E1. destruct E1 as [-> _]. apply ev_var in E2. destruct E2 as [-> T2].
  rewrite TR in T2. try (injection T2 as <-).
  apply vpcmpeqb_tail_exec in X; [| rewrite update_frame by discriminate; exact Y0 | ].
  2: { intro H. assert (archtyps dst = None) by (rewrite <- H; reflexivity). congruence. }
  destruct X as [-> [y [_ [C ->]]]]. split. reflexivity. exists y. split.
  - rewrite update_updated in C. exact C.
  - apply reset_dst. rewrite TD. discriminate. apply update_updated.
    intros v V NT. rewrite update_frame by exact V. rewrite !update_frame by (apply NT). reflexivity.
Qed.

(* VPCMPEQB dst, YMM0, [r + k] *)
Lemma vpcmpeqb_ldo_exec: forall s r k dst c' s' x,
  s R_YMM0 = 0 -> archtyps r = Some 64 -> archtyps dst = Some 256 -> not_temp r ->
  exec_stmt archtyps s (Move (V_TEMP 0) (BinOp OP_PLUS (Var r) (Word k 64)) $;
                        Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
                        vpcmpeqb_tail (V_TEMP 1) (V_TEMP 2) dst) c' s' x ->
  x = None /\ exists y, cmpz_spec 32 y (getmem 64 LittleE 32 (s V_MEM64) ((s r + k) mod 2^64)) /\
             reset_temps s s' = update s dst y.
Proof.
  intros s r k dst c' s' x Y0 TR TD NR X.
  apply seq_move_inv in X. destruct X as [n0 [w0 [E X]]].
  inv_exp E. rewrite TR in T. try (injection T as <-). ev_in X.
  apply seq_move_inv in X. destruct X as [n1 [w1 [E X]]].
  apply ev_load in E. destruct E as [mm [a [w' [E1 [E2 [-> ->]]]]]].
  apply ev_var in E1. destruct E1 as [-> _]. apply ev_var in E2. destruct E2 as [-> T2].
  rewrite update_updated in T2. try (injection T2 as <-).
  apply vpcmpeqb_tail_exec in X; [| rewrite !update_frame by discriminate; exact Y0 | ].
  2: { intro H. assert (archtyps dst = None) by (rewrite <- H; reflexivity). congruence. }
  destruct X as [-> [y [_ [C ->]]]]. split. reflexivity. exists y. split.
  - upd_in NR C. exact C.
  - apply reset_dst. rewrite TD. discriminate. apply update_updated.
    intros v V NT. rewrite update_frame by exact V. rewrite !update_frame by (apply NT). reflexivity.
Qed.

(* VPCMPEQB dst, YMM0, src (register) *)
Lemma vpcmpeqb_reg_exec: forall s src dst c' s' x,
  s R_YMM0 = 0 -> archtyps dst = Some 256 ->
  exec_stmt archtyps s (vpcmpeqb_tail src (V_TEMP 0) dst) c' s' x ->
  x = None /\ exists y, cmpz_spec 32 y (s src) /\ reset_temps s s' = update s dst y.
Proof.
  intros s src dst c' s' x Y0 TD X.
  apply vpcmpeqb_tail_exec in X; [| exact Y0 | ].
  2: { intro H. assert (archtyps dst = None) by (rewrite <- H; reflexivity). congruence. }
  destruct X as [-> [y [_ [C ->]]]]. split. reflexivity. exists y. split. exact C.
  apply reset_dst. rewrite TD. discriminate. apply update_updated.
  intros v V NT. rewrite update_frame by exact V. rewrite update_frame by (apply NT). reflexivity.
Qed.

(* VPMOVMSKB d32, y *)
Lemma vpmovmskb_rst_exec: forall s y d c' s' x,
  not_temp y -> archtyps d = Some 64 ->
  exec_stmt archtyps s (vpmovmskb_stmt y d) c' s' x ->
  x = None /\ exists r, movmsk_spec 32 r (s y) /\ reset_temps s s' = update s d r.
Proof.
  intros s y d c' s' x NY TD X.
  assert (ND: not_temp d) by (apply archtyps_not_temp; rewrite TD; discriminate).
  apply vpmovmskb_exec in X; [|exact NY|exact ND]. destruct X as [-> [M F]].
  split. reflexivity. exists (s' d). split. exact M.
  apply reset_dst. rewrite TD. discriminate. reflexivity. exact F.
Qed.

(* VPMINUB dst, ra, [r + k] *)
Lemma vpminub_ldo_exec: forall s ra r k dst c' s' x,
  archtyps r = Some 64 -> archtyps dst = Some 256 -> not_temp ra -> not_temp r ->
  exec_stmt archtyps s (Move (V_TEMP 0) (BinOp OP_PLUS (Var r) (Word k 64)) $;
                        Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
                        vpminub_tail ra (V_TEMP 1) (V_TEMP 2) dst) c' s' x ->
  x = None /\ exists y, pmin_spec 32 y (s ra) (getmem 64 LittleE 32 (s V_MEM64) ((s r + k) mod 2^64)) /\
             reset_temps s s' = update s dst y.
Proof.
  intros s ra r k dst c' s' x TR TD NA NR X.
  apply seq_move_inv in X. destruct X as [n0 [w0 [E X]]].
  inv_exp E. rewrite TR in T. try (injection T as <-). ev_in X.
  apply seq_move_inv in X. destruct X as [n1 [w1 [E X]]].
  apply ev_load in E. destruct E as [mm [a [w' [E1 [E2 [-> ->]]]]]].
  apply ev_var in E1. destruct E1 as [-> _]. apply ev_var in E2. destruct E2 as [-> T2].
  rewrite update_updated in T2. try (injection T2 as <-).
  apply vpminub_tail_exec in X.
  2: { intro H. assert (archtyps dst = None) by (rewrite <- H; reflexivity). congruence. }
  destruct X as [-> [y [_ [C ->]]]]. split. reflexivity. exists y. split.
  - upd_in NR C. exact C.
  - apply reset_dst. rewrite TD. discriminate. apply update_updated.
    intros v V NT. rewrite update_frame by exact V. rewrite !update_frame by (apply NT). reflexivity.
Qed.

(* VPMINUB dst, ra, rb (registers) *)
Lemma vpminub_reg_exec: forall s ra rb dst c' s' x,
  archtyps dst = Some 256 ->
  exec_stmt archtyps s (vpminub_tail ra rb (V_TEMP 0) dst) c' s' x ->
  x = None /\ exists y, pmin_spec 32 y (s ra) (s rb) /\ reset_temps s s' = update s dst y.
Proof.
  intros s ra rb dst c' s' x TD X.
  apply vpminub_tail_exec in X.
  2: { intro H. assert (archtyps dst = None) by (rewrite <- H; reflexivity). congruence. }
  destruct X as [-> [y [_ [C ->]]]]. split. reflexivity. exists y. split. exact C.
  apply reset_dst. rewrite TD. discriminate. apply update_updated.
  intros v V NT. rewrite update_frame by exact V. rewrite update_frame by (apply NT). reflexivity.
Qed.

(** * VPCMPEQB between two registers, VPBROADCASTB *)

Definition vpcmpeqb_rr (ra rb tv dst: var) : stmt :=
  Move tv (lane_chain (cmpeq_lane ra rb) 31) $;
  Move dst (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var tv))).

Definition cmpeq_spec (L y a b: N) :=
  forall i, i < L -> byte y i = if byte a i =? byte b i then 255 else 0.

Lemma vpcmpeqb_rr_exec: forall s ra rb dst c' s' x,
  archtyps dst = Some 256 ->
  exec_stmt archtyps s (vpcmpeqb_rr ra rb (V_TEMP 0) dst) c' s' x ->
  x = None /\ exists y, cmpeq_spec 32 y (s ra) (s rb) /\ reset_temps s s' = update s dst y.
Proof.
  intros s ra rb dst c' s' x TD X. unfold vpcmpeqb_rr in X.
  apply seq_move_inv in X. destruct X as [n [w [E X]]].
  apply move_inv in X. destruct X as [n2 [w2 [E2 [-> [-> ->]]]]].
  destruct (lane_chain_eval archtyps s (cmpeq_lane ra rb) (fun i => if byte (s ra) i =? byte (s rb) i then 255 else 0) 31 n w)
    as [W [B BY]]; [intros i v w' _ E'; exact (cmpeq_lane_eval _ _ _ _ _ _ _ E')
                   | intro i; destruct (_ =? _); [reflexivity|reflexivity] | exact E |].
  change (8 * N.succ (N.of_nat 31)) with 256 in W. subst w.
  inv_exp E2. rewrite update_updated. ev. rewrite N.mod_small by exact B.
  split. reflexivity. exists n. split.
  - intros i I. apply BY. cbn; lia.
  - apply reset_dst. rewrite TD. discriminate. apply update_updated.
    intros v V NT. rewrite update_frame by exact V. rewrite update_frame by (apply NT). reflexivity.
Qed.

(* The broadcast chain: Concat (... (Concat t t) ...) t, k+1 copies of t. *)
Fixpoint bc_chain (t: var) (k: nat) : exp :=
  match k with O => Var t | S k' => Concat (bc_chain t k') (Var t) end.

Lemma byte_cbits_up: forall a b i, b < 2^8 -> byte (cbits a 8 b) (N.succ i) = byte a i.
Proof.
  intros a b i B. apply N.bits_inj. intro j. rewrite !byte_testbit.
  destruct (N.ltb_spec j 8); [|reflexivity]. cbn [andb].
  rewrite cbits_testbit by exact B.
  replace (j + 8 * N.succ i <? 8) with false by (symmetry; apply N.ltb_ge; lia).
  f_equal. lia.
Qed.

Lemma bc_chain_eval: forall c s t v k n w, c t = Some 8 -> s t = v -> v < 256 ->
  eval_exp c s (bc_chain t k) n w ->
  w = 8 * N.succ (N.of_nat k) /\ n < 2^w /\ forall i, i <= N.of_nat k -> byte n i = v.
Proof.
  intros c s t v k. induction k as [|k IH]; intros n w CT ST V E.
  - cbn [bc_chain] in E. apply ev_var in E. destruct E as [-> T]. rewrite CT in T. injection T as <-.
    split. reflexivity. split. rewrite ST. exact V.
    intros i I. cbn in I. replace i with 0 by lia. rewrite ST. apply byte_small, V.
  - cbn [bc_chain] in E. apply ev_concat in E. destruct E as [n1 [w1 [n2 [w2 [E1 [E2 [-> ->]]]]]]].
    destruct (IH n1 w1 CT ST V E1) as [W1 [B1 BY]].
    apply ev_var in E2. destruct E2 as [-> T]. rewrite CT in T. injection T as <-.
    rewrite ST. subst w1. rewrite Nat2N.inj_succ.
    split. lia. split.
    + unfold cbits. replace (8 * N.succ (N.of_nat k) + 8) with (8 + 8 * N.succ (N.of_nat k)) by lia.
      rewrite N.add_comm. apply concat_bound. exact B1. exact V.
    + intros i I. destruct (N.eq_dec i 0) as [->|NZ].
      * change 0 with (8 * 0). replace (cbits n1 8 v) with (cbits n1 (8 * 1) v) by reflexivity.
        rewrite byte_cbits_lo by (exact V || lia). apply byte_small, V.
      * replace i with (N.succ (N.pred i)) by lia. rewrite byte_cbits_up by exact V. apply BY. lia.
Qed.

Definition vpbroadcastb0_stmt : stmt :=
  Move (V_TEMP 0) (Extract 7 0 (Var R_YMM0)) $;
  Move R_YMM0 (bc_chain (V_TEMP 0) 31) $;
  Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM0))).

(* VPBROADCASTB YMM0, XMM0 *)
Lemma vpbroadcastb0_exec: forall s c' s' x,
  exec_stmt archtyps s vpbroadcastb0_stmt c' s' x ->
  x = None /\ exists y, (forall i, i < 32 -> byte y i = s R_YMM0 mod 2^8) /\
             reset_temps s s' = update s R_YMM0 y.
Proof.
  intros s c' s' x X. unfold vpbroadcastb0_stmt in X.
  apply seq_move_inv in X. destruct X as [n0 [w0 [E X]]]. inv_exp E.
  apply seq_move_inv in X. destruct X as [n1 [w1 [E X]]].
  apply move_inv in X. destruct X as [n2 [w2 [E2 [-> [-> ->]]]]].
  apply (bc_chain_eval _ _ (V_TEMP 0) (xbits (s R_YMM0) 0 (N.succ 7))) in E;
    [destruct E as [W [B BY]] | apply update_updated | apply update_updated | apply xbits_bound].
  change (8 * N.succ (N.of_nat 31)) with 256 in W. subst w1.
  inv_exp E2. rewrite update_updated. ev. rewrite (N.mod_small n1) by exact B.
  split. reflexivity. exists n1. split.
  - intros i I. rewrite BY by (cbn; lia). unfold xbits. rewrite N.shiftr_0_r. reflexivity.
  - apply reset_dst. discriminate. apply update_updated.
    intros v V NT. rewrite !update_frame by (first [exact V | apply NT]). reflexivity.
Qed.

(* VPCMPEQB dst, ra, [r]: compare register ra against the 32 bytes at [r]. *)
Lemma vpcmpeqb_rld_exec: forall s ra r dst c' s' x,
  archtyps r = Some 64 -> archtyps dst = Some 256 -> not_temp ra -> not_temp r -> ra <> V_TEMP 0 ->
  exec_stmt archtyps s (Move (V_TEMP 0) (Load (Var V_MEM64) (Var r) LittleE 32) $;
                        vpcmpeqb_rr ra (V_TEMP 0) (V_TEMP 1) dst) c' s' x ->
  x = None /\ exists y, cmpeq_spec 32 y (s ra) (getmem 64 LittleE 32 (s V_MEM64) (s r)) /\
             reset_temps s s' = update s dst y.
Proof.
  intros s ra r dst c' s' x TR TD NA NR NE X.
  apply seq_move_inv in X. destruct X as [n0 [w0 [E X]]].
  apply ev_load in E. destruct E as [mm [a [w' [E1 [E2 [-> ->]]]]]].
  apply ev_var in E1. destruct E1 as [-> _]. apply ev_var in E2. destruct E2 as [-> T2].
  rewrite TR in T2. injection T2 as <-.
  unfold vpcmpeqb_rr in X.
  apply seq_move_inv in X. destruct X as [nn [ww [E X]]].
  apply move_inv in X. destruct X as [n2 [w2 [E2 [-> [-> ->]]]]].
  set (M := s[V_TEMP 0 := getmem 64 LittleE 32 (s V_MEM64) (s r)]) in *.
  destruct (lane_chain_eval (archtyps[V_TEMP 0 := Some (32*8)]) M (cmpeq_lane ra (V_TEMP 0))
              (fun i => if byte (M ra) i =? byte (M (V_TEMP 0)) i then 255 else 0) 31 nn ww)
    as [W [B BY]]; [intros i v w' _ E'; exact (cmpeq_lane_eval _ _ _ _ _ _ _ E')
                   | intro i; destruct (_ =? _); [reflexivity|reflexivity] | exact E |].
  change (8 * N.succ (N.of_nat 31)) with 256 in W. subst ww.
  inv_exp E2. rewrite update_updated. ev. rewrite N.mod_small by exact B.
  split. reflexivity. exists nn. split.
  - intros i I. rewrite BY by (cbn; lia). subst M.
    rewrite (update_frame s (V_TEMP 0) _ ra) by exact NE.
    rewrite update_updated. reflexivity.
  - apply reset_dst. rewrite TD. discriminate. apply update_updated.
    intros v V NT. rewrite update_frame by exact V. subst M.
    rewrite !update_frame by (first [exact V | apply NT]). reflexivity.
Qed.

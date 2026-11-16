From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import stpcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
From Grok.scratch Require Import GrokStr_draft.
Import ARM8Notations.
Open Scope N.

Theorem stpcpy_welltyped: welltyped_prog arm8typctx stpcpy_armv8.
Proof. Picinae_typecheck. Qed.

Lemma xor_mod8: ∀ q d, (N.lxor q d) mod 8 = 0 -> msub 64 q d mod 8 = 0.
Proof.
  intros q d H. change 8 with (2^3) in *. rewrite msub_mod_pow2. apply msub_move_0_r.
  apply N.bits_inj. intro i. destruct (N.lt_ge_cases i 3) as [L|G].
  - rewrite !N.mod_pow2_bits_low by exact L.
    assert (B: N.testbit ((N.lxor q d) mod 2^3) i = false) by (rewrite H; apply N.bits_0).
    rewrite N.mod_pow2_bits_low, N.lxor_spec in B by exact L.
    destruct (N.testbit q i), (N.testbit d i); try reflexivity; discriminate.
  - rewrite !N.mod_pow2_bits_high by exact G. reflexivity.
Qed.

Lemma byte_test: ∀ x b, x < 2^8 -> negb ((x >> 0) mod 2^32 =? 0) = b -> (b = true /\ x ≠ 0) \/ (b = false /\ x = 0).
Proof.
  intros x b X B. rewrite N.shiftr_0_r, N.mod_small in B by (eapply N.lt_le_trans; [exact X | discriminate]).
  destruct (N.eqb_spec x 0); subst b; simpl; [right|left]; split; auto.
Qed.

Lemma bcp_succ: ∀ m d q k,
  bcp m d q (N.to_nat (k+1)) = setmem 64 LittleE 1 (bcp m d q (N.to_nat k)) (d + k) (getmem 64 LittleE 1 (bcp m d q (N.to_nat k)) (q + k)).
Proof. intros. replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia. cbn [bcp]. rewrite N2Nat.id. reflexivity. Qed.

Lemma bnz_word: ∀ m d q k w, msub 64 q d mod 8 = 0 ->
  getmem 64 LittleE 8 (bcp m d q (N.to_nat k)) (q + k) = w ->
  (∀ i, i < 8 -> byte w i ≠ 0) -> bnz m d q k -> bnz m d q (k+8).
Proof.
  intros m d q k w AL W B NZ i I. destruct (N.lt_ge_cases i k) as [L|G]. apply NZ, L.
  replace i with (k + (i-k)) by lia. replace (N.to_nat (k + (i-k))) with (N.to_nat k + N.to_nat (i-k))%nat by lia.
  replace (q + (k + (i-k))) with (q + N.of_nat (N.to_nat k + N.to_nat (i-k))) by lia.
  rewrite (bcp_word_read m d q w (N.to_nat k)) by (rewrite ?N2Nat.id; assumption || lia).
  rewrite N2Nat.id. apply B. lia.
Qed.

Lemma bcp_word8: ∀ m d q k, msub 64 q d mod 8 = 0 ->
  bcp m d q (N.to_nat (k+8)) = setmem 64 LittleE 8 (bcp m d q (N.to_nat k)) (d + k) (getmem 64 LittleE 8 (bcp m d q (N.to_nat k)) (q + k)).
Proof.
  intros. replace (N.to_nat (k+8)) with (N.to_nat k + 8)%nat by lia.
  rewrite (bcp_word m d q (getmem 64 LittleE 8 (bcp m d q (N.to_nat k)) (q + k)) (N.to_nat k)) by (rewrite ?N2Nat.id; assumption || reflexivity).
  rewrite N2Nat.id. reflexivity.
Qed.

Lemma land_mod_r: ∀ a b n, b < 2^n -> N.land a b = N.land (a mod 2^n) b.
Proof.
  intros a b n B. apply N.bits_inj. intro i. rewrite !N.land_spec.
  destruct (N.lt_ge_cases i n) as [L|G].
  - rewrite N.mod_pow2_bits_low by exact L. reflexivity.
  - rewrite (testbit_ge_bound b n i B G). rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma haszero_none': ∀ x, x < 2^64 ->
  N.land (N.land (x + K8) (N.lxor x 18446744073709551615)) H8 = 0 -> ∀ i, i < 8 -> byte x i ≠ 0.
Proof.
  intros x X T. apply haszero_none.
  change (N.lxor x 18446744073709551615) with (N.lnot x 64) in T.
  rewrite (land_mod_r (x + K8) (N.lnot x 64) 64) in T. exact T.
  assert (LG: N.log2 x < 64) by (destruct (N.eq_dec x 0) as [->|NZ]; [reflexivity | apply N.log2_lt_pow2; lia]).
  rewrite N.lnot_sub_low by exact LG. unfold N.ones. rewrite N.shiftl_1_l. lia.
Qed.

Section Invariants.
  Variables (sp mem raddr d q : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e950 => Inv 0 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e95c => Inv 0 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e990 => Inv 0 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X4 = K8 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e9ac => Inv 0 (∃ k, s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15e9bc => Post 0 (∃ k, bnz mem d q k /\ getmem 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k) = 0 /\
                          s V_MEM64 = bcp mem d q (N.to_nat (k+1)) /\
                          s R_X0 = (d + k) mod 2^64 /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition stpcpy_exits := make_exits 0 stpcpy_armv8 invs.
  Definition stpcpy_invs := make_invs 0 stpcpy_armv8 invs.
End Invariants.

Ltac al3 := match goal with AL: msub 64 ?q ?d mod 8 = 0 |- msub 3 ?q ?d = 0 =>
  transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL] end.
Ltac modeq := rewrite ?N.Div0.add_mod_idemp_r, ?N.Div0.add_mod_idemp_l; f_equal; lia.

Theorem stpcpy_partial_correctness:
  ∀ prog s sp mem raddr d q t xs'
    (PROG: stpcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e950, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q),
  satisfies_all prog (stpcpy_invs sp mem raddr d q) (stpcpy_exits sp mem raddr d q) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=stpcpy_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold stpcpy_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply stpcpy_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as BD. pose proof (MDL1 R_X1 64 eq_refl) as BQ.
    rewrite X0 in BD. rewrite X1 in BQ.
    repeat arm8_step.
    + exists 0. apply N.eqb_eq in BC. split.
      * transitivity (msub 64 q d mod 2^3).
        rewrite msub_mod_pow2. reflexivity. apply xor_mod8. exact BC.
      * repeat split; rewrite ?N.add_0_r, ?N.mod_small by assumption; try assumption; try reflexivity.
        intros i I. lia.
    + exists 0.
      repeat split; rewrite ?N.add_0_r, ?N.mod_small by assumption; try assumption; try reflexivity.
      intros i I. lia.
  - destruct PRE as (k & AL & X0 & X1 & NZ & MEM & SP & X30).
    repeat arm8_step.
    + exists k. split. al3. split. reflexivity. repeat split; assumption.
    + exists k. apply N.eqb_eq in BC0. repeat split; try assumption. rewrite bcp_succ. reflexivity.
    + exists (k+1). apply N.eqb_neq in BC0. split. al3. repeat split; try assumption.
      * modeq.
      * modeq.
      * apply bnz_succ; assumption.
      * rewrite bcp_succ. reflexivity.
  - destruct PRE as (k & AL & X4 & X0 & X1 & NZ & MEM & SP & X30).
    repeat arm8_step.
    + exists (k+8). apply N.eqb_eq in BC. split. al3. split. reflexivity. repeat split; try assumption.
      * modeq.
      * modeq.
      * apply (bnz_word mem d q k _ AL eq_refl); [|exact NZ].
        apply haszero_none'; [apply getmem_bound | exact BC].
      * rewrite bcp_word8 by exact AL. reflexivity.
    + exists k. repeat split; assumption.
  - destruct PRE as (k & X0 & X1 & NZ & MEM & SP & X30).
    repeat arm8_step.
    all: pose proof (getmem_bound 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k)) as B;
         change (2^(1*8)) with (2^8) in B;
         destruct (byte_test _ _ B BC) as [[T NZK] | [T ZK]]; try discriminate T.
    + exists (k+1). repeat split; try assumption.
      * modeq.
      * modeq.
      * apply bnz_succ; assumption.
      * rewrite bcp_succ. reflexivity.
    + exists k. repeat split; try assumption. rewrite bcp_succ. reflexivity.
Qed.

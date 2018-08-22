(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2018 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Interpreter Theory module:                          MMMMMMMMMMMMMMMMM^NZMMN+Z
   * theory of store-updates and memory-accesses,       MMMMMMMMMMMMMMM/.$MZM8O+
   * theory of two's-complement binary numbers,          MMMMMMMMMMMMMM7..$MNDM+
   * determinism of Unknown-free programs,                MMDMMMMMMMMMZ7..$DM$77
   * monotonicity of stores,                               MMMMMMM+MMMZ7..7ZM~++
   * boundedness of While-free programs,                    MMMMMMMMMMM7..ZNOOMZ
   * inductive schemas for program analysis, and             MMMMMMMMMM$.$MOMO=7
   * frame theorems for assignment-free programs.             MDMMMMMMMO.7MDM7M+
                                                               ZMMMMMMMM.$MM8$MN
   To compile this module, first load the Picinae_core         $ZMMMMMMZ..MMMOMZ
   module and compile it with menu option                       ?MMMMMM7..MNN7$M
   Compile->Compile_buffer.                                      ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Export Picinae_core.
Require Import NArith.
Require Import ZArith.
Require Import Program.Equality.
Require Import FunctionalExtensionality.
Require Setoid.



(* Tactic "vreflexivity v" reduces "v==v" to true (actually "left _"). *)
Theorem iseq_refl {A} {_:EqDec A}:
  forall (x:A), exists (H: x = x), (x == x) = left H.
Proof.
  intro. destruct (x == x).
    eexists. reflexivity.
    contradict n. reflexivity.
Qed.

Ltac vreflexivity v :=
  let Hveq := fresh "H" v "eq" in let H := fresh in
  destruct (iseq_refl v) as [Hveq H];
  rewrite H in *;
  clear H; try clear Hveq.

(* Tactic "vantisym v1 v2" reduces "v1==v2" to false (actually "right _")
   and introduces a subgoal of "v1<>v2". *)
Theorem iseq_antisym {A} {_:EqDec A}:
  forall (x y:A), x<>y -> exists (H: x<>y), (x == y) = right H.
Proof.
  intros. destruct (x == y).
    contradict H. assumption.
    eexists. reflexivity.
Qed.

Ltac vantisym v1 v2 :=
  let H1 := fresh in let Hv1v2 := fresh "H" v1 v2 in let H2 := fresh in
  enough (H1: v1 <> v2);
  [ destruct (iseq_antisym v1 v2 H1) as [Hv1v2 H2];
    rewrite H2 in *;
    clear H1 H2; try clear Hv1v2 |].


Section PartialFunctionTheory.

(* Symmetric updates preserve the partial order relation. *)
Theorem pfsub_update {A B} {_: EqDec A}:
  forall (f g: A -> option B) (SS: f ⊆ g) (x:A) (y:option B),
  update f x y ⊆ update g x y.
Proof.
  intros. unfold update. intros z y' H. destruct (z == x).
    assumption.
    apply SS. assumption.
Qed.

Definition updateall {A B:Type} (f g: A -> option B) (x:A) : option B :=
  match g x with None => f x | Some y => Some y end.

Theorem updateall_subset {A B}:
  forall (f g: A->option B), f ⊆ g -> updateall g f = g.
Proof.
  unfold pfsub, updateall. intros.
  apply functional_extensionality. intro x. specialize H with (x:=x). destruct (f x).
    symmetry. apply H. reflexivity.
    reflexivity.
Qed.

Theorem subset_updateall {A B}:
  forall (f g: A->option B), f ⊆ updateall g f.
Proof. unfold pfsub, updateall. intros. rewrite H. reflexivity. Qed.

Theorem updateall_mono {A B}:
  forall (f1 f2 g: A -> option B) (SS: f1 ⊆ f2), updateall f1 g ⊆ updateall f2 g.
Proof.
  unfold pfsub, updateall. intros. destruct (g x).
    assumption.
    apply SS. assumption.
Qed.

(* Frame property: Updating variable x does not affect the value of any other variable z. *)
Theorem update_frame {A B} {_: EqDec A}:
  forall (s:A->B) x y z (NE: z<>x),
  update s x y z = s z.
Proof.
  intros. unfold update. destruct (z == x).
    exfalso. apply NE. assumption.
    reflexivity.
Qed.

(* Updating x and then reading it returns its new value. *)
Theorem update_updated {A B} {_: EqDec A}:
  forall (s:A->B) x y,
  update s x y x = y.
Proof.
  intros. unfold update. vreflexivity x. reflexivity.
Qed.

(* Reversing the order of assignments to two different variables yields the same store. *)
Theorem update_swap {A B} {_: EqDec A}:
  forall (s:A->B) x1 x2 y1 y2 (NE:x1<>x2),
  update (update s x1 y1) x2 y2 = update (update s x2 y2) x1 y1.
Proof.
  intros. extensionality z. unfold update.
  destruct (z == x2).
    subst z. vantisym x2 x1. reflexivity. intro. apply NE. symmetry. assumption.
    destruct (z == x1); reflexivity.
Qed.

(* Overwriting a store value discards the earlier update. *)
Theorem update_cancel {A B} {_: EqDec A}:
  forall (s:A->B) x y1 y2,
  update (update s x y1) x y2 = update s x y2.
Proof.
  intros. apply functional_extensionality. intro z. unfold update.
  destruct (z == x); reflexivity.
Qed.

(* Equivalent updates within a sequence of updates can be disregarded when searching
   for updates that cancel each other via update_cancel. *)
Theorem update_inner_same {A B} {_: EqDec A}:
  forall (s1 s2:A->B) x1 y1 x2 y2,
    update s1 x2 y2 = update s2 x2 y2 ->
  update (update s1 x1 y1) x2 y2 = update (update s2 x1 y1) x2 y2.
Proof.
  intros. destruct (x1 == x2).
    subst x2. do 2 rewrite update_cancel. assumption.
    rewrite (update_swap s1), (update_swap s2) by assumption. rewrite H. reflexivity.
Qed.

(* If variable v's value u is known for store s, then s[v:=u] is the same as s.
   This fact is useful for "stocking" store expressions with explicit updates that
   reveal the values of known variables, allowing tactics to use that information to
   make progress without searching the rest of the proof context. *)
Theorem store_upd_eq {A B} {_: EqDec A}:
  forall (s: A -> option B) v u (SV: s v = u),
  s = update s v u.
Proof.
  intros.
  extensionality v0.
  destruct (v0 == v).
    subst v0. rewrite update_updated. exact SV.
    rewrite update_frame. reflexivity. assumption.
Qed.

End PartialFunctionTheory.


Section TwosComplement.

(* Reinterpreting an unsigned nat as a signed integer in two's complement form
   always yields an integer in range [-2^w, 2^w), where w is one less than the
   bitwidth of the original unsigned number. *)

Remark N2Z_pow2_pos:
  forall w, (0 < Z.of_N (2^w))%Z.
Proof. intros. rewrite N2Z.inj_pow. apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg. Qed.

Remark N2Z_pow2_nonzero:
  forall w, Z.of_N (2^w) <> Z0.
Proof. intros. apply Z.neq_sym, Z.lt_neq, N2Z_pow2_pos. Qed.

Lemma hibits_zero_bound:
  forall n w,
    (forall b, w<=b -> N.testbit n b = false) ->
  n < 2^w.
Proof.
  intros.
  destruct n. destruct (2^w) eqn:H1. apply N.pow_nonzero in H1. contradict H1. discriminate 1. reflexivity.
  apply N.compare_nge_iff. intro P.
    apply N.log2_le_pow2 in P; [|reflexivity].
    apply H in P. rewrite N.bit_log2 in P. discriminate P. discriminate 1.
Qed.

Lemma bound_hibits_zero:
  forall w n b, n < 2^w -> w<=b -> N.testbit n b = false.
Proof.
  intros. destruct n. reflexivity. apply N.bits_above_log2, N.log2_lt_pow2. reflexivity.
  eapply N.lt_le_trans. eassumption.
  apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

Theorem signbit:
  forall n w (LT: n < 2^w), N.testbit n (N.pred w) = (2^(N.pred w) <=? n).
Proof.
  intros. destruct (_ <=? _) eqn:H.

    destruct (N.testbit _ _) eqn:SB. reflexivity.
    exfalso. apply N.leb_le in H. apply H, N.lt_gt, hibits_zero_bound.
    intros b LE. apply N.lt_eq_cases in LE. destruct LE.
      eapply bound_hibits_zero. exact LT. apply N.lt_pred_le. assumption.
      subst b. assumption.

    eapply bound_hibits_zero. apply N.leb_gt, H. reflexivity.
Qed.

Theorem toZ_bounds:
  forall n w, n < 2^w -> signed_range w (toZ w n).
Proof.
  intros. unfold toZ, signed_range.
  destruct w as [|w]. apply N.lt_1_r in H. subst n. rewrite N.bits_0. reflexivity.
  rewrite signbit by assumption. destruct (_ <=? _) eqn:SB; split.

    apply Z.le_add_le_sub_l. rewrite Z.add_opp_r.
    rewrite <- N2Z.inj_sub by (apply N.pow_le_mono_r; [ discriminate 1 | apply N.le_pred_l]).
    apply N2Z.inj_le.
    rewrite <- (N.mul_1_l (2^(N.pred _))).
    rewrite <- (N.succ_pred (N.pos w)) at 1 by discriminate 1.
    rewrite N.pow_succ_r', <- N.mul_sub_distr_r, N.mul_1_l.
    apply N.leb_le, SB.

    eapply Z.lt_le_trans.
      apply Z.lt_sub_0. apply N2Z.inj_lt. assumption.
      apply N2Z.is_nonneg.

    transitivity Z0; [apply Z.opp_nonpos_nonneg|]; apply N2Z.is_nonneg.

    apply N2Z.inj_lt, N.leb_gt, SB.
Qed.

Theorem ofZ_bound:
  forall z w, ofZ w z < 2^w.
Proof.
  intros. rewrite <- (N2Z.id (2^w)). unfold ofZ. apply Z2N.inj_lt;
  solve [ apply Z.mod_pos_bound, N2Z_pow2_pos | apply N2Z.is_nonneg ].
Qed.

(* ofZ inverts toZ *)
Theorem ofZ_toZ:
  forall n w (LT: n < 2^w), ofZ w (toZ w n) = n.
Proof.
  intros. unfold toZ, ofZ. destruct (N.testbit _ _).

    rewrite <- Zminus_mod_idemp_r.
    rewrite Z.mod_same by apply N2Z_pow2_nonzero.
    rewrite Z.sub_0_r, <- N2Z.inj_mod, N2Z.id by (apply N.pow_nonzero; discriminate 1).
    apply N.mod_small. assumption.

    rewrite Z.mod_small. apply N2Z.id. split.
      apply N2Z.is_nonneg.
      apply N2Z.inj_lt. assumption.
Qed.

Corollary toZ_inj:
  forall w n1 n2 (LT1: n1 < 2^w) (LT2: n2 < 2^w),
    toZ w n1 = toZ w n2 -> n1 = n2.
Proof.
  intros.
  rewrite <- (ofZ_toZ n1 w), <- (ofZ_toZ n2 w), H by assumption.
  reflexivity.
Qed.

Theorem ofZ_inj:
  forall z1 z2 w (SR1: signed_range w z1) (SR2: signed_range w z2),
    ofZ w z1 = ofZ w z2 -> z1 = z2.
Proof.
  match goal with |- forall z1 z2, ?P => cut (forall z1 z2 (LE: z2 <= z1), P)%Z end.
    intros. destruct (Z.le_gt_cases z2 z1); [|symmetry]; eapply H; try eassumption.
    apply Z.lt_le_incl. assumption. symmetry. assumption.

  unfold ofZ. intros.
  apply Zminus_eq. rewrite <- (Z.mod_small (_-_) (Z.of_N (2^w))). rewrite Zminus_mod.
  apply Z2N.inj in H; try (apply Z.mod_pos_bound; change Z0 with (Z.of_N 0);
    apply N2Z.inj_lt, N.neq_0_lt_0, N.pow_nonzero; discriminate 1).
  apply Zeq_minus in H. rewrite H. reflexivity.

  split. apply Zle_minus_le_0, LE.
  destruct w as [|w]. rewrite SR1,SR2. reflexivity.
  rewrite <- (N.succ_pred (Npos w)) by discriminate 1. rewrite N.pow_succ_r', N2Z.inj_mul.
  change (Z.of_N 2) with (1+1)%Z. rewrite Z.mul_add_distr_r, Z.mul_1_l, <- Z.sub_opp_r.
  apply Z.sub_lt_le_mono. apply SR1. apply SR2.
Qed.

Theorem toZ_ofZ:
  forall z w (SR: signed_range w z), toZ w (ofZ w z) = z.
Proof.
  intros. eapply ofZ_inj; try eassumption.
    apply toZ_bounds, ofZ_bound.
    apply ofZ_toZ, ofZ_bound.
Qed.

Lemma ofZ_eqm:
  forall z1 z2 w, eqm (Z.of_N (2^w)) z1 z2 <-> ofZ w z1 = ofZ w z2.
Proof.
  unfold ofZ. split; intro.
    rewrite H. reflexivity.
    apply Z2N.inj; solve [ apply H | apply Z.mod_pos_bound, N2Z_pow2_pos ].
Qed.

Lemma toZ_Neqm:
  forall n1 n2 w, toZ w n1 = toZ w n2 -> n1 mod 2^w = n2 mod 2^w.
Proof.
  unfold toZ. intros.
  apply N2Z.inj. rewrite !N2Z.inj_mod by (apply N.pow_nonzero; discriminate 1).
  apply (f_equal (fun z => Z.modulo z (Z.of_N (2^w)))) in H. repeat destruct (N.testbit _ _);
    repeat rewrite Zminus_mod, Z.mod_same, Z.sub_0_r, Z.mod_mod in H by apply N2Z_pow2_nonzero;
    rewrite H; reflexivity.
Qed.

Lemma eqm_toZ:
  forall w n z, eqm (Z.of_N (2^w)) (Z.of_N n) z -> eqm (Z.of_N (2^w)) (toZ w n) z.
Proof.
  intros. unfold eqm,toZ. destruct (N.testbit _ _);
  [ rewrite <- Zminus_mod_idemp_r, Z.mod_same, Z.sub_0_r by (
      rewrite N2Z.inj_pow; apply Z.pow_nonzero; [ discriminate 1 | apply N2Z.is_nonneg]) |];
  apply H.
Qed.

Lemma toZ_eqm:
  forall w n, eqm (Z.of_N (2^w)) (toZ w n) (Z.of_N n).
Proof.
  intros. unfold toZ. destruct (N.testbit _ _).
    unfold eqm. rewrite <- Zminus_mod_idemp_r, Z.mod_same, Z.sub_0_r by apply N2Z_pow2_nonzero. reflexivity.
    reflexivity.
Qed.

Theorem ofZ_add:
  forall w z1 z2, (ofZ w z1 + ofZ w z2) mod 2^w = ofZ w (z1 + z2).
Proof.
  intros. unfold ofZ.
  rewrite <- Z2N.inj_add by apply Z.mod_pos_bound, N2Z_pow2_pos.
  rewrite <- (N2Z.id (2^w)) at 3.
  rewrite <- Z2N.inj_mod by solve [ apply N2Z_pow2_pos | apply Z.add_nonneg_nonneg; apply Z.mod_pos_bound, N2Z_pow2_pos ].
  rewrite <- Z.add_mod by apply N2Z_pow2_nonzero.
  reflexivity.
Qed.

Theorem signed_sub:
  forall w n1 n2, n2 < 2^w -> (2^w + n1 - n2) mod 2^w = sbop Z.sub w n1 n2.
Proof.
  intros. unfold sbop.
  rewrite <- (ofZ_toZ (_ mod _) w) by (apply N.mod_upper_bound, N.pow_nonzero; discriminate 1).
  apply ofZ_eqm, eqm_toZ.
  rewrite N2Z.inj_mod by (apply N.pow_nonzero; discriminate 1).
  unfold eqm. rewrite Z.mod_mod by apply N2Z_pow2_nonzero.
  rewrite N2Z.inj_sub, N2Z.inj_add by (eapply N.lt_le_incl, N.lt_le_trans; [ exact H | apply N.le_add_r ]).
  rewrite <- Z.add_sub_assoc, <- Zplus_mod_idemp_l, Z.mod_same, Z.add_0_l by apply N2Z_pow2_nonzero.
  apply Zminus_eqm; apply eqm_sym, toZ_eqm.
Qed.

Theorem signed_neg:
  forall w n, n < 2^w -> (2^w - n) mod 2^w = ofZ w (- toZ w n).
Proof.
  intros. rewrite <- (N.add_0_r (2^w)) at 1. rewrite <- Z.sub_0_l. apply signed_sub. assumption.
Qed.

Theorem ofZ_mul:
  forall w z1 z2, (ofZ w z1 * ofZ w z2) mod 2^w = ofZ w (z1 * z2).
Proof.
  intros. unfold ofZ.
  rewrite <- Z2N.inj_mul by apply Z.mod_pos_bound, N2Z_pow2_pos.
  rewrite <- (N2Z.id (2^w)) at 3.
  rewrite <- Z2N.inj_mod by solve [ apply N2Z_pow2_pos | apply Z.mul_nonneg_nonneg; apply Z.mod_pos_bound, N2Z_pow2_pos ].
  rewrite <- Z.mul_mod by apply N2Z_pow2_nonzero.
  reflexivity.
Qed.

Theorem ofZ_mod_pow2:
  forall w z n, (ofZ w z) mod 2^n = ofZ w (z mod Z.of_N (2^n)).
Proof.
  intros. rewrite <- (N2Z.id (2^n)) at 1. unfold ofZ. rewrite <- Z2N.inj_mod.
    rewrite !N2Z.inj_pow, <- !Z.land_ones, <- !Z.land_assoc, (Z.land_comm (Z.ones _)) by apply N2Z.is_nonneg. reflexivity.
    apply Z.mod_pos_bound, N2Z_pow2_pos.
    apply N2Z_pow2_pos.
Qed.

Theorem ofZ_shiftl:
  forall w z n,
  (N.shiftl (ofZ w z) n) mod 2^w = ofZ w (Z.shiftl z (Z.of_N n)).
Proof.
  intros. unfold ofZ.
  rewrite N.shiftl_mul_pow2, Z.shiftl_mul_pow2 by apply N2Z.is_nonneg.
  rewrite <- (N2Z.id (2^n)), <- Z2N.inj_mul.
    rewrite <- (N2Z.id (2^w)) at 2. rewrite <- Z2N.inj_mod.
      rewrite Z.mul_mod_idemp_l, N2Z.inj_pow by apply N2Z_pow2_nonzero. reflexivity.
      apply Z.mul_nonneg_nonneg.
        apply Z.mod_pos_bound, N2Z_pow2_pos.
        apply Z.lt_le_incl, N2Z_pow2_pos.
      apply N2Z_pow2_pos.
    apply Z.mod_pos_bound, N2Z_pow2_pos.
    apply Z.lt_le_incl, N2Z_pow2_pos.
Qed.

Lemma testbit_ofZ:
  forall w z n, N.testbit (ofZ w z) n = andb (n <? w) (Z.testbit z (Z.of_N n)).
Proof.
  intros. destruct (N.lt_ge_cases n w).
    replace (n <? w) with true.
      unfold ofZ. rewrite <- Z.testbit_of_N. rewrite Z2N.id.
        rewrite N2Z.inj_pow. apply Z.mod_pow2_bits_low, N2Z.inj_lt, H.
        apply Z.mod_pos_bound, N2Z_pow2_pos.
      symmetry. apply N.ltb_lt. assumption.
    replace (n <? w) with false.
      eapply bound_hibits_zero. apply ofZ_bound. assumption.
      symmetry. apply N.ltb_ge. assumption.
Qed.

Theorem ofZ_land:
  forall w z1 z2, N.land (ofZ w z1) (ofZ w z2) = ofZ w (Z.land z1 z2).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.land_spec, !testbit_ofZ, Z.land_spec.
  destruct (_ <? _); destruct (Z.testbit _ _); destruct (Z.testbit _ _); reflexivity.
Qed.

Theorem ofZ_lor:
  forall w z1 z2, N.lor (ofZ w z1) (ofZ w z2) = ofZ w (Z.lor z1 z2).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.lor_spec, !testbit_ofZ, Z.lor_spec.
  destruct (_ <? _); destruct (Z.testbit _ _); destruct (Z.testbit _ _); reflexivity.
Qed.

Theorem ofZ_lxor:
  forall w z1 z2, N.lxor (ofZ w z1) (ofZ w z2) = ofZ w (Z.lxor z1 z2).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.lxor_spec, !testbit_ofZ, Z.lxor_spec.
  destruct (_ <? _); destruct (Z.testbit _ _); destruct (Z.testbit _ _); reflexivity.
Qed.

Theorem ofZ_lnot:
  forall w z, N.lnot (ofZ w z) w = ofZ w (Z.lnot z).
Proof.
  intros. apply N.bits_inj. intro b. destruct (N.lt_ge_cases b w).

    rewrite N.lnot_spec_low by assumption.
    rewrite !testbit_ofZ, Z.lnot_spec by apply N2Z.is_nonneg.
    apply N.ltb_lt in H. rewrite H. reflexivity.

    rewrite N.lnot_spec_high by assumption.
    rewrite !testbit_ofZ. apply N.ltb_ge in H. rewrite H. reflexivity.
Qed.

End TwosComplement.



Module Type PICINAE_THEORY (IL: PICINAE_IL).

Import IL.
Open Scope N.


Section StoreTheory.

(* The getmem/setmem memory accessors are defined as Peano recursions over N,
   rather than natural number recursions.  This is important for keeping proof
   terms small, but can make it more difficult to write inductive proofs.  To
   ease this burden, we here define machinery for inductively reasoning about
   getmem/setmem.

   Proofs that inductively expand getmem/setmem should typically perform the
   following steps:

   (1) Use Peano induction to induct over length argument:
         induction len using N.peano_ind.

   (2) Within the proof, unfold the base case (where len=0) using the getmem_0
       or setmem_0 theorems.

   (3) Unfold inductive cases (where len = N.succ _) using the getmem_succ
       or setmem_succ theorems. *)

(* Base cases for getmem/setmem *)
Theorem getmem_0: forall e m a, getmem e N0 m a = N0.
Proof. reflexivity. Qed.

Theorem setmem_0: forall e m a v, setmem e N0 m a v = m.
Proof. reflexivity. Qed.

(* Unfold getmem/setmem by one byte (for inductive cases of proofs). *)
Theorem getmem_succ:
  forall e len m a, getmem e (N.succ len) m a =
    match e with BigE => N.lor (getmem e len m (N.succ a)) (N.shiftl (m a) (Mb*len))
               | LittleE => N.lor (m a) (N.shiftl (getmem e len m (N.succ a)) Mb)
    end.
Proof.
  intros. unfold getmem.
  rewrite (N.recursion_succ (@eq (addr->N))).
  destruct e; reflexivity.
  reflexivity.
  intros x y H1 f g H2. rewrite H1,H2. reflexivity.
Qed.

Theorem setmem_succ:
  forall e len m a v, setmem e (N.succ len) m a v =
    match e with BigE => setmem e len (update m a (N.shiftr v (Mb*len))) (N.succ a) (v mod 2^(Mb*len))
               | LittleE => setmem e len (update m a match len with N0 => v | Npos _ => v mod 2^Mb end) (N.succ a) (N.shiftr v Mb)
    end.
Proof.
  intros. unfold setmem.
  rewrite (N.recursion_succ (@eq ((addr->N)->addr->N->(addr->N)))).
  destruct e; reflexivity.
  reflexivity.
  intros x y H1 f g H2. rewrite H1,H2. reflexivity.
Qed.

(* special cases for when getmem/setmem are applied to access a single memory byte *)
Corollary getmem_1: forall e m a, getmem e 1 m a = m a.
Proof.
  intros. change 1 with (N.succ 0).
  rewrite getmem_succ, getmem_0, N.mul_0_r, N.shiftl_0_r, N.lor_0_l, N.lor_0_r.
  destruct e; reflexivity.
Qed.

Corollary setmem_1: forall e, setmem e 1 = update.
Proof.
  intros. extensionality m. extensionality a. extensionality v.
  change 1 with (N.succ 0).
  rewrite setmem_succ, !setmem_0, N.mul_0_r, N.shiftr_0_r.
  destruct e; reflexivity.
Qed.

(* Break an (i+j)-byte number read/stored to/from memory into two numbers of size i and j. *)
Theorem getmem_split:
  forall e i j m a, getmem e (i+j) m a =
    match e with BigE => N.lor (getmem e j m (a+i)) (N.shiftl (getmem e i m a) (Mb*j))
               | LittleE => N.lor (getmem e i m a) (N.shiftl (getmem e j m (a+i)) (Mb*i))
    end.
Proof.
  induction i using N.peano_ind; intros.
    rewrite N.add_0_l, N.add_0_r, N.mul_0_r, getmem_0, N.shiftl_0_l, N.shiftl_0_r, N.lor_0_r, N.lor_0_l. destruct e; reflexivity.
    rewrite <- N.add_succ_comm, getmem_succ, N.add_succ_l. destruct e.
      rewrite N.shiftl_lor, N.shiftl_shiftl, N.lor_assoc, <- IHi, <- N.mul_add_distr_l. apply getmem_succ.
      rewrite (N.mul_succ_r _ i), <- N.shiftl_shiftl, <- N.lor_assoc, <- N.shiftl_lor, <- IHi. apply getmem_succ.
Qed.

Theorem setmem_split:
  forall e i j m a v, setmem e (i+j) m a v =
    match e with BigE => setmem e j (setmem e i m a (N.shiftr v (Mb*j))) (a+i) match i with N0 => v | Npos _ => v mod 2^(Mb*j) end
               | LittleE => setmem e j (setmem e i m a match j with N0 => v | Npos _ => v mod 2^(Mb*i) end) (a+i) (N.shiftr v (Mb*i))
    end.
Proof.
  induction i using N.peano_ind; intros.
    rewrite N.add_0_l, N.add_0_r, N.mul_0_r, N.shiftr_0_r, setmem_0, setmem_0. destruct e; reflexivity.
    rewrite <- N.add_succ_comm, !setmem_succ, N.add_succ_l. destruct e.

      rewrite <- (N.succ_pos_spec i), N.shiftr_shiftr, <- N.mul_add_distr_l, (N.add_comm j), setmem_succ, IHi.
      rewrite <- N.land_ones, <- N.land_ones, N.shiftr_land, (N.shiftr_div_pow2 (N.ones _)).
      rewrite N.ones_div_pow2 by (rewrite N.mul_add_distr_l, N.add_comm; apply N.le_add_r).
      rewrite N.mul_add_distr_l at 2. rewrite N.add_sub, N.land_ones, <- N.land_assoc, N.land_ones, N.land_ones.
      rewrite N.ones_mod_pow2 by (rewrite N.mul_add_distr_l, N.add_comm; apply N.le_add_r).
      rewrite N.land_ones. destruct i; reflexivity.

      rewrite setmem_succ, IHi. destruct j.
        rewrite N.add_0_r, setmem_0, setmem_0. reflexivity.
        destruct i.
          rewrite N.mul_0_r, N.add_0_l, setmem_0, setmem_0, N.mul_1_r, N.shiftr_0_r. reflexivity.
          destruct (N.pos _ + N.pos _) eqn:H.
            apply N.eq_add_0 in H. destruct H. discriminate H.

            rewrite N.shiftr_shiftr.
            rewrite <- (N.land_ones _ (_*N.succ _)), <- (N.land_ones (N.land _ _)), <- N.land_assoc.
            rewrite N.shiftr_land, (N.shiftr_div_pow2 (N.ones _)).
            rewrite N.land_ones.
            rewrite N.ones_mod_pow2, N.ones_div_pow2 by (rewrite N.mul_succ_r, N.add_comm; apply N.le_add_r).
            rewrite N.land_ones, N.land_ones, N.mul_succ_r, N.add_sub, (N.add_comm (_*_)).
            reflexivity.
Qed.

(* setmem doesn't modify addresses below a, or address at or above a+w. *)
Theorem setmem_frame_low:
  forall e len m a v a' (LT: a' < a),
  setmem e len m a v a' = m a'.
Proof.
  induction len using N.peano_ind; intros.
    rewrite setmem_0. reflexivity.
    rewrite setmem_succ. destruct e;
      rewrite IHlen by apply N.lt_lt_succ_r, LT; apply update_frame, N.lt_neq, LT.
Qed.

Theorem setmem_frame_high:
  forall e len m a v a' (LE: a + len <= a'),
  setmem e len m a v a' = m a'.
Proof.
  induction len using N.peano_ind; intros.
    rewrite setmem_0. reflexivity.

    assert (LT: a < a'). eapply N.lt_le_trans; [|exact LE]. apply N.lt_add_pos_r, N.lt_0_succ.
    rewrite setmem_succ. destruct e; (rewrite IHlen;
    [ apply update_frame, not_eq_sym, N.lt_neq, LT
    | rewrite N.add_succ_l; apply N.le_succ_l; (eapply N.lt_le_trans; [|exact LE]); apply N.add_lt_mono_l, N.lt_succ_diag_r ]).
Qed.

(* getmem inverts setmem *)
Lemma recompose_bytes:
  forall w v, N.lor (v mod 2^w) (N.shiftl (N.shiftr v w) w) = v.
Proof.
  intros.
  rewrite <- N.ldiff_ones_r, <- N.land_ones, N.lor_comm.
  apply N.lor_ldiff_and.
Qed.

Theorem getmem_setmem:
  forall e len m a v,
  getmem e len (setmem e len m a v) a = match len with N0 => N0 | Npos _ => v end.
Proof.
  induction len using N.peano_ind; intros.
    apply getmem_0.
    rewrite <- N.succ_pos_spec at 3. rewrite getmem_succ, setmem_succ. destruct e; rewrite IHlen; destruct len.
      rewrite N.lor_0_l, N.mul_0_r, setmem_0, N.shiftl_0_r, N.shiftr_0_r. apply update_updated.
      rewrite setmem_frame_low by apply N.lt_succ_diag_r. rewrite update_updated. apply recompose_bytes.
      rewrite setmem_0, N.shiftl_0_l, N.lor_0_r. apply update_updated.
      rewrite setmem_frame_low by apply N.lt_succ_diag_r. rewrite update_updated. apply recompose_bytes.
Qed.

End StoreTheory.



Section Determinism.

(* The semantics of eval_exp, exec_stmt, and exec_prog are deterministic
   as long as there are no Unknown expressions. *)

Theorem eval_exp_deterministic:
  forall {h e s v1 v2} (NU: forall_exps_in_exp not_unknown e)
         (E1: eval_exp h s e v1) (E2: eval_exp h s e v2), v1=v2.
Proof.
  induction e; intros; inversion E1; inversion E2; clear E1 E2; subst;
  simpl in NU; repeat match type of NU with _ /\ _ => let H := fresh NU in destruct NU as [H NU] end;
  try (remember (match n0 with N0 => e3 | _ => e2 end) as e);
  repeat match goal with [ IH: forall _ _ _, _ -> eval_exp ?h _ ?e _ -> eval_exp ?h _ ?e _ -> _=_,
                           H0: exps_in_exp and not_unknown ?e,
                           H1: eval_exp ?h ?s ?e ?v1,
                           H2: eval_exp ?h ?s ?e ?v2 |- _ ] =>
           specialize (IH s v1 v2 H0 H1 H2); clear H0 H1 H2;
           try (injection IH; clear IH; intros); subst;
           try match type of E' with
             eval_exp _ _ (match ?N with N0 => _ | _ => _ end) _ => destruct N
           end
         end;
  try reflexivity.

  rewrite SV in SV0. injection SV0. intro. assumption.
  exfalso. assumption.
Qed.

Theorem exec_stmt_deterministic:
  forall {h s q d s1 x1 s2 x2} (NU: forall_exps_in_stmt not_unknown q)
         (X1: exec_stmt h s q d s1 x1) (X2: exec_stmt h s q d s2 x2),
  s1 = s2 /\ x1 = x2.
Proof.
  intros. revert s2 x2 X2.
  dependent induction X1; intros; inversion X2; subst;
  try solve [ split;reflexivity ];
  try destruct NU as [NU1 NU2].

  replace u0 with u.
    split; reflexivity.
    apply (eval_exp_deterministic NU E E0).

  assert (H:=eval_exp_deterministic NU E E0).
  injection H. intros. subst. split; reflexivity.

  apply IHX1; assumption.

  apply (IHX1 NU1) in XS1. destruct XS1. discriminate.

  apply (IHX1_1 NU1) in XS. destruct XS. discriminate.

  apply (IHX1_1 NU1),proj1 in XS1. subst. apply (IHX1_2 NU2) in XS0. assumption.

  apply IHX1; repeat first [ assumption | split ].

  apply IHX1.
    destruct NU2. destruct c; assumption.
    assert (H:=eval_exp_deterministic NU1 E E0). injection H; intros; subst. assumption.
Qed.

Theorem exec_prog_deterministic:
  forall {p a h s d n s1 x1 s2 x2} (NU: forall_exps_in_prog not_unknown p)
  (XP1: exec_prog h p a s d n s1 x1) (XP2: exec_prog h p a s d n s2 x2),
  s1 = s2 /\ x1 = x2.
Proof.
  intros. revert s2 x2 XP2. dependent induction XP1; intros; inversion XP2; subst;
  assert (NUa:=NU a);
  try (rewrite LU0 in LU; first [ discriminate LU
                                | injection LU; clear LU; intros; subst; rewrite LU0 in NUa ]);
  try solve [ split;reflexivity ];
  assert (ESD:=exec_stmt_deterministic (NUa _ _ (eq_refl _)) XS XS0);
  destruct ESD as [ESD1 ESD2]; try (injection ESD2; clear ESD2; intro); subst.

  replace a'0 with a' in XP.
    apply IHXP1. assumption.
    destruct x0 as [x0|]; [destruct x0|]; first
    [ discriminate
    | injection EX; injection EX0; intros; subst; subst; reflexivity ].

  destruct x2; discriminate.

  destruct x; discriminate.

  split; reflexivity.
Qed.

End Determinism.


Section Monotonicity.

(* Some monotonicity properties: *)

(* exec_stmt and exec_prog are monotonic with respect to their input and output
   stores (i.e., there is no "delete variable" operation). *)

Theorem exec_stmt_nodelete:
  forall {h s q d s' x} (XS: exec_stmt h s q d s' x) v (V': s' v = None),
  s v = None.
Proof.
  intros. dependent induction XS; try apply IHXS; try assumption.
  unfold update in V'. destruct (v0 == v). discriminate. assumption.
  apply IHXS1, IHXS2. assumption.
Qed.

Theorem exec_prog_nodelete:
  forall {h p a s d n s' x} (XP: exec_prog h p a s d n s' x)
         v (V': s' v = None),
  s v = None.
Proof.
  intros. dependent induction XP; try assumption;
  apply (exec_stmt_nodelete XS); try apply IHXP; assumption.
Qed.

Theorem eval_exp_hmono:
  forall h1 h2 s e u (HS: h1 ⊆ h2) (E: eval_exp h1 s e u),
  eval_exp h2 s e u.
Proof.
  intros. revert s u HS E. induction e; intros;
  inversion E; clear E; subst;
  repeat match goal with [ IH: forall _ _, _ -> eval_exp _ _ ?e _ -> eval_exp _ _ ?e _,
                           H: eval_exp _ _ ?e _ |- _ ] =>
    eapply IH in H; [|exact HS]
  end;
  econstructor; try eassumption.

  intros. split; [apply HS|]; apply R; assumption.

  intros. split; [apply HS|]; apply W; assumption.

  destruct n1.
    eapply IHe3; eassumption.
    eapply IHe2; eassumption.
Qed.

Theorem eval_exp_smono:
  forall s1 s2 h e u (SS: s1 ⊆ s2) (E: eval_exp h s1 e u),
  eval_exp h s2 e u.
Proof.
  intros until e. revert s1 s2. induction e; intros;
  inversion E; clear E; subst;
  repeat match goal with [ IH: forall _ _ _, _ -> eval_exp ?h _ ?e _ -> eval_exp ?h _ ?e _,
                           H: eval_exp ?h _ ?e _ |- _ ] =>
    eapply IH in H; [|exact SS]
  end;
  econstructor; try eassumption.

  apply SS. assumption.

  intros. split.
    apply R. assumption.
    eapply mem_readable_mono. exact SS. apply R. assumption.

  intros. split.
    apply W. assumption.
    eapply mem_writable_mono. exact SS. apply W. assumption.

  eapply IHe2; [|eassumption].
  intros x y. unfold update. intro. destruct (x == v). assumption.
  apply SS. assumption.

  destruct n1.
    eapply IHe3; eassumption.
    eapply IHe2; eassumption.
Qed.

Theorem exec_stmt_hmono:
  forall h1 h2 s q d s' x (HS: h1 ⊆ h2)
         (XS: exec_stmt h1 s q d s' x),
  exec_stmt h2 s q d s' x.
Proof.
  intros. dependent induction XS; econstructor;
    try eapply eval_exp_hmono; eassumption.
Qed.

Theorem exec_stmt_smono:
  forall s1 s2 h q d s1' x (SS: s1 ⊆ s2) (XS: exec_stmt h s1 q d s1' x),
  exec_stmt h s2 q d (updateall s2 s1') x.
Proof.
  intros. revert s2 SS. dependent induction XS; intros;
  try (rewrite updateall_subset; [ try constructor | assumption ]).

  replace (updateall s2 (s[v:=Some u])) with (s2[v:=Some u]).
    apply XMove. eapply eval_exp_smono; eassumption.
    extensionality x. unfold update, updateall. destruct (x == v).
      reflexivity.
      unfold pfsub in SS. specialize SS with (x:=x). destruct (s x).
        apply SS. reflexivity.
        reflexivity.

  apply XJmp with (w:=w). eapply eval_exp_smono; eassumption.

  apply XSeq1. apply IHXS. assumption.

  apply XSeq2 with (s2:=updateall s0 s2).
    apply IHXS1. assumption.
    replace (updateall s0 s') with (updateall (updateall s0 s2) s').
      apply IHXS2. apply subset_updateall.
      extensionality z. unfold updateall. assert (H:=exec_stmt_nodelete XS2 z). destruct (s' z).
        reflexivity.
        rewrite H. reflexivity. reflexivity.

  apply XWhile. apply IHXS. assumption.

  apply XIf with (c:=c). eapply eval_exp_smono; eassumption. apply IHXS. assumption.
Qed.

Theorem exec_prog_hmono:
  forall h1 h2 p s a d n s' x (HS: h1 ⊆ h2)
         (XP: exec_prog h1 p a s d n s' x),
  exec_prog h2 p a s d n s' x.
Proof.
  intros. revert s a XP. induction n; intros; inversion XP; clear XP; subst.
    apply XDone.
    eapply XStep; try apply PS; try eassumption.
      eapply exec_stmt_hmono; eassumption.
      apply IHn. assumption.
    eapply XAbort; try apply PS; try eassumption.
      eapply exec_stmt_hmono; eassumption.
Qed.

Theorem exec_prog_smono:
  forall p s1 s2 h a d n s1' x (SS: s1 ⊆ s2)
         (XP: exec_prog h p a s1 d n s1' x),
  exec_prog h p a s2 d n (updateall s2 s1') x.
Proof.
  intros. revert s2 SS. dependent induction XP; intros.

  replace (updateall s2 s) with s2.
    constructor.
    symmetry. apply updateall_subset. assumption.

  apply XStep with (sz:=sz) (q:=q) (s2:=updateall s0 s2) (x1:=x1) (a':=a').
    assumption.
    eapply exec_stmt_smono; eassumption.
    assumption.
    replace (updateall s0 s') with (updateall (updateall s0 s2) s').
      apply IHXP. apply subset_updateall.
      extensionality z. unfold updateall. assert (H:=exec_prog_nodelete XP z). destruct (s' z).
        reflexivity.
        rewrite H. reflexivity. reflexivity.

  apply XAbort with (sz:=sz) (q:=q).
    assumption.
    eapply exec_stmt_smono; eassumption.
    assumption.
Qed.

Theorem exec_prog_pmono:
  forall p1 p2 s h a d n s' x (PS: p1 ⊆ p2)
         (XP: exec_prog h p1 a s d n s' x),
  exec_prog h p2 a s d n s' x.
Proof.
  intros. dependent induction XP; econstructor; try apply PS; eassumption.
Qed.

End Monotonicity.


Section Boundedness.

(* If there are no while-loops, we can compute a necessary and sufficient recursion depth
   bound to avoid an Unfinished condition for execution of any statement. *)

Theorem depth_bound_pos:
  forall q d (SB: depth_bound q = Some d), (0<d)%nat.
Proof.
  induction q; intros;
  simpl in SB; try (injection SB; clear SB; intro; subst d);
  try solve [ exact Nat.lt_0_1 | discriminate ];
  destruct (depth_bound q1); destruct (depth_bound q2); try discriminate;
  injection SB; clear SB; intro; subst;
  apply Nat.lt_0_succ.
Qed.

Theorem stmt_finish:
  forall h s q d d' s' x
         (SB: depth_bound q = Some d) (LT: (d <= d')%nat)
         (XS: exec_stmt h s q d' s' x),
  x <> Some Unfinished.
Proof.
  intros.
  revert d SB LT. dependent induction XS; intros; try discriminate.

  exfalso. apply le_not_lt in LT. apply LT. revert SB. apply depth_bound_pos.

  3: destruct c.
  all: simpl in SB; destruct (depth_bound q1) as [d1|]; destruct (depth_bound q2) as [d2|]; try discriminate.
  all: injection SB; clear SB; intro; subst.
  2: rename IHXS2 into IHXS.
  all: eapply IHXS; [reflexivity|].
  all: transitivity (max d1 d2); [ first [ apply Max.le_max_l | apply Max.le_max_r ]
                                 | apply le_S_n; assumption ].
Qed.

(* A stmt that finishes within n steps will also finish within (S n) steps. *)
Theorem exec_stmt_incbound:
  forall h d s q s' x (FIN: x <> Some Unfinished) (XS: exec_stmt h s q d s' x),
  exec_stmt h s q (S d) s' x.
Proof.
  induction d; intros; inversion XS; clear XS; subst.
    contradict FIN. reflexivity.
    apply XNop.
    apply XMove. exact E.
    eapply XJmp. exact E.
    apply XExn.
    apply XSeq1. apply IHd. exact FIN. exact XS0.
    eapply XSeq2.
      apply IHd. discriminate 1. exact XS1.
      apply IHd. exact FIN. exact XS0.
    apply XWhile. apply IHd. exact FIN. exact XS0.
    eapply XIf. exact E. apply IHd. exact FIN. exact XS0.
Qed.

Corollary exec_stmt_raisebound:
  forall h d' d s q s' x (LE: (d <= d')%nat) (FIN: x <> Some Unfinished) (XS: exec_stmt h s q d s' x),
  exec_stmt h s q d' s' x.
Proof.
  intros. pattern d'. revert d' LE. apply le_ind.
    exact XS.
    intros. apply exec_stmt_incbound. exact FIN. assumption.
Qed.

End Boundedness.


Section InvariantProofs.

(* To prove properties of while-loops, it suffices to prove that each loop iteration
   preserves the property.  This is equivalent to stepping the loop three small-steps
   at a time (to unfold the While->If->Seq expansion of the loop). *)
Theorem while_inv:
  forall (P: store -> Prop)
         h s e q d s' x (XS: exec_stmt h s (While e q) d s' x) (PRE: P s)
         (INV: forall s c d s' x (PRE: P s)
                      (EX: eval_exp h s e (VaN (Npos c) 1))
                      (XS: exec_stmt h s q d s' x), P s'),
  P s'.
Proof.
  intros. revert s s' x XS PRE.
  rewrite (Nat.div_mod d 3); [|discriminate].
  induction (Nat.div d 3) as [|m'].

  simpl. destruct (snd _); intros.
    inversion XS; inversion XS0; inversion XS1; subst. exact PRE.
    destruct y.
      inversion XS; inversion XS0; subst. exact PRE.
      inversion XS; subst. exact PRE.

  rewrite Nat.mul_succ_r. rewrite (plus_comm _ 3). rewrite <- plus_assoc. intros.
  inversion XS; inversion XS0; subst. destruct c; inversion XS1; subst.
    exact PRE.
    eapply INV. exact PRE. exact E. exact XS2.
    eapply IHm'.
      exact XS3.
      eapply INV. exact PRE. exact E. exact XS2.
Qed.

(* Append a step to an exec_prog computation. *)
Theorem exec_prog_append:
  forall h p n a s d sz q s2 a1 s' x'
         (XP: exec_prog h p a s d n s2 (Exit a1))
         (LU: p a1 = Some (sz,q))
         (XS: exec_stmt h s2 q d s' x'),
    exec_prog h p a s d (S n) s' (match x' with None => Exit (a1+sz)
                                              | Some x' => x' end).
Proof.
  induction n; intros; inversion XP; subst.
    destruct x'; [destruct e|]; econstructor; solve [ eassumption | reflexivity | apply XDone ].
    eapply XStep; try eassumption. eapply IHn; eassumption.
    discriminate.
Qed.

(* Split an exec_prog computation into two parts. *)
Theorem exec_prog_split:
  forall h p a s d n1 n2 s' x'
         (XP: exec_prog h p a s d (n1 + S n2)%nat s' x'),
  exists s1 a1, exec_prog h p a s d n1 s1 (Exit a1) /\ exec_prog h p a1 s1 d (S n2) s' x'.
Proof.
  intros. revert n2 XP. induction n1; intros.
    exists s,a. split. apply XDone. exact XP.
    rewrite Nat.add_succ_comm in XP. destruct (IHn1 _ XP) as [s1 [a1 [XP1 XP2]]]. inversion XP2; subst. exists s2,a'. split.
      eapply exec_prog_append in XP1; [|exact LU | exact XS]. destruct x1 as [e|]; [destruct e|].
        discriminate EX.
        injection EX as; subst. exact XP1.
        discriminate EX.
        injection EX as; subst. exact XP1.
      assumption.
Qed.

(* Concatenate two exec_prog comptations into one whole. *)
Theorem exec_prog_concat:
  forall h p a s d n1 n2 s1 a1 s' x'
         (XP1: exec_prog h p a s d n1 s1 (Exit a1)) (XP2: exec_prog h p a1 s1 d (S n2) s' x'),
  exec_prog h p a s d (n1 + S n2)%nat s' x'.
Proof.
  intros. revert n2 s1 a1 XP1 XP2. induction n1; intros.
    inversion XP1; subst. exact XP2.
    rewrite <- Nat.add_1_r in XP1. apply exec_prog_split in XP1. destruct XP1 as [s2 [a2 [XP0 XP1]]]. rewrite Nat.add_succ_comm. eapply IHn1.
     exact XP0.
     inversion XP1; subst.
       eapply XStep. exact LU. exact XS. exact EX. inversion XP; subst. exact XP2.
       discriminate EX.
Qed.

(* To prove that a property holds at the conclusion of a program's execution, it suffices
   to prove that the property is preserved by every statement in the program. *)
Theorem prog_inv_universal:
  forall (P: exit -> store -> Prop)
         h p a0 s0 d n s' x' (XP: exec_prog h p a0 s0 d n s' x') (PRE: P (Exit a0) s0)
         (INV: forall a1 s1 sz q s1' x1 (IL: p a1 = Some (sz,q)) (PRE: P (Exit a1) s1)
                      (XS: exec_stmt h s1 q d s1' x1),
               P (match x1 with None => Exit (a1 + sz)
                              | Some x => x end) s1'),
  P x' s'.
Proof.
  intros. revert a0 s0 XP PRE. induction n; intros; inversion XP; subst.
    exact PRE.
    apply (IHn a' s2).
      exact XP0.
      specialize (INV a0 s0 sz q s2 x1 LU PRE XS). destruct x1; [destruct e|]; first
      [ discriminate EX
      | injection EX; intro; subst a'; exact INV ].
    specialize (INV a0 s0 sz q s' (Some x') LU PRE XS). exact INV.
Qed.

(* Alternatively, one may prove that the property is preserved by all the reachable statements.
   (The user's invariant may adopt a precondition of False for unreachable statements.) *)
Theorem prog_inv_reachable:
  forall (P: exit -> store -> nat -> Prop)
         h p a0 s0 d n s' x' (XP: exec_prog h p a0 s0 d n s' x') (PRE: P (Exit a0) s0 O)
         (INV: forall a1 s1 n1 sz q s1' x1 (IL: p a1 = Some (sz,q)) (PRE: P (Exit a1) s1 n1) (LT: (n1 < n)%nat)
                      (XP: exec_prog h p a0 s0 d n1 s1 (Exit a1))
                      (XS: exec_stmt h s1 q d s1' x1)
                      (XP': match x1 with None => exec_prog h p (a1+sz) s1' d (n - S n1) s' x'
                                        | Some (Exit a2) => exec_prog h p a2 s1' d (n - S n1) s' x'
                                        | Some x2 => x'=x2 end),
               P (match x1 with None => Exit (a1 + sz)
                              | Some x => x end) s1' (S n1)),
  P x' s' n.
Proof.
  intros.
  assert (H: exists a1 s1 n2, (n2 <= n)%nat /\
               exec_prog h p a0 s0 d (n - n2) s1 (Exit a1) /\ P (Exit a1) s1 (n - n2)%nat /\
               exec_prog h p a1 s1 d n2 s' x').
    exists a0,s0,n. rewrite Nat.sub_diag. repeat split.
      apply le_n.
      apply XDone.
      exact PRE.
      exact XP.
  destruct H as [a1 [s1 [n2 [LE [XP1 [PRE1 XP2]]]]]].
  clear XP. revert a1 s1 LE PRE1 XP1 XP2. induction n2; intros.
    inversion XP2; clear XP2; subst. rewrite Nat.sub_0_r in PRE1. exact PRE1.
    inversion XP2; clear XP2; subst.
      apply (IHn2 a' s2).
        transitivity (S n2). apply le_S, le_n. assumption.

        specialize (INV a1 s1 (n - S n2)%nat sz q s2 x1 LU PRE1 (Nat.sub_lt n (S n2) LE (Nat.lt_0_succ n2)) XP1 XS).
        rewrite minus_Sn_m, Nat.sub_succ in INV by exact LE.
        replace (n - (n - n2))%nat with n2 in INV by (apply plus_minus; symmetry; apply Nat.sub_add, le_Sn_le, LE).
        destruct x1; [destruct e|].
          discriminate EX.
          injection EX. intro. subst a'. apply INV. exact XP.
          discriminate EX.
          injection EX. intro. subst a'. apply INV. exact XP.

        destruct n. inversion LE. apply le_S_n in LE. rewrite Nat.sub_succ_l; [|exact LE].
        replace (Exit a') with (match x1 with None => Exit (a1 + sz)
                                            | Some x => x end).
          eapply exec_prog_append. exact XP1. exact LU. exact XS.
          destruct x1; [destruct e|]; first [ discriminate EX | injection EX; intro; subst; reflexivity ].

        exact XP.
      specialize (INV a1 s1 (n-1)%nat sz q s' (Some x') LU PRE1 (Nat.sub_lt n 1 LE Nat.lt_0_1) XP1 XS).
      rewrite minus_Sn_m, Nat.sub_succ, Nat.sub_0_r in INV by exact LE.
      apply INV. destruct x'.
        reflexivity.
        discriminate EX.
        reflexivity.
Qed.

(* Rather than assigning and proving an invariant at every machine instruction, we can generalize
   the above to allow users to assign invariants to only a few machine instructions.  To prove that
   all the invariants are satisfied, the user can prove that any execution that starts in an
   invariant-satisfying state and that reaches another invariant always satisfies the latter. *)

(* The "next invariant satisfied" property is true if we're at an invariant point and the state
   satisfies that invariant, or we're not at an invariant point and (inductively) taking one
   exec_prog step leads to a "next invariant satisfied" state. *)
Inductive next_inv_sat (PS: exit -> store -> nat -> option Prop):
            bool -> exit -> hdomain -> program -> store -> nat -> nat -> nat -> store -> exit -> Prop :=
| NISHere x h p s d n n' s' x' (TRU: match PS x s n with None => False | Some P => P end):
    next_inv_sat PS true x h p s d n n' s' x'
| NISStep h p s d n n' s' x' a
          (STEP: forall sz q s1 x1 (LT: (n < n')%nat)
                        (IL: p a = Some (sz,q)) (XS: exec_stmt h s q d s1 x1)
                        (XP': match x1 with None => exec_prog h p (a+sz) s1 d (n' - S n) s' x'
                              | Some (Exit a2) => exec_prog h p a2 s1 d (n' - S n) s' x'
                              | Some x2 => x'=x2 end),
                 next_inv_sat PS (match PS match x1 with None => Exit (a+sz) | Some x1 => x1 end s1 (S n) with
                                  | Some _ => true | None => false end)
                              match x1 with None => Exit (a+sz) | Some x1 => x1 end
                              h p s1 d (S n) n' s' x'):
    next_inv_sat PS false (Exit a) h p s d n n' s' x'.

(* Proving the "next invariant satisfied" property for all invariant points proves partial
   correctness of the program. *)
Theorem prog_inv:
  forall (PS: exit -> store -> nat -> option Prop) h p a0 s0 d n s' x'
         (XP: exec_prog h p a0 s0 d n s' x')
         (PRE: match PS (Exit a0) s0 O with Some P => P | None => False end)
         (INV: forall a1 s1 n1
                      (XP: exec_prog h p a0 s0 d n1 s1 (Exit a1))
                      (PRE: match PS (Exit a1) s1 n1 with Some P => P | None => False end),
               next_inv_sat PS false (Exit a1) h p s1 d n1 n s' x'),
  match PS x' s' n with Some P => P | None => True end.
Proof.
  intros.
  assert (NIS: next_inv_sat PS (match PS x' s' n with Some _ => true | None => false end) x' h p s' d n n s' x').
    pattern x' at -3, s' at -3, n at -3. eapply prog_inv_reachable.
      exact XP.
      destruct (PS (Exit a0) s0 O) eqn:PS0.
        apply NISHere. rewrite PS0. exact PRE.
        exfalso. exact PRE.
      intros. specialize (INV a1 s1 n1 XP0). destruct (PS (Exit a1) s1 n1) eqn:PS1.

        inversion PRE0; subst. rewrite PS1 in TRU. specialize (INV TRU).
        inversion INV; subst. eapply STEP. exact LT. exact IL. exact XS. exact XP'.

        inversion PRE0; subst. eapply STEP. exact LT. exact IL. exact XS. exact XP'.
  destruct (PS x' s' n) eqn:PS'.
    inversion NIS. rewrite PS' in TRU. exact TRU.
    exact I.
Qed.

End InvariantProofs.


Section FrameTheorems.

(* Statements and programs that contain no assignments to some IL variable v
   leave that variable unchanged in the output store. *)

Theorem novar_noassign v:
  forall q, forall_vars_in_stmt (fun v0 => v0 <> v) q -> noassign v q.
Proof.
  induction q; intro; constructor; try ((apply IHq1 + apply IHq2 + apply IHq); split); apply H.
Qed.

Theorem noassign_stmt_same:
  forall v h q (NA: noassign v q) d (s s':store) x,
  exec_stmt h s q d s' x -> s' v = s v.
Proof.
  induction q; intros; inversion H; subst; try reflexivity.
    inversion NA; subst. apply update_frame, not_eq_sym. assumption.
    eapply IHq1; try eassumption. inversion NA. assumption.
    inversion NA. transitivity (s2 v); [ eapply IHq2 | eapply IHq1 ]; eassumption.

    pattern s'. eapply while_inv.
      eassumption.
      reflexivity.
      intros. rewrite <- PRE. eapply IHq. inversion NA. assumption. eassumption.

    inversion NA. destruct c; [ eapply IHq2 | eapply IHq1 ]; eassumption.
Qed.

Theorem noassign_prog_same:
  forall v h p (NA: prog_noassign v p) d s' x
         n a s (EP: exec_prog h p a s d n s' x),
  s' v = s v.
Proof.
  intros. pattern x, s'. eapply prog_inv_universal.
    exact EP.
    reflexivity.
    intros. rewrite <- PRE. apply (noassign_stmt_same v) in XS.
      exact XS.
      specialize (NA a1). rewrite IL in NA. exact NA.
Qed.

End FrameTheorems.

Ltac prove_noassign :=
  try lazymatch goal with [ |- prog_noassign _ _ ] => let a := fresh "a" in
    let a := fresh "a" in intro a; destruct a as [|a];
    repeat first [ exact I | destruct a as [a|a|] ]
  end;
  repeat lazymatch goal with [ |- _ <> _ ] => discriminate 1
                           | _ => constructor; let g:=numgoals in guard g<=2 end.

End PICINAE_THEORY.


Module PicinaeTheory (IL: PICINAE_IL) <: PICINAE_THEORY IL.
  Include PICINAE_THEORY IL.
End PicinaeTheory.

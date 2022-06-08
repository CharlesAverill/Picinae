 (* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2021 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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



(* Define some tactics for reasoning about IL variable identifier equalities
   of the form "v1 == v2", which asserts that v1 and v2 are the same IL var. *)

(* Tactic "vreflexivity v" reduces "v==v" to true (actually "left _"). *)
Theorem iseq_refl {A} {_:EqDec A}:
  forall (x:A), exists (H: x = x), (x == x) = left H.
Proof.
  intro. destruct (x == x).
    eexists. reflexivity.
    contradict n. reflexivity.
Qed.

Ltac vreflexivity v :=
  let H := fresh in
  let t Hveq :=
    destruct (iseq_refl v) as [Hveq H];
    rewrite H in *;
    clear H; try clear Hveq
  in first [ let Hveq := fresh "H" v "eq" in t Hveq
           | let Hveq := fresh "Heq" in t Hveq ].

(* Tactic "vantisym v1 v2" reduces "v1==v2" to false (actually "right _")
   and introduces a subgoal of "v1<>v2". *)
Theorem iseq_antisym {A} {_:EqDec A}:
  forall (x y:A), x<>y -> exists (H: x<>y), (x == y) = right H.
Proof.
  intros. destruct (x == y).
    contradict H. assumption.
    eexists. reflexivity.
Qed.

Tactic Notation "vantisym" constr(v1) constr(v2) :=
  let H1 := fresh in let H2 := fresh in
  let t Hneq :=
    enough (H1: v1 <> v2);
    [ destruct (iseq_antisym v1 v2 H1) as [Hneq H2];
      rewrite H2 in *;
      clear H1 H2; try clear Hneq |]
  in first [ let Hneq := fresh "H" v1 "neq" in t Hneq
           | let Hneq := fresh "Hneq" in t Hneq ].

Tactic Notation "vantisym" constr(v1) constr(v2) "by" tactic(T) :=
  vantisym v1 v2; [|solve T].


(* Define the partial order of A-to-B partial functions ordered by subset. *)

Definition pfsub {A B:Type} (f g: A -> option B) : Prop :=
  forall x y, f x = Some y -> g x = Some y.

Notation "f ⊆ g" := (pfsub f g) (at level 70, right associativity).

Theorem pfsub_refl {A B}: forall (f:A->option B), f ⊆ f.
Proof. unfold pfsub. intros. assumption. Qed.

Theorem pfsub_antisym {A B}:
  forall (f g:A->option B), f ⊆ g -> g ⊆ f -> f = g.
Proof.
  unfold pfsub. intros f g FG GF. extensionality v.
  specialize (FG v). specialize (GF v). destruct (f v) as [b|].
    symmetry. apply FG. reflexivity.
    destruct (g v). apply GF. reflexivity. reflexivity.
Qed.

Theorem pfsub_trans {A B}:
  forall (f g h:A->option B), f ⊆ g -> g ⊆ h -> f ⊆ h.
Proof. unfold pfsub. intros f g h FG GH x y FX. apply GH,FG. assumption. Qed.

Theorem pfsub_contrapos {A B}:
  forall (f g: A -> option B) x, f ⊆ g -> g x = None -> f x = None.
Proof.
  unfold pfsub. intros f g x SS H. specialize (SS x). destruct (f x).
    symmetry. rewrite <- H. apply SS. reflexivity.
    reflexivity.
Qed.

Add Parametric Relation {A B:Type}: (A -> option B) pfsub
  reflexivity proved by pfsub_refl
  transitivity proved by pfsub_trans
as pfsubset.

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
  forall (s: A -> B) v u (SV: s v = u),
  s = update s v u.
Proof.
  intros.
  extensionality v0.
  destruct (v0 == v).
    subst v0. rewrite update_updated. exact SV.
    rewrite update_frame. reflexivity. assumption.
Qed.



(* Theory of bit-extraction. *)
Section XBits.

Lemma N_ones_spec_ltb:
  forall m n, N.testbit (N.ones m) n = (n <? m).
Proof.
  intros. destruct (_ <? _) eqn:H.
    apply N.ones_spec_low, N.ltb_lt, H.
    apply N.ones_spec_high, N.ltb_ge, H.
Qed.

Theorem xbits_spec:
  forall n i j b, N.testbit (xbits n i j) b = andb (N.testbit n (b + i)) (b + i <? j).
Proof.
  intros. unfold xbits.
  rewrite <- N.land_ones, N.land_spec, N.shiftr_spec', N_ones_spec_ltb.
  apply f_equal. destruct (b + i <? j) eqn:H.
    apply N.ltb_lt, N.lt_add_lt_sub_r, N.ltb_lt, H.
    apply N.ltb_ge, N.le_sub_le_add_r, N.ltb_ge, H.
Qed.

Theorem xbits_equiv:
  forall n i j, xbits n i j = N.shiftr (n mod 2^j) i.
Proof.
  intros. rewrite <- N.land_ones. apply N.bits_inj. intro b.
  rewrite xbits_spec, N.shiftr_spec', N.land_spec, N_ones_spec_ltb.
  reflexivity.
Qed.

Theorem xbits_0_l:
  forall i j, xbits 0 i j = 0.
Proof.
  intros. unfold xbits. rewrite N.shiftr_0_l. reflexivity.
Qed.

Theorem xbits_0_i:
  forall n j, xbits n 0 j = n mod 2^j.
Proof.
  intros. unfold xbits. rewrite N.sub_0_r, N.shiftr_0_r. reflexivity.
Qed.

Theorem xbits_0_j:
  forall n i, xbits n i 0 = 0.
Proof.
  intros. unfold xbits. rewrite N.sub_0_l. apply N.mod_1_r.
Qed.

Lemma xbits_none:
  forall n i j, j <= i -> xbits n i j = 0.
Proof.
  intros. unfold xbits. rewrite (proj2 (N.sub_0_le _ _) H). apply N.mod_1_r.
Qed.

Theorem xbits_high:
  forall w w' n, n < 2^w -> xbits n (w - w') w = N.shiftr n (w - w').
Proof.
  intros. unfold xbits. apply N.mod_small, (N.mul_lt_mono_pos_r (2^(w-w'))).
    apply N.neq_0_lt_0, N.pow_nonzero. discriminate 1.
    rewrite <- N.pow_add_r, N.sub_add by apply N.le_sub_l. eapply N.le_lt_trans.
      rewrite N.shiftr_div_pow2, N.mul_comm. apply N.mul_div_le, N.pow_nonzero. discriminate 1.
      exact H.
Qed.

Corollary cast_low_xbits:
  forall w w' n, cast CAST_LOW w w' n = xbits n 0 w'.
Proof. symmetry. apply xbits_0_i. Qed.

Corollary cast_high_xbits:
  forall w w' n, n < 2^w -> cast CAST_HIGH w w' n = xbits n (w - w') w.
Proof. symmetry. apply xbits_high, H. Qed.

Theorem xbits_bound:
  forall n i j, xbits n i j < 2^(j-i).
Proof.
  intros. unfold xbits. apply N.mod_lt, N.pow_nonzero. discriminate 1.
Qed.

Theorem xbits_le:
  forall n i j, xbits n i j <= n / 2^i.
Proof.
  intros. rewrite xbits_equiv, N.shiftr_div_pow2. apply N.div_le_mono.
    apply N.pow_nonzero. discriminate 1.
    apply N.mod_le, N.pow_nonzero. discriminate 1.
Qed.

Theorem xbits_split:
  forall i j k n, i <= j -> j <= k -> xbits n i k = N.lor (xbits n i j) (N.shiftl (xbits n j k) (j - i)).
Proof.
  intros. unfold xbits. rewrite <- !N.land_ones.
  rewrite <- !N.ones_div_pow2, <- !N.shiftr_div_pow2 by repeat (eassumption + etransitivity).
  rewrite <- !N.shiftr_shiftl_l by assumption.
  rewrite <- !N.shiftr_land, <- N.shiftr_lor, <- N.ldiff_ones_r.
  replace (N.land n (N.ones j)) with (N.land (N.land n (N.ones k)) (N.ones j)).
    rewrite N.lor_comm, N.lor_ldiff_and. reflexivity.
    rewrite <- N.land_assoc. apply f_equal. rewrite N.land_comm, N.land_ones. apply N.mod_small, N.succ_lt_mono. rewrite N.ones_equiv, N.succ_pred.
      apply N.lt_succ_r, N.pow_le_mono_r. discriminate. assumption.
      apply N.pow_nonzero. discriminate.
Qed.

Theorem xbits_ones:
  forall n i j, xbits (N.ones n) i j = N.ones ((N.min n j) - i).
Proof.
  symmetry. apply N.bits_inj. intro b.
  rewrite xbits_spec, !N_ones_spec_ltb, <- N.sub_min_distr_r.
  destruct (b + i <? j) eqn:H1.
    destruct (b + i <? n) eqn:H2.
      apply N.ltb_lt, N.min_glb_lt; apply N.lt_add_lt_sub_r, N.ltb_lt; assumption.
      apply N.ltb_ge, N.min_le_iff. left. apply N.le_sub_le_add_r, N.ltb_ge, H2.
    rewrite Bool.andb_false_r. apply N.ltb_ge, N.min_le_iff. right. apply N.le_sub_le_add_r, N.ltb_ge, H1.
Qed.

Theorem xbits_land:
  forall n m i j, xbits (N.land n m) i j = N.land (xbits n i j) (xbits m i j).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.land_spec, !xbits_spec, N.land_spec.
  destruct (_ <? _), N.testbit, N.testbit; reflexivity.
Qed.

Theorem xbits_lor:
  forall n m i j, xbits (N.lor n m) i j = N.lor (xbits n i j) (xbits m i j).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.lor_spec, !xbits_spec, N.lor_spec.
  destruct (_ <? _), N.testbit, N.testbit; reflexivity.
Qed.

Theorem xbits_lxor:
  forall n m i j, xbits (N.lxor n m) i j = N.lxor (xbits n i j) (xbits m i j).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.lxor_spec, !xbits_spec, N.lxor_spec.
  destruct (_ <? _), N.testbit, N.testbit; reflexivity.
Qed.

Theorem xbits_ldiff:
  forall n m i j, xbits (N.ldiff n m) i j = N.ldiff (xbits n i j) (xbits m i j).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite N.ldiff_spec, !xbits_spec, N.ldiff_spec.
  destruct (_ <? _), N.testbit, N.testbit; reflexivity.
Qed.

Theorem xbits_lnot:
  forall a n i j, xbits (N.lnot a n) i j = N.lnot (xbits a i j) (N.min n j - i).
Proof.
  intros. unfold N.lnot. rewrite xbits_lxor, xbits_ones. reflexivity.
Qed.

Theorem xbits_shiftl:
  forall n k i j, xbits (N.shiftl n k) i j = N.shiftl (xbits n (i-k) (j-k)) (k-i).
Proof.
  intros. unfold xbits. rewrite <- !N.land_ones. destruct (N.le_ge_cases k i).
    rewrite N.shiftr_shiftl_r, <- N.sub_add_distr, N.add_sub_assoc, N.add_comm, N.add_sub,
            (proj2 (N.sub_0_le k i) H), N.shiftl_0_r by assumption. reflexivity.

    rewrite (proj2 (N.sub_0_le i k) H), N.shiftr_0_r, N.sub_0_r, N.shiftr_shiftl_l by assumption.
    destruct (N.le_ge_cases k j).

      etransitivity; [|apply N.lor_0_r].
      erewrite N.shiftl_land, <- (N.mod_mul _ (2^_)) by (apply N.pow_nonzero; discriminate).
      rewrite <- N.land_ones, <- N.shiftl_mul_pow2, <- N.land_lor_distr_r.
      rewrite <- N.lxor_lor, <- N.add_nocarry_lxor by
        (rewrite N.land_ones, N.shiftl_mul_pow2; apply N.mod_mul, N.pow_nonzero; discriminate).
      rewrite (N.shiftl_mul_pow2 (N.ones _)), N.mul_comm, <- N.ones_add, N.add_comm.
      rewrite N.add_sub_assoc, N.sub_add by assumption. reflexivity.

      rewrite (proj2 (N.sub_0_le j k) H0), N.land_0_r, N.shiftl_0_l. destruct (N.le_ge_cases i j).
        rewrite N.shiftl_mul_pow2, N.land_ones, <- (N.sub_add j k), <- N.add_sub_assoc, N.pow_add_r,
                N.mul_assoc by assumption. apply N.mod_mul, N.pow_nonzero. discriminate.
        rewrite (proj2 (N.sub_0_le j i)) by assumption. apply N.land_0_r.
Qed.

Theorem xbits_shiftr:
  forall n k i j, xbits (N.shiftr n k) i j = xbits n (i+k) (j+k).
Proof.
  intros. unfold xbits.
  rewrite N.shiftr_shiftr, (N.add_comm i k), N.sub_add_distr, N.add_sub.
  reflexivity.
Qed.

Lemma N2Z_inj_ones:
  forall n, Z.of_N (N.ones n) = Z.ones (Z.of_N n).
Proof.
  intros. rewrite N.ones_equiv, Z.ones_equiv, N2Z.inj_pred, N2Z.inj_pow. reflexivity.
  apply N.neq_0_lt_0, N.pow_nonzero. discriminate.
Qed.

Lemma Z2N_inj_ones:
  forall z, Z.to_N (Z.ones z) = N.ones (Z.to_N z).
Proof.
  intros. rewrite Z.ones_equiv, N.ones_equiv, Z2N.inj_pred. destruct z as [|p|p]; try reflexivity.
  rewrite Z2N.inj_pow by discriminate 1. reflexivity.
Qed.

Lemma Z2N_inj_mul:
  forall z1 z2, (0 <= z1 \/ 0 <= z2 -> Z.to_N (z1 * z2) = (Z.to_N z1 * Z.to_N z2)%N)%Z.
Proof.
  assert (THM: forall m n, (0 <= m -> Z.to_N (m * n) = (Z.to_N m * Z.to_N n)%N)%Z).
    intros. destruct n.
      rewrite Z.mul_0_r, N.mul_0_r. reflexivity.
      apply Z2N.inj_mul. assumption. discriminate.
      rewrite N.mul_0_r, Z.mul_comm. destruct m; try reflexivity. exfalso. apply H. reflexivity.
  intros. destruct H.
    apply THM, H.
    rewrite Z.mul_comm, N.mul_comm. apply THM, H.
Qed.

Lemma N2Z_inj_land:
  forall n1 n2, Z.of_N (N.land n1 n2) = Z.land (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. apply Z.bits_inj'. intros i H.
  rewrite Z.testbit_of_N', Z.land_spec, !Z.testbit_of_N' by assumption. apply N.land_spec.
Qed.

Lemma Z2N_inj_land:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.land z1 z2) = N.land (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1, z2; try (reflexivity + contradiction).
  apply N2Z.id.
Qed.

Lemma N2Z_inj_lor:
  forall n1 n2, Z.of_N (N.lor n1 n2) = Z.lor (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. apply Z.bits_inj'. intros i H.
  rewrite Z.testbit_of_N', Z.lor_spec, !Z.testbit_of_N' by assumption. apply N.lor_spec.
Qed.

Lemma Z2N_inj_lor:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.lor z1 z2) = N.lor (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1, z2; reflexivity + contradiction.
Qed.

Lemma N2Z_inj_lxor:
  forall n1 n2, Z.of_N (N.lxor n1 n2) = Z.lxor (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. apply Z.bits_inj'. intros i H.
  rewrite Z.testbit_of_N', Z.lxor_spec, !Z.testbit_of_N' by assumption. apply N.lxor_spec.
Qed.

Lemma Z2N_inj_lxor:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.lxor z1 z2) = N.lxor (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1, z2; try (reflexivity + contradiction).
  apply N2Z.id. 
Qed.

Lemma N2Z_inj_ldiff:
  forall n1 n2, Z.of_N (N.ldiff n1 n2) = Z.ldiff (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. apply Z.bits_inj'. intros i H.
  rewrite Z.testbit_of_N', Z.ldiff_spec, !Z.testbit_of_N' by assumption. apply N.ldiff_spec.
Qed.

Lemma Z2N_inj_ldiff:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.ldiff z1 z2) = N.ldiff (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1, z2; try (reflexivity + contradiction).
  apply N2Z.id. 
Qed.

Lemma N2Z_inj_shiftl:
  forall n1 n2, Z.of_N (N.shiftl n1 n2) = Z.shiftl (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. rewrite N.shiftl_mul_pow2, Z.shiftl_mul_pow2 by apply N2Z.is_nonneg.
  change 2%Z with (Z.of_N 2). rewrite <- N2Z.inj_pow. apply N2Z.inj_mul.
Qed.

Lemma Z2N_inj_shiftl:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.shiftl z1 z2) = N.shiftl (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1.
    rewrite Z.shiftl_0_l. reflexivity.
    destruct z2.
      reflexivity.
      simpl. erewrite (Pos.iter_swap_gen _ _ Z.to_N _ (N.mul 2)), (Pos.iter_swap_gen _ _ N.pos).
        reflexivity.
        reflexivity.
        intro a. destruct a; reflexivity.
      contradiction.
    contradiction.
Qed.

Lemma N2Z_inj_shiftr: forall n1 n2, Z.of_N (N.shiftr n1 n2) = Z.shiftr (Z.of_N n1) (Z.of_N n2).
Proof.
  intros. rewrite N.shiftr_div_pow2, Z.shiftr_div_pow2 by apply N2Z.is_nonneg.
  change 2%Z with (Z.of_N 2). rewrite <- N2Z.inj_pow. apply N2Z.inj_div.
Qed.

Lemma Z2N_inj_shiftr:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> Z.to_N (Z.shiftr z1 z2) = N.shiftr (Z.to_N z1) (Z.to_N z2))%Z.
Proof.
  intros. destruct z1.
    rewrite Z.shiftr_0_l, N.shiftr_0_l. reflexivity.
    destruct z2.
      reflexivity.
      unfold Z.shiftr. simpl. erewrite (Pos.iter_swap_gen _ _ Z.to_N _ N.div2).
        reflexivity.
        exact Z2N.inj_div2.
      contradiction.
    contradiction.
Qed.

Lemma N2Z_inj_eqb:
  forall n1 n2, (n1 =? n2)%N = (Z.of_N n1 =? Z.of_N n2)%Z.
Proof.
  intros. rewrite N.eqb_compare, Z.eqb_compare, N2Z.inj_compare. reflexivity.
Qed.

Lemma Z2N_inj_eqb:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> z1 =? z2 = (Z.to_N z1 =? Z.to_N z2)%N)%Z.
Proof.
  intros. rewrite N.eqb_compare, Z.eqb_compare, Z2N.inj_compare by assumption. reflexivity.
Qed.

Lemma N2Z_inj_ltb:
  forall n1 n2, (Z.of_N n1 <? Z.of_N n2)%Z = (n1 <? n2)%N.
Proof.
  intros. unfold Z.ltb. rewrite N2Z.inj_compare. reflexivity.
Qed.

Lemma Z2N_inj_ltb:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> (Z.to_N z1 <? Z.to_N z2)%N = (z1 <? z2))%Z.
Proof.
  intros. unfold N.ltb. rewrite Z2N.inj_compare by assumption. reflexivity.
Qed.

Lemma N2Z_inj_leb:
  forall m n, (Z.of_N m <=? Z.of_N n)%Z = (m <=? n).
Proof.
  intros. unfold Z.leb. rewrite N2Z.inj_compare. reflexivity.
Qed.

Lemma Z2N_inj_leb:
  forall z1 z2, (0 <= z1 -> 0 <= z2 -> (Z.to_N z1 <=? Z.to_N z2)%N = (z1 <=? z2))%Z.
Proof.
  intros. unfold N.leb. rewrite Z2N.inj_compare by assumption. reflexivity.
Qed.

Definition Z_xbits z i j := ((Z.shiftr z i) mod 2^Z.max 0 (j - i))%Z.

Theorem Z_xbits_spec:
  forall z i j b, (Z.testbit (Z_xbits z i j) b = Z.testbit z (b + i) && (b + i <? j) && (0 <=? b))%Z%bool.
Proof.
  intros. destruct (Z.le_gt_cases 0 b).

  unfold Z_xbits.
  rewrite <- Z.land_ones by apply Z.le_max_l.
  rewrite Z.land_spec, Z.shiftr_spec by assumption.
  rewrite Z.testbit_ones by apply Z.le_max_l.
  rewrite <- Bool.andb_assoc, (Bool.andb_comm (_ <? _)%Z).
  apply f_equal, f_equal. destruct (b + i <? j)%Z eqn:H1.
    apply Z.ltb_lt, Z.max_lt_iff. right. apply Z.lt_add_lt_sub_r, Z.ltb_lt, H1.
    apply Z.ltb_ge, Z.max_lub. assumption. apply Z.le_sub_le_add_r, Z.ltb_ge, H1.

  rewrite Z.testbit_neg_r by assumption.
  symmetry. apply Bool.andb_false_intro2, Z.leb_gt, H.
Qed.

Theorem Z_xbits_nonneg:
  forall z i j, (0 <= Z_xbits z i j)%Z.
Proof.
  intros. unfold Z_xbits. apply Z.mod_pos_bound, Z.pow_pos_nonneg.
    reflexivity.
    apply Z.le_max_l.
Qed.

Theorem Z_xbits_0_l:
  forall i j, Z_xbits 0 i j = Z0.
Proof.
  intros. unfold Z_xbits. rewrite Z.shiftr_0_l. apply Z.mod_0_l, Z.pow_nonzero.
    discriminate 1.
    apply Z.le_max_l.
Qed.

Theorem N2Z_xbits:
  forall n i j, Z.of_N (xbits n i j) = Z_xbits (Z.of_N n) (Z.of_N i) (Z.of_N j).
Proof.
  intros. unfold xbits, Z_xbits.
  rewrite N2Z.inj_mod, N2Z_inj_shiftr, N2Z.inj_pow, N2Z.inj_sub_max.
  reflexivity.
Qed.

Theorem Z2N_xbits:
  forall n i j, (0 <= n -> 0 <= i -> 0 <= j ->
  Z.to_N (Z_xbits n i j) = xbits (Z.to_N n) (Z.to_N i) (Z.to_N j))%Z.
Proof.
  intros. apply N2Z.inj. rewrite N2Z_xbits, !Z2N.id; try assumption.
    reflexivity.
    apply Z_xbits_nonneg.
Qed.

Theorem Z_xbits_equiv:
  forall z i j, Z_xbits z i j =  Z.shiftr (z mod 2^Z.max 0 j) i.
Proof.
  intros. apply Z.bits_inj. intro b. rewrite Z_xbits_spec, <- Z.land_ones by apply Z.le_max_l. destruct (Z.le_gt_cases 0 b).
    rewrite Z.shiftr_spec, Z.land_spec, (proj2 (Z.leb_le 0 b)), Bool.andb_true_r by assumption. destruct (Z.le_gt_cases 0 (b+i)).
      destruct (Z.le_ge_cases 0 j).
        rewrite Z.max_r, Z.testbit_ones, Zle_imp_le_bool by assumption. reflexivity.
        rewrite Z.max_l, Z.testbit_0_l, (proj2 (Z.ltb_ge _ _)). reflexivity.
          transitivity Z0; assumption.
          assumption.
      rewrite Z.testbit_neg_r by assumption. reflexivity.
    rewrite (proj2 (Z.leb_gt _ _)), Bool.andb_false_r, Z.testbit_neg_r by assumption. reflexivity.
Qed.

Theorem xbits_Z2N:
  forall z i j, (0 <= z)%Z -> xbits (Z.to_N z) i j = Z.to_N (Z_xbits z (Z.of_N i) (Z.of_N j)).
Proof.
  intros. rewrite Z2N_xbits, !N2Z.id. reflexivity.
    assumption.
    apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
Qed.

End XBits.



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

Lemma N_mod_mod_pow:
  forall n a b c, a <> 0 -> n mod a^b mod a^c = n mod a^N.min b c.
Proof.
  intros. destruct (N.le_ge_cases b c) as [H1|H1].
    rewrite (N.min_l _ _ H1). eapply N.mod_small, N.lt_le_trans.
      apply N.mod_lt, N.pow_nonzero, H.
      apply N.pow_le_mono_r; assumption.
    rewrite (N.min_r _ _ H1), <- (N.sub_add _ _ H1), N.pow_add_r, N.mul_comm, N.mod_mul_r,
            N.mul_comm, N.mod_add, N.mod_mod by apply N.pow_nonzero, H. reflexivity.
Qed.

Lemma Z_mod_mod_pow:
  forall z a b c, (0 < a -> 0 <= b -> 0 <= c -> z mod a^b mod a^c = z mod a^Z.min b c)%Z.
Proof.
  intros. destruct (Z.le_ge_cases b c).
    rewrite Z.min_l by assumption. apply Z.mod_small. split.
      apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; assumption.
      eapply Z.lt_le_trans.
        apply Z.mod_pos_bound, Z.pow_pos_nonneg; assumption.
        apply Z.pow_le_mono_r; assumption.
    rewrite Z.min_r, <- (Zplus_minus c b), Z.pow_add_r, Z.rem_mul_r, Z.mul_comm, Z_mod_plus_full. apply Zmod_mod.
      apply Z.pow_nonzero. apply not_eq_sym, Z.lt_neq. assumption. assumption.
      apply Z.pow_pos_nonneg. assumption. apply Z.le_0_sub. assumption.
      assumption.
      apply Z.le_0_sub. assumption.
      assumption.
Qed.

Theorem signed_range_0_l:
  forall z, signed_range 0 z -> z = Z0.
Proof.
  intros. destruct z as [|z|z].
    reflexivity.
    apply proj2 in H. destruct z; discriminate.
    apply proj1 in H. contradiction.
Qed.

Theorem signed_range_0_r:
  forall w, signed_range w 0.
Proof.
  split.
    apply Z.opp_nonpos_nonneg, Z.pow_nonneg. discriminate.
    apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem signed_range_abs:
  forall w z (SR: signed_range w z), (Z.abs z <= 2^Z.of_N (N.pred w))%Z.
Proof.
  intros. destruct w as [|w].
    apply signed_range_0_l in SR. subst z. discriminate.
    destruct z as [|n|n].
      apply Z.pow_nonneg. discriminate.
      apply Z.lt_le_incl, SR.
      rewrite N2Z.inj_pred by reflexivity. apply Z.opp_le_mono, SR.
Qed.

Theorem signed_range_mono_l:
  forall w' w z (LE: w' <= w) (SR: signed_range w' z), signed_range w z.
Proof.
  split.
    etransitivity; [|apply SR]. apply -> Z.opp_le_mono. apply Z.pow_le_mono_r.
      reflexivity.
      apply -> Z.pred_le_mono. apply N2Z.inj_le, LE.
    eapply Z.lt_le_trans. apply SR. apply Z.pow_le_mono_r.
      reflexivity.
      apply N2Z.inj_le, N.pred_le_mono, LE.
Qed.

Theorem signed_range_mono_r:
  forall w z' z (LE: (Z.abs z < Z.abs z')%Z) (SR: signed_range w z'), signed_range w z.
Proof.
  intros. destruct w as [|w].
    contradict LE. apply signed_range_0_l in SR. subst z'. apply Z.nlt_ge, Z.abs_nonneg.
    destruct z as [|n|n].
      apply signed_range_0_r.
      split.
        etransitivity.
          apply Z.opp_nonpos_nonneg, Z.pow_nonneg. discriminate.
          discriminate.
        eapply Z.lt_le_trans.
          apply LE.
          apply signed_range_abs, SR.
      split; etransitivity.
        rewrite <- N2Z.inj_pred by reflexivity. apply -> Z.opp_le_mono. apply signed_range_abs, SR.
        apply Z.opp_le_mono. rewrite Z.opp_involutive. apply Z.lt_le_incl, LE.
        apply Zlt_neg_0.
        apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem signed_range_hibits:
  forall i w z (SR: signed_range w z) (HI: w <= i),
  Z.testbit z (Z.of_N i) = Z.testbit z (Z.pred (Z.of_N w)).
Proof.
  intros. destruct w as [|w].
    apply signed_range_0_l in SR. subst z. rewrite !Z.testbit_0_l. reflexivity.
    destruct z as [|z|z].
      rewrite !Z.testbit_0_l. reflexivity.
      replace (Z.testbit _ _) with false; symmetry; apply Z.bits_above_log2; try discriminate 1.
        apply Z.log2_lt_pow2. reflexivity. rewrite <- N2Z.inj_pred by reflexivity. apply SR.
        apply Z2N.inj_lt.
          apply Z.log2_nonneg.
          apply N2Z.is_nonneg.
          rewrite N2Z.id. eapply N.lt_le_trans; [|eassumption]. apply N.lt_pred_lt, N2Z.inj_lt. rewrite Z2N.id.
            apply Z.log2_lt_pow2. reflexivity. apply SR.
            apply Z.log2_nonneg.
      destruct (Pos.lt_total z 1) as [H|[H|H]].
        contradict H. apply Pos.nlt_1_r.
        subst z. rewrite Z.bits_m1 by apply N2Z.is_nonneg. symmetry. apply Z.bits_m1, Z.lt_le_pred. reflexivity.

        apply proj1, Z.opp_le_mono in SR. rewrite Z.opp_involutive in SR.
        replace (Z.testbit _ _) with true; symmetry; apply Z.bits_above_log2_neg; try reflexivity.
          apply Z.log2_lt_pow2.
            apply Z.succ_lt_mono. rewrite Z.succ_pred. exact H.
            apply Z.lt_pred_le. apply SR.
          apply Z2N.inj_lt.
            apply Z.log2_nonneg.
            apply N2Z.is_nonneg.
            rewrite N2Z.id. eapply N.lt_le_trans; [|eassumption]. apply N2Z.inj_lt. rewrite Z2N.id.
              apply Z.log2_lt_pow2.
                apply Z.succ_lt_mono. rewrite Z.succ_pred. exact H.
                apply Z.lt_pred_le. etransitivity. apply SR. apply Z.pow_le_mono_r. reflexivity. apply Z.le_pred_l.
              apply Z.log2_nonneg.
Qed.

Theorem hibits_signed_range:
  forall w z (HI: forall i, w <= i -> Z.testbit z (Z.of_N i) = Z.testbit z (Z.pred (Z.of_N w))),
  signed_range w z.
Proof.
  intros. destruct w as [|w].
    replace z with Z0.
      apply signed_range_0_r.
      symmetry. apply Z.bits_inj_0. intro i. destruct (Z.neg_nonneg_cases i).
        apply Z.testbit_neg_r. assumption.
        rewrite <- (Z2N.id i) by assumption. apply HI, N.le_0_l.
    split.
      apply Z.opp_le_mono, Z.lt_pred_le. rewrite Z.opp_involutive. destruct (Z.nonpos_pos_cases (Z.pred (-z))) as [H|H].
        eapply Z.le_lt_trans. exact H. apply Z.pow_pos_nonneg. reflexivity. destruct w; discriminate.
        apply Z.log2_lt_pow2. exact H. apply Z.lt_nge. intro H2. apply Z.le_lteq in H2. destruct H2 as [H2|H2].
          apply Z.lt_pred_le, Z2N.inj_le in H2.
            rewrite N2Z.id in H2. assert (H3:=N.le_le_succ_r _ _ H2). apply HI in H2. apply HI in H3. rewrite <- H3, N2Z.inj_succ, !Z2N.id in H2.
              rewrite Z.bit_log2_neg, Z.bits_above_log2_neg in H2.
                discriminate.
                apply Z.opp_pos_neg. etransitivity. exact H. apply Z.lt_pred_l.
                apply Z.lt_succ_diag_r.
                apply Z.opp_lt_mono. rewrite Z.opp_involutive. apply Z.pred_lt_mono, H.
              apply Z.log2_nonneg.
            apply N2Z.is_nonneg.
            apply Z.log2_nonneg.
          rewrite H2, Z.bit_log2_neg in HI.
            specialize (HI _ (N.le_refl _)). rewrite Z.bits_above_log2_neg in HI.
              discriminate.
              apply Z.opp_pos_neg. etransitivity. exact H. apply Z.lt_pred_l.
              rewrite <- H2. apply Z.lt_pred_l.
            apply Z.opp_lt_mono. rewrite Z.opp_involutive. apply Z.pred_lt_mono, H.
      destruct (Z.nonpos_pos_cases z) as [H|H].
        eapply Z.le_lt_trans. exact H. apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
        rewrite N2Z.inj_pred by reflexivity. apply Z.log2_lt_pow2. exact H. apply Z.lt_nge. intro H2. apply Z.le_lteq in H2. destruct H2 as [H2|H2].
          apply Z.lt_pred_le, Z2N.inj_le in H2.
            rewrite N2Z.id in H2. assert (H3:=N.le_le_succ_r _ _ H2). apply HI in H2. apply HI in H3. rewrite <- H3, N2Z.inj_succ, !Z2N.id in H2.
              rewrite Z.bit_log2 in H2 by exact H. rewrite Z.bits_above_log2 in H2.
                discriminate.
                apply Z.lt_le_incl, H.
                apply Z.lt_succ_diag_r.
              apply Z.log2_nonneg.
            apply N2Z.is_nonneg.
            apply Z.log2_nonneg.
          rewrite H2, Z.bit_log2 in HI by exact H. specialize (HI _ (N.le_refl _)). rewrite Z.bits_above_log2 in HI.
            discriminate.
            apply Z.lt_le_incl, H.
            rewrite <- H2. apply Z.lt_pred_l.
Qed.

Theorem N2Z_ofZ:
  forall w z, Z.of_N (ofZ w z) = (z mod 2^Z.of_N w)%Z.
Proof.
  intros. unfold ofZ. rewrite Z2N.id.
    reflexivity.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem ofZ_N2Z:
  forall w n, ofZ w (Z.of_N n) = n mod 2^w.
Proof.
  intros. unfold ofZ. change 2%Z with (Z.of_N 2).
  rewrite <- N2Z.inj_pow, <- N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  apply N2Z.id.
Qed.

Theorem ofZ_bound:
  forall w z, ofZ w z < 2^w.
Proof.
  intros. rewrite <- (N2Z.id (2^w)). unfold ofZ. apply Z2N.inj_lt.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
    rewrite N2Z.inj_pow. apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem canonicalZ_bounds:
  forall w z, signed_range w (canonicalZ (Z.of_N w) z).
Proof.
  intros. unfold canonicalZ, signed_range.
  destruct w as [|w]. rewrite Z.mod_1_r. split; reflexivity.
  rewrite N2Z.inj_pred by reflexivity.
  rewrite <- (Z.succ_pred (Z.of_N (N.pos w))) at 3 6.
  set (w' := Z.pred (Z.of_N (N.pos w))).
  rewrite Z.pow_succ_r by (apply Zlt_0_le_0_pred; reflexivity).
  split.
    apply Z.le_add_le_sub_l. rewrite Z.add_opp_diag_r. apply Z.mod_pos_bound, Z.mul_pos_pos.
      reflexivity.
      apply Z.pow_pos_nonneg. reflexivity. apply Zlt_0_le_0_pred. reflexivity.
    apply Z.lt_sub_lt_add_r. rewrite Z.add_diag. apply Z.mod_pos_bound, Z.mul_pos_pos.
      reflexivity.
      apply Z.pow_pos_nonneg. reflexivity. apply Zlt_0_le_0_pred. reflexivity.
Qed.

Corollary toZ_bounds:
  forall w n, signed_range w (toZ w n).
Proof. intros. apply canonicalZ_bounds. Qed.

Corollary ofZ_0_l:
  forall z, ofZ 0 z = 0.
Proof. intro. apply N.lt_1_r, ofZ_bound. Qed.

Theorem ofZ_0_r:
  forall w, ofZ w 0 = 0.
Proof. reflexivity. Qed.

Theorem canonicalZ_neg_l:
  forall w z, (w < 0)%Z -> canonicalZ w z = z.
Proof.
  intros. unfold canonicalZ.
  rewrite (Z.pow_neg_r _ w), Zmod_0_r by assumption. apply Z.add_simpl_r.
Qed.

Theorem canonicalZ_0_l:
  forall z, canonicalZ 0 z = Z0.
Proof.
  intros. unfold canonicalZ. rewrite Z.mod_1_r. reflexivity.
Qed.

Theorem canonicalZ_0_r:
  forall w, canonicalZ w 0 = Z0.
Proof.
  intros. destruct w as [|w|w].
    reflexivity.
    unfold canonicalZ. rewrite Z.add_0_l, Z.mod_small. apply Z.sub_diag. split.
      apply Z.pow_nonneg. discriminate.
      apply Z.pow_lt_mono_r. reflexivity. discriminate. apply Z.lt_pred_l.
    apply canonicalZ_neg_l. reflexivity.
Qed.

Corollary toZ_0_l:
  forall n, toZ 0 n = Z0.
Proof.
  intros. assert (B:=toZ_bounds 0 n). destruct B as [B1 B2].
  destruct (toZ 0 n). reflexivity. destruct p; discriminate. contradiction.
Qed.

Corollary toZ_0_r:
  forall w, toZ w 0 = Z0.
Proof. intros. apply canonicalZ_0_r. Qed.

Corollary sbop1_0_l:
  forall zop n1 n2, sbop1 zop 0 n1 n2 = 0.
Proof. intros. apply ofZ_0_l. Qed.

Corollary sbop2_0_l:
  forall zop n1 n2, sbop2 zop 0 n1 n2 = 0.
Proof. intros. apply ofZ_0_l. Qed.

Theorem eqm_eq:
  forall w z1 z2 (SR1: signed_range w z1) (SR2: signed_range w z2),
  eqm (2^Z.of_N w) z1 z2 -> z1 = z2.
Proof.
  unfold signed_range, eqm. intros. destruct w as [|w].
    destruct SR1, SR2, z1, z2; try first [ contradiction | destruct p; discriminate ]. reflexivity.

  assert (H1: forall z, signed_range (N.pos w) z ->
      (z + 2^Z.pred (Z.of_N (N.pos w)) = (z + 2^Z.pred (Z.of_N (N.pos w))) mod 2^Z.of_N (N.pos w))%Z).
    intros. symmetry. apply Z.mod_small. split.
      apply Z.le_sub_le_add_r. rewrite Z.sub_0_l. apply H0.
      rewrite <- (Z.succ_pred (Z.of_N (N.pos w))) at 2. rewrite Z.pow_succ_r, <- Z.add_diag.
         apply Z.add_lt_mono_r. rewrite <- N2Z.inj_pred by reflexivity. apply H0.
         destruct w; discriminate.

  apply (Z.add_cancel_r _ _ (2^Z.pred (Z.of_N (N.pos w)))). etransitivity.
    apply H1, SR1.
    rewrite <- Zplus_mod_idemp_l, H, Zplus_mod_idemp_l. symmetry. apply H1, SR2.
Qed.

Theorem N2Z_eqm_eq:
  forall w n1 n2 (LT1: n1 < 2^w) (LT2: n2 < 2^w),
  eqm (2^Z.of_N w) (Z.of_N n1) (Z.of_N n2) -> n1 = n2.
Proof.
  unfold eqm. intros. revert H.
  change 2%Z with (Z.of_N 2). rewrite <- N2Z.inj_pow, <- !N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  intro H. apply N2Z.inj. rewrite !N.mod_small in H; assumption.
Qed.

Theorem eqm_canonicalZ:
  forall w' w z, (0 <= w' -> w' <= w -> eqm (2^w') (canonicalZ w z) z)%Z.
Proof.
  intros. unfold eqm, canonicalZ.
  rewrite <- Zminus_mod_idemp_l, Z_mod_mod_pow.
    rewrite Z.min_r, Zminus_mod_idemp_l, Z.add_simpl_r by assumption. reflexivity.
    reflexivity.
    etransitivity; eassumption.
    assumption.
Qed.

Theorem eqm_toZ:
  forall w' w n, (0 <= w' -> w' <= Z.of_N w -> eqm (2^w') (toZ w n) (Z.of_N n))%Z.
Proof.
  intros. etransitivity. apply eqm_canonicalZ.
    assumption.
    assumption.
    reflexivity.
Qed.

Theorem eqm_ofZ:
  forall w' w z, (0 <= w' -> w' <= Z.of_N w -> eqm (2^w') (Z.of_N (ofZ w z)) z)%Z.
Proof.
  intros. unfold ofZ, eqm. rewrite Z2N.id.
    rewrite <- (Z.min_r _ _ H0) at 2. apply Z_mod_mod_pow. reflexivity. apply N2Z.is_nonneg. assumption.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem canonicalZ_mod_pow2:
  forall w' w z, (0 <= w -> w <= w' -> canonicalZ w (z mod 2^w') = canonicalZ w z)%Z.
Proof.
  intros. unfold canonicalZ at 1. rewrite <- Zplus_mod_idemp_l, Z_mod_mod_pow, (Z.min_r _ _ H0), Zplus_mod_idemp_l.
    reflexivity.
    reflexivity.
    etransitivity; eassumption.
    assumption.
Qed.

Theorem mod_pow2_canonicalZ:
  forall w w' z, (0 <= w' -> w' <= w -> (canonicalZ w z) mod 2^w' = z mod 2^w')%Z.
Proof.
  intros. apply eqm_canonicalZ; assumption.
Qed.

Theorem toZ_mod_pow2:
  forall w' w n, w <= w' -> toZ w (n mod 2^w') = toZ w n.
Proof.
  intros. unfold toZ. rewrite N2Z.inj_mod, N2Z.inj_pow.
    apply canonicalZ_mod_pow2, N2Z.inj_le, H.
    apply N2Z.is_nonneg.
Qed.

Theorem mod_pow2_toZ:
  forall w w' n, w' <= w  -> (toZ w n mod 2^Z.of_N w')%Z = Z.of_N (n mod 2^w').
Proof.
  intros. unfold toZ. rewrite mod_pow2_canonicalZ, N2Z.inj_mod, N2Z.inj_pow. reflexivity.
    apply N2Z.is_nonneg.
    apply N2Z.inj_le, H.
Qed.

Theorem ofZ_mod_pow2:
  forall w w' z, w' <= w -> ofZ w' (z mod 2^Z.of_N w) = ofZ w' z.
Proof.
  intros. unfold ofZ. rewrite Z_mod_mod_pow, Z.min_r. reflexivity.
    apply N2Z.inj_le, H.
    reflexivity.
    apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
Qed.

Theorem mod_pow2_ofZ:
  forall w w' z, w <= w' -> ofZ w z mod 2^w' = ofZ w z.
Proof.
  intros. unfold ofZ. eapply N.mod_small, N.lt_le_trans.
    apply ofZ_bound.
    apply N.pow_le_mono_r. discriminate. assumption.
Qed.

Theorem ofZ_canonicalZ:
  forall w w' z, w' <= w -> ofZ w' (canonicalZ (Z.of_N w) z) = ofZ w' z.
Proof.
  intros. unfold ofZ. rewrite mod_pow2_canonicalZ. reflexivity.
    apply N2Z.is_nonneg.
    apply N2Z.inj_le, H.
Qed.

Theorem eqm_canonicalZ_op:
  forall f w z, (forall z0, eqm (2^w) (f z0) (f (z0 mod 2^w)%Z)) -> eqm (2^w) (f z) (f (canonicalZ w z)).
Proof.
  intros. destruct (Z.lt_ge_cases w 0).
    rewrite canonicalZ_neg_l by assumption. reflexivity.
    etransitivity. apply H. rewrite <- (mod_pow2_canonicalZ w w z), <- H. reflexivity. assumption. reflexivity.
Qed.

Theorem eqm_ofZ_canonicalZ:
  forall f w z, (forall z0, eqm (2^Z.of_N w) (f z0) (f (z0 mod 2^Z.of_N w)))%Z -> ofZ w (f (canonicalZ (Z.of_N w) z)) = ofZ w (f z).
Proof.
  intros. unfold ofZ. erewrite H, eqm_canonicalZ, <- H. reflexivity.
    apply N2Z.is_nonneg.
    reflexivity.
Qed.

Theorem toZ_ofZ_canonicalZ:
  forall w' w z, w' <= w -> toZ w' (ofZ w z) = canonicalZ (Z.of_N w') z.
Proof.
  intros. unfold toZ. rewrite N2Z_ofZ. apply canonicalZ_mod_pow2, N2Z.inj_le, H. apply N2Z.is_nonneg.
Qed.

Theorem canonicalZ_id:
  forall w' w z (LE: w' <= (Z.to_N w)) (SR: signed_range w' z), canonicalZ w z = z.
Proof.
  intros. destruct (Z.neg_nonneg_cases w) as [H|H].
    replace w' with 0 in SR.
      apply signed_range_0_l in SR. subst z. apply canonicalZ_0_r.
      symmetry. apply N.le_0_r. destruct w; try discriminate. exact LE.
    rewrite <- (Z2N.id w) by exact H. apply (eqm_eq (Z.to_N w)).
      apply canonicalZ_bounds.
      eapply signed_range_mono_l; eassumption.
      apply eqm_canonicalZ. apply N2Z.is_nonneg. reflexivity.
Qed.

Theorem canonicalZ_involutive:
  forall w1 w2 z, (0 <= w1 -> 0 <= w2 -> canonicalZ w1 (canonicalZ w2 z) = canonicalZ (Z.min w1 w2) z)%Z.
Proof.
  intros.
  destruct (Z.le_ge_cases w1 w2) as [H1|H1].
    rewrite (Z.min_l _ _ H1), <- (canonicalZ_mod_pow2 _ _ _ H H1), mod_pow2_canonicalZ.
      rewrite (canonicalZ_mod_pow2 _ _ _ H). reflexivity. assumption.
      assumption.
      reflexivity.
    rewrite (Z.min_r _ _ H1). apply (canonicalZ_id (Z.to_N w2)).
      apply Z2N.inj_le; assumption.
      rewrite <- (Z2N.id w2) at 2 by assumption. apply canonicalZ_bounds.
Qed.

Theorem ofZ_toZ_bitcast:
  forall w w' n, w' <= w -> ofZ w' (toZ w n) = n mod 2^w'.
Proof.
  intros. unfold ofZ. rewrite mod_pow2_toZ by exact H. apply N2Z.id.
Qed.

Corollary ofZ_toZ:
  forall w n, ofZ w (toZ w n) = n mod 2^w.
Proof. intros. apply ofZ_toZ_bitcast. reflexivity. Qed.

Theorem eqm_toZ_ofZ:
  forall w' w w0 z, w0 <= w' -> w' <= w -> eqm (2^Z.of_N w0) (toZ w' (ofZ w z)) z.
Proof.
  intros.
  rewrite toZ_ofZ_canonicalZ by assumption.
  apply eqm_canonicalZ, N2Z.inj_le.
    apply N2Z.is_nonneg.
    assumption.
Qed.

Corollary toZ_ofZ:
  forall w z (SR: signed_range w z), toZ w (ofZ w z) = z.
Proof.
  intros. rewrite toZ_ofZ_canonicalZ by reflexivity.
  eapply canonicalZ_id, SR. rewrite N2Z.id. reflexivity.
Qed.

Corollary toZ_inj:
  forall w n1 n2 (LT1: n1 < 2^w) (LT2: n2 < 2^w),
    toZ w n1 = toZ w n2 -> n1 = n2.
Proof.
  intros.
  erewrite <- (N.mod_small n1), <- (N.mod_small n2) by eassumption.
  rewrite <- (ofZ_toZ w n1), <- (ofZ_toZ w n2), H by assumption.
  reflexivity.
Qed.

Theorem ofZ_inj:
  forall w z1 z2 (SR1: signed_range w z1) (SR2: signed_range w z2),
    ofZ w z1 = ofZ w z2 -> z1 = z2.
Proof.
  intros. rewrite <- (toZ_ofZ w z1), <- (toZ_ofZ w z2), H by assumption. reflexivity.
Qed.

Theorem canonicalZ_nonneg:
  forall w z, (z mod 2^w < 2^Z.pred w -> canonicalZ w z = z mod 2^w)%Z.
Proof.
  intros. destruct (Z.lt_trichotomy w 0) as [H2|[H2|H2]].
    rewrite Z.pow_neg_r, Zmod_0_r by exact H2. apply canonicalZ_neg_l. assumption.
    subst w. rewrite Z.mod_1_r. apply canonicalZ_0_l.
    erewrite <- canonicalZ_mod_pow2; [|apply Z.lt_le_incl, H2 | reflexivity].
      unfold canonicalZ. rewrite Z.mod_small, Z.add_simpl_r. reflexivity. split.
        apply Z.add_nonneg_nonneg.
          apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply Z.lt_le_incl, H2.
          apply Z.pow_nonneg. discriminate.
        rewrite <- (Z.succ_pred w) at 3. rewrite Z.pow_succ_r, <- Z.add_diag.
          apply Z.add_lt_le_mono. assumption. reflexivity.
          apply Z.lt_le_pred, H2.
Qed.

Theorem canonicalZ_neg:
  forall w z, (0 < w -> 2^Z.pred w <= z mod 2^w -> canonicalZ w z = z mod 2^w - 2^w)%Z.
Proof.
  intros. erewrite <- canonicalZ_mod_pow2; [|apply Z.lt_le_incl, H | reflexivity]. unfold canonicalZ.
  rewrite <- (Z.sub_add (2^Z.pred w) (z mod 2^w)) at 1.
  rewrite <- Z.add_assoc, Z.add_diag, <- Z.pow_succ_r, Z.succ_pred by apply Z.lt_le_pred, H.
  rewrite <- Z.add_mod_idemp_r, Z.mod_same, Z.add_0_r by (apply Z.pow_nonzero; [ discriminate | apply Z.lt_le_incl, H ]).
  rewrite Z.mod_small, <- Z.sub_add_distr, Z.add_diag.
    rewrite <- Z.pow_succ_r, Z.succ_pred by apply Z.lt_le_pred, H. reflexivity.
    split.
      apply Z.le_0_sub. assumption.
      eapply Z.le_lt_trans.
        apply Z.le_sub_nonneg, Z.pow_nonneg. discriminate.
        apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply Z.lt_le_incl, H.
Qed.

Theorem toZ_nonneg:
  forall w n, n mod 2^w < 2^N.pred w <-> toZ w n = Z.of_N (n mod 2^w).
Proof.
  split; intro H1.

    destruct w as [|w].
      rewrite N.mod_1_r. apply toZ_0_l.
      unfold toZ. rewrite canonicalZ_nonneg; change 2%Z with (Z.of_N 2); rewrite <- N2Z.inj_pow.
        symmetry. apply N2Z.inj_mod.

        rewrite <- N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
        rewrite <- N2Z.inj_pred, <- N2Z.inj_pow by reflexivity.
        apply N2Z.inj_lt, H1.

    apply (f_equal Z.to_N) in H1. rewrite N2Z.id in H1. rewrite <- H1. destruct (toZ w n) eqn:H2.
      apply N.neq_0_lt_0, N.pow_nonzero. discriminate.
      apply N2Z.inj_lt. rewrite Z2N.id, N2Z.inj_pow, <- H2 by discriminate. apply toZ_bounds.
      apply N.neq_0_lt_0, N.pow_nonzero. discriminate.
Qed.

Theorem toZ_neg:
  forall w n, 2^N.pred (N.pos w) <= n mod 2^(N.pos w) <-> toZ (N.pos w) n = (Z.of_N (n mod 2^(N.pos w)) - 2^Z.of_N (N.pos w))%Z.
Proof.
  split; intro H1.

    unfold toZ. rewrite canonicalZ_neg; change 2%Z with (Z.of_N 2); try rewrite <- N2Z.inj_pow.
      rewrite <-N2Z.inj_mod. reflexivity.
      reflexivity.
      rewrite <- N2Z.inj_pred, <- N2Z.inj_pow, <- N2Z.inj_mod.
        apply N2Z.inj_le, H1.
        reflexivity.

    apply Z.add_move_r, (f_equal Z.to_N) in H1. rewrite N2Z.id in H1. rewrite <- H1.
    rewrite <- (N2Z.id (2^_)). apply Z2N.inj_le.
      apply N2Z.is_nonneg.
      rewrite <- (Z.add_opp_diag_l (2^Z.pred (Z.of_N (N.pos w)))). apply Z.add_le_mono.
        apply toZ_bounds.
        apply Z.pow_le_mono_r. reflexivity. apply Z.le_pred_l.
      rewrite <- (Z.succ_pred (Z.of_N (N.pos w))), Z.pow_succ_r, <- Z.add_diag, Z.add_assoc.
        rewrite <- (Z.add_0_l (Z.of_N _)), N2Z.inj_pow, N2Z.inj_pred.
          apply Z.add_le_mono_r, Z.le_sub_le_add_r. rewrite Z.sub_0_l. apply toZ_bounds.
          reflexivity.
        apply Z.lt_le_pred. reflexivity.
Qed.

Theorem testbit_ofZ:
  forall w z i, N.testbit (ofZ w z) i = andb (i <? w) (Z.testbit z (Z.of_N i)).
Proof.
  intros. destruct (N.lt_ge_cases i w).
    rewrite (proj2 (N.ltb_lt _ _) H). unfold ofZ. rewrite <- Z.testbit_of_N, Z2N.id.
      apply Z.mod_pow2_bits_low, N2Z.inj_lt, H.
      apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
    rewrite (proj2 (N.ltb_ge _ _) H). eapply bound_hibits_zero.
      apply ofZ_bound.
      assumption.
Qed.

Theorem testbit_canonicalZ:
  forall w z i, (0 <= w -> Z.testbit (canonicalZ w z) i = Z.testbit z (Z.min i (Z.pred w)))%Z.
Proof.
  intros. apply Z.le_lteq in H. destruct H.
    unfold canonicalZ. destruct (Z.le_gt_cases i (Z.pred w)) as [H2|H2].

      rewrite Z.min_l by assumption.
      rewrite <- (Z.mod_pow2_bits_low _ w) by apply Z.lt_le_pred, H2.
      rewrite Zminus_mod_idemp_l, Z.add_simpl_r.
      apply Z.mod_pow2_bits_low, Z.lt_le_pred, H2.

      rewrite Z.min_r by apply Z.lt_le_incl, H2.
      rewrite <- (Z.sub_add (Z.pred w) i), <- Z.div_pow2_bits; [| apply Z.lt_le_pred, H | apply Z.le_0_sub, Z.lt_le_incl, H2].
      rewrite <- Z.add_opp_r, Z.opp_eq_mul_m1, Z.mul_comm, Z.div_add by (apply Z.pow_nonzero; [ discriminate | apply Z.lt_le_pred, H ]).
      rewrite <- Z.shiftr_div_pow2 by apply Z.lt_le_pred, H.
      rewrite <- Zplus_mod_idemp_l, <- !Z.land_ones, Z.shiftr_land by apply Z.lt_le_incl, H.
      rewrite Z.shiftr_div_pow2 by apply Z.lt_le_pred, H.
      rewrite <- (Z.mul_1_l (2^Z.pred w)) at 1.
      rewrite Z.div_add by (apply Z.pow_nonzero; [ discriminate | apply Z.lt_le_pred, H ]).
      rewrite <- Z.shiftr_div_pow2, Z.shiftr_land, !Z.shiftr_div_pow2 by apply Z.lt_le_pred, H.
      rewrite !Z.ones_div_pow2 by (split; [ apply Z.lt_le_pred, H | apply Z.le_pred_l ]).
      rewrite Z.sub_pred_r, Z.sub_diag, (Z.land_ones (_/_) 1) by discriminate.
      rewrite <- Z.testbit_spec' by apply Z.lt_le_pred, H.
      destruct (Z.testbit z (Z.pred w)).
        apply Z.bits_m1, Z.le_0_sub, Z.lt_le_incl, H2.
        apply Z.testbit_0_l.

    subst w. rewrite canonicalZ_0_l, Z.bits_0. symmetry. apply Z.testbit_neg_r, Z.min_lt_iff.
    right. reflexivity.
Qed.

Corollary testbit_toZ:
  forall w n i, w <> 0 -> Z.testbit (toZ w n) (Z.of_N i) = N.testbit n (N.min i (N.pred w)).
Proof.
  intros. unfold toZ.
  rewrite testbit_canonicalZ, <- N2Z.inj_pred, <- N2Z.inj_min.
    apply N2Z.inj_testbit.
    apply N.neq_0_lt_0, H.
    apply N2Z.is_nonneg.
Qed.

Theorem signbit:
  forall n w, w <> 0 -> (N.testbit n (N.pred w) = (toZ w n <? 0))%Z.
Proof.
  intros. rewrite <- (N.min_id (N.pred w)). rewrite <- testbit_toZ by assumption.
  apply Z.b2z_inj. rewrite Z.testbit_spec' by apply N2Z.is_nonneg.
  destruct (_ <? 0)%Z eqn:SB.

    rewrite <- (Z.add_simpl_r (toZ w n) (2^Z.of_N (N.pred w))), <- Z.add_opp_r.
    rewrite  <- (Z.mul_1_l (2^_)) at 2.
    rewrite <- Z.mul_opp_l, Z.div_add by (apply Z.pow_nonzero; [ discriminate | apply N2Z.is_nonneg ]).
    rewrite Z.div_small. reflexivity. split.
      apply Z.le_sub_le_add_r. rewrite Z.sub_0_l, N2Z.inj_pred by apply N.neq_0_lt_0, H. apply toZ_bounds.
      apply Z.lt_add_lt_sub_r. rewrite Z.sub_diag. apply Z.ltb_lt, SB.

    rewrite Z.div_small. reflexivity. split. apply Z.ltb_ge, SB. apply toZ_bounds.
Qed.

Theorem toZ_sign:
  forall n w, n mod 2^w < 2^N.pred w <-> (0 <= toZ w n)%Z.
Proof.
  destruct w as [|w]; split; intro H1.
    rewrite toZ_0_l. reflexivity.
    rewrite N.mod_1_r. reflexivity.
    erewrite <- toZ_mod_pow2 by reflexivity. unfold toZ, canonicalZ. rewrite Z.mod_small; [|split].
      rewrite Z.add_simpl_r. apply N2Z.is_nonneg.
      apply Z.add_nonneg_nonneg. apply N2Z.is_nonneg. apply Z.pow_nonneg. discriminate.
      rewrite <- (Z.succ_pred (Z.of_N (N.pos w))) at 2. rewrite Z.pow_succ_r, <- Z.add_diag.
        apply Z.add_lt_mono_r. rewrite <- (Z2N.id (2^_)).
          apply N2Z.inj_lt. rewrite Z2N.inj_pow.
            rewrite Z2N.inj_pred, N2Z.id. exact H1.
            discriminate.
            apply Z.lt_le_pred. reflexivity.
          apply Z.pow_nonneg. discriminate.
        apply Z.lt_le_pred. reflexivity.
    rewrite <- ofZ_toZ. unfold ofZ. rewrite Z.mod_small; [|split].
      rewrite <- N2Z.id. apply Z2N.inj_lt.
        exact H1.
        apply N2Z.is_nonneg.
        rewrite N2Z.inj_pow. apply toZ_bounds.
      exact H1.
      eapply Z.lt_le_trans. apply toZ_bounds. apply Z.pow_le_mono_r. reflexivity. apply N2Z.inj_le, N.le_pred_l.
Qed.

Theorem toZ_nop:
  forall zop nop w n1 n2
    (N2Z: Z.of_N (nop n1 n2) = zop (Z.of_N n1) (Z.of_N n2))
    (MOD: forall z1 z2, w <> 0 -> ((zop z1 z2) mod 2^Z.of_N w = (zop (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  toZ w (nop n1 n2) = canonicalZ (Z.of_N w) (zop (toZ w n1) (toZ w n2)).
Proof.
  intros. destruct w as [|w]. rewrite canonicalZ_0_l. apply toZ_0_l.
  unfold toZ at 1. rewrite N2Z.
  unfold toZ. unfold canonicalZ at 3 4. symmetry.
  erewrite <- canonicalZ_mod_pow2; [| apply N2Z.is_nonneg | reflexivity ].
  rewrite MOD, !Zminus_mod_idemp_l, !Z.add_simpl_r, <- MOD by discriminate.
  apply canonicalZ_mod_pow2. apply N2Z.is_nonneg. reflexivity.
Qed.

Corollary nop_sbop2:
  forall zop nop w n1 n2
    (N2Z: Z.of_N (nop n1 n2) = zop (Z.of_N n1) (Z.of_N n2))
    (MOD: forall z1 z2, w <> 0 -> ((zop z1 z2) mod 2^Z.of_N w = (zop (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  (nop n1 n2) mod 2^w = sbop2 zop w n1 n2.
Proof.
  intros. apply (toZ_inj w). apply N.mod_upper_bound, N.pow_nonzero. discriminate. apply ofZ_bound.
  unfold sbop2. rewrite toZ_mod_pow2, toZ_ofZ_canonicalZ by reflexivity. apply toZ_nop; assumption.
Qed.

Corollary nop_sbop1:
  forall zop nop w n
    (N2Z: Z.of_N (nop n) = zop (Z.of_N n))
    (MOD: forall z, w <> 0 -> ((zop z) mod 2^Z.of_N w = (zop (z mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  (nop n) mod 2^w = ofZ w (zop (toZ w n)).
Proof.
  intros zop nop.
  pose (nop1 (n1:N) := nop). pose (zop1 (z1:Z) := zop).
  change nop with (nop1 N0). change zop with (zop1 Z0).
  intros. rewrite <- (toZ_0_r w). apply nop_sbop2. apply N2Z.
  intro. apply MOD.
Qed.

Theorem ofZ_zop2:
  forall zop nop w z1 z2
    (N2Z: Z.of_N (nop (ofZ w z1) (ofZ w z2)) = zop (Z.of_N (ofZ w z1)) (Z.of_N (ofZ w z2)))
    (MOD: w <> 0 -> ((zop z1 z2) mod 2^Z.of_N w = (zop (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  ofZ w (zop z1 z2) = (nop (ofZ w z1) (ofZ w z2)) mod 2^w.
Proof.
  intros. destruct w as [|w]. rewrite N.mod_1_r. apply ofZ_0_l.
  unfold ofZ at 1. apply N2Z.inj.
  rewrite N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  rewrite N2Z.
  rewrite !Z2N.id by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ]).
  unfold ofZ. rewrite !Z2N.id by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ]).
  rewrite N2Z.inj_pow. apply MOD. discriminate.
Qed.

Corollary ofZ_zop1:
  forall zop nop w z
    (N2Z: Z.of_N (nop (ofZ w z)) = zop (Z.of_N (ofZ w z)))
    (MOD: w <> 0 -> ((zop z) mod 2^Z.of_N w = (zop (z mod 2^Z.of_N w)) mod 2^Z.of_N w)%Z),
  ofZ w (zop z) = (nop (ofZ w z)) mod 2^w.
Proof.
  intros zop nop.
  pose (nop1 (n1 n2:N) := nop n2). pose (zop1 (z1 z2:Z) := zop z2).
  change nop with (nop1 N0). change zop with (zop1 Z0).
  intros. rewrite <- (ofZ_0_r w). apply ofZ_zop2; assumption.
Qed.

Theorem add_sbop:
  forall w n1 n2, (n1 + n2) mod 2^w = sbop2 Z.add w n1 n2.
Proof.
  intros. apply nop_sbop2.
    apply N2Z.inj_add.
    intros. apply Z.add_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem ofZ_add:
  forall w z1 z2, ofZ w (z1 + z2) = (ofZ w z1 + ofZ w z2) mod 2^w.
Proof.
  intros. apply ofZ_zop2.
    apply N2Z.inj_add.
    intros. apply Z.add_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem toZ_add:
  forall w n1 n2, toZ w (N.add n1 n2) = canonicalZ (Z.of_N w) (Z.add (toZ w n1) (toZ w n2)).
Proof.
  intros. apply (toZ_nop Z.add N.add).
    apply N2Z.inj_add.
    intros. apply Z.add_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem sub_sbop:
  forall w n1 n2, n2 < 2^w -> (2^w + n1 - n2) mod 2^w = sbop2 Z.sub w n1 n2.
Proof.
  intros.
  unfold sbop2. erewrite <- N.mod_mod, <- ofZ_mod_pow2; [| reflexivity | apply N.pow_nonzero; discriminate ].
  set (x := (_-_) mod _). set (y := ((_-_) mod _)%Z). pattern n1, n2 in x. pattern (toZ w n1), (toZ w n2) in y. subst x y.
  apply nop_sbop2.

    rewrite N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
    rewrite N2Z.inj_sub by (etransitivity; [ apply N.lt_le_incl, H | apply N.le_add_r ]).
    rewrite N2Z.inj_add, <- Z.add_sub_assoc, <- Zplus_mod_idemp_l, Z.mod_same, Z.add_0_l, N2Z.inj_pow.
      reflexivity.
      rewrite N2Z.inj_pow. apply Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.

    intros. rewrite <- Zminus_mod. reflexivity.
Qed.

Theorem ofZ_sub:
  forall w z1 z2, ofZ w (z1 - z2) = (2^w + ofZ w z1 - ofZ w z2) mod 2^w.
Proof.
  intros.
  rewrite <- N.mod_mod, <- (ofZ_mod_pow2 w _ (_-_)); [| reflexivity | apply N.pow_nonzero; discriminate ].
  set (x := (_ - _) mod _). set (y := (_ mod _)%Z). pattern (ofZ w z1), (ofZ w z2) in x. pattern z1, z2 in y. subst x y.
  apply ofZ_zop2.

    rewrite N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
    rewrite N2Z.inj_sub by (etransitivity; [ apply N.lt_le_incl, ofZ_bound | apply N.le_add_r ]).
    rewrite N2Z.inj_add, <- Z.add_sub_assoc, <- Zplus_mod_idemp_l, Z.mod_same, Z.add_0_l, N2Z.inj_pow.
      reflexivity.
      rewrite N2Z.inj_pow. apply Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.

    intros. rewrite <- Zminus_mod. reflexivity.
Qed.

Theorem toZ_sub:
  forall w n1 n2 (LE: n2 <= n1),
  toZ w (n1 - n2) = canonicalZ (Z.of_N w) (toZ w n1 - toZ w n2).
Proof.
  intros. apply (toZ_nop Z.sub N.sub).
    apply N2Z.inj_sub, LE.
    intros. apply Zminus_mod.
Qed.

Theorem neg_sbop:
  forall w n, n < 2^w -> (2^w - n) mod 2^w = ofZ w (- toZ w n).
Proof.
  intros. rewrite <- (N.add_0_r (2^w)) at 1. rewrite <- Z.sub_0_l, <- (toZ_0_r w).
  apply sub_sbop. assumption.
Qed.

Theorem ofZ_neg:
  forall w z, ofZ w (-z) = (2^w - ofZ w z) mod 2^w.
Proof.
  intros. rewrite <- (N.add_0_r (2^w)) at 1. rewrite <- Z.sub_0_l, <- (ofZ_0_r w).
  apply ofZ_sub.
Qed.

Theorem mul_sbop:
  forall w n1 n2, (n1 * n2) mod 2^w = sbop2 Z.mul w n1 n2.
Proof.
  intros. apply nop_sbop2.
    apply N2Z.inj_mul.
    intros. apply Z.mul_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem ofZ_mul:
  forall w z1 z2, ofZ w (z1 * z2) = (ofZ w z1 * ofZ w z2) mod 2^w.
Proof.
  intros. apply ofZ_zop2.
    apply N2Z.inj_mul.
    intros. apply Z.mul_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Theorem toZ_mul:
  forall w n1 n2, toZ w (n1 * n2) = canonicalZ (Z.of_N w) (toZ w n1 * toZ w n2).
Proof.
  intros. apply (toZ_nop Z.mul N.mul).
    apply N2Z.inj_mul.
    intros. apply Z.mul_mod, Z.pow_nonzero. discriminate. apply N2Z.is_nonneg.
Qed.

Remark Z_div_nonneg:
  forall a b, ((0 <= a) -> (0 <= b) -> (0 <= a / b))%Z.
Proof.
  intros a b H1 H2. apply Z.le_lteq in H2. destruct H2 as [H2|H2].
    apply Z.div_pos; assumption.
    subst b. destruct a; reflexivity.
Qed.

Remark N_div_le:
  forall a b, a / b <= a.
Proof.
  intros. destruct b as [|b].
    destruct a; apply N.le_0_l.
    apply N.div_le_upper_bound.
      discriminate.
      rewrite <- (N.mul_1_l a) at 1. apply N.mul_le_mono_r. destruct b; discriminate.
Qed.

Theorem div_sbop:
  forall w n1 n2, (n1 / n2) mod 2^w = ofZ w (Z.of_N n1 / Z.of_N n2).
Proof.
  intros. unfold ofZ. rewrite Z2N.inj_mod.
    rewrite Z2N.inj_div, Z2N.inj_pow, !N2Z.id by first [ apply N2Z.is_nonneg | discriminate ]. reflexivity.
    apply Z_div_nonneg; apply N2Z.is_nonneg.
    apply Z.pow_nonneg. discriminate.
Qed.

Corollary div_sbop':
  forall w n1 n2, n1 < 2^w -> n1 / n2 = ofZ w (Z.of_N n1 / Z.of_N n2).
Proof.
  intros. rewrite <- (N.mod_small (_/_) (2^w)).
    apply div_sbop.
    eapply N.le_lt_trans. apply N_div_le. apply H.
Qed.

Theorem ofZ_div:
  forall w z1 z2, ofZ w ((z1 mod 2^Z.of_N w) / (z2 mod 2^Z.of_N w)) = (ofZ w z1 / ofZ w z2) mod 2^w.
Proof.
  intros. unfold ofZ.
  rewrite <- Z2N.inj_div by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ]).
  rewrite Z2N.inj_mod.
    rewrite Z2N.inj_pow, N2Z.id. reflexivity. discriminate. apply N2Z.is_nonneg.
    apply Z_div_nonneg; (apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ]).
    apply Z.pow_nonneg. discriminate.
Qed.

Theorem toZ_div:
  forall w n1 n2, toZ w (n1 / n2) = canonicalZ (Z.of_N w) (Z.of_N n1 / Z.of_N n2).
Proof.
  intros. unfold toZ. rewrite N2Z.inj_div. reflexivity.
Qed.

Theorem mod_sbop:
  forall w n1 n2, n2 <> 0 -> (n1 mod n2) mod 2^w = ofZ w ((Z.of_N n1) mod (Z.of_N n2)).
Proof.
  intros. unfold ofZ.
  rewrite !Z2N.inj_mod.
    rewrite Z2N.inj_pow.
      rewrite !N2Z.id. reflexivity.
      discriminate.
      apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
    destruct n2. contradiction. apply N2Z.is_nonneg.
    apply Z.mod_pos_bound. destruct n2. contradiction. reflexivity.
    apply Z.pow_nonneg. discriminate.
Qed.

Corollary mod_sbop':
  forall w n1 n2, 0 < n2 < 2^w -> n1 mod n2 = ofZ w ((Z.of_N n1) mod (Z.of_N n2)).
Proof.
  intros. rewrite <- (N.mod_small (n1 mod n2) (2^w)). apply mod_sbop. apply N.neq_0_lt_0, H.
  etransitivity. apply N.mod_lt, N.neq_0_lt_0, H. apply H.
Qed.

Theorem ofZ_mod:
  forall w z1 z2, (z2 mod 2^Z.of_N w <> 0)%Z ->
  ofZ w ((z1 mod 2^Z.of_N w) mod (z2 mod 2^Z.of_N w)) = ((ofZ w z1) mod (ofZ w z2)).
Proof.
  intros.
  assert (H': (0 < 2^Z.of_N w)%Z). apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
  apply (Z.mod_pos_bound z2), proj1, Z.lt_eq_cases in H'.
  destruct H' as [H'|H']; [| rewrite <- H' in H; contradiction ].
  unfold ofZ. rewrite (Z.mod_small (_ mod _)); [|split]. apply Z2N.inj_mod.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
    apply Z.lt_le_incl, H'.
    apply Z.mod_pos_bound. apply H'.
    etransitivity.
      apply Z.mod_pos_bound. apply H'.
      apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
Qed.

Theorem toZ_mod:
  forall w n1 n2, toZ w (n1 mod n2) = canonicalZ (Z.of_N w) ((Z.of_N n1) mod (Z.of_N n2)).
Proof.
  intros. unfold toZ. rewrite N2Z.inj_mod. reflexivity.
Qed.

Lemma Z_shiftl_eqm:
  forall w z1 z2, (0 <= z2)%Z -> eqm (2^w) (Z.shiftl z1 z2) (Z.shiftl (z1 mod 2^w) z2).
Proof.
  intros. unfold eqm. destruct (Z.neg_nonneg_cases w) as [H1|H1].
    rewrite Z.pow_neg_r, !Zmod_0_r by assumption. reflexivity.

    apply Z.bits_inj'. intros i H2.
    rewrite <- !Z.land_ones, !Z.land_spec, !Z.shiftl_spec, Z.land_spec, !Z.testbit_ones, (proj2 (Z.leb_le 0 i) H2) by assumption.
    destruct (0 <=? i - z2)%Z eqn:H3.
      destruct (i <? w)%Z eqn:H4.
        replace (i - z2 <? w)%Z with true.
          rewrite !Bool.andb_true_r. reflexivity.
          symmetry. rewrite <- (Z.sub_0_r w). apply Z.ltb_lt, Z.sub_lt_le_mono. apply Z.ltb_lt, H4. assumption.
        rewrite !Bool.andb_false_r. reflexivity.
      rewrite Z.testbit_neg_r. reflexivity. apply Z.leb_gt, H3.
Qed.

Theorem shiftl_sbop:
  forall w n1 n2, (N.shiftl n1 n2) mod 2^w = sbop1 Z.shiftl w n1 n2.
Proof.
  intros.
  pose (nop n := N.shiftl n n2). pose (zop z := Z.shiftl z (Z.of_N n2)).
  change (N.shiftl _ _) with (nop n1). unfold sbop1. change (Z.shiftl _ _) with (zop (toZ w n1)).
  apply nop_sbop1. apply N2Z_inj_shiftl. intros. apply Z_shiftl_eqm, N2Z.is_nonneg.
Qed.

Theorem ofZ_shiftl:
  forall w z n, ofZ w (Z.shiftl z (Z.of_N n)) = (N.shiftl (ofZ w z) n) mod 2^w.
Proof.
  intros.
  pose (nop n1 := N.shiftl n1 n). pose (zop z1 := Z.shiftl z1 (Z.of_N n)).
  change (N.shiftl _ _) with (nop (ofZ w z)). change (Z.shiftl _ _) with (zop z).
  apply ofZ_zop1. apply N2Z_inj_shiftl. intro. apply Z_shiftl_eqm, N2Z.is_nonneg.
Qed.

Theorem toZ_shiftl:
  forall w n1 n2, toZ w (N.shiftl n1 n2) = canonicalZ (Z.of_N w) (Z.shiftl (Z.of_N n1) (Z.of_N n2)).
Proof.
  intros. unfold toZ. rewrite N2Z_inj_shiftl. reflexivity. 
Qed.

Theorem shiftr_sbop:
  forall w n1 n2, (N.shiftr n1 n2) mod 2^w = ofZ w (Z.shiftr (Z.of_N n1) (Z.of_N n2)).
Proof.
  intros. unfold ofZ.
  rewrite Z.shiftr_div_pow2 by apply N2Z.is_nonneg.
  rewrite Z2N.inj_mod.

    rewrite Z2N.inj_div; [| apply N2Z.is_nonneg | apply Z.pow_nonneg; discriminate ].
    rewrite !Z2N.inj_pow by first [ discriminate | apply N2Z.is_nonneg ].
    rewrite <- N.shiftr_div_pow2, !N2Z.id. reflexivity.

    apply Z.div_pos. apply N2Z.is_nonneg. apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.

    apply Z.pow_nonneg. discriminate.
Qed.

Theorem ofZ_shiftr:
  forall w z n, ofZ w (Z.shiftr (z mod 2^Z.of_N w) (Z.of_N n)) = (N.shiftr (ofZ w z) n) mod 2^w.
Proof.
  symmetry. rewrite <- N2Z_ofZ. apply shiftr_sbop.
Qed.

Theorem toZ_shiftr:
  forall w n1 n2, toZ w (N.shiftr n1 n2) = canonicalZ (Z.of_N w) (Z.shiftr (Z.of_N n1) (Z.of_N n2)).
Proof.
  intros. unfold toZ. rewrite N2Z_inj_shiftr. reflexivity.
Qed.

Theorem ashiftr_0_w:
  forall n1 n2, ashiftr 0 n1 n2 = 0.
Proof. intros. apply sbop1_0_l. Qed.

Theorem ashiftr_0_l:
  forall w n2, ashiftr w 0 n2 = 0.
Proof.
  intros. unfold ashiftr, sbop1. rewrite toZ_0_r, Z.shiftr_0_l. apply ofZ_0_r.
Qed.

Theorem ashiftr_0_r:
  forall w n1, ashiftr w n1 0 = n1 mod 2^w.
Proof.
  intros. unfold ashiftr, sbop1. rewrite Z.shiftr_0_r. apply ofZ_toZ.
Qed.

Theorem ashiftr_spec:
  forall w n1 n2 i, N.testbit (ashiftr w n1 n2) i = andb (i <? w) (N.testbit n1 (N.min (i + n2) (N.pred w))).
Proof.
  intros. unfold ashiftr, sbop1. destruct w as [|w].
    rewrite ofZ_0_l. destruct i; apply N.bits_0.
    rewrite testbit_ofZ, Z.shiftr_spec by apply N2Z.is_nonneg.
      rewrite <- N2Z.inj_add, testbit_toZ by discriminate. reflexivity.
Qed.

Theorem ashiftr_nonneg:
  forall w n1 n2, n1 mod 2^w < 2^N.pred w -> ashiftr w n1 n2 = N.shiftr (n1 mod 2^w) n2.
Proof.
  symmetry. unfold ashiftr, sbop1.
  rewrite (proj1 (toZ_nonneg w n1) H), <- (N.mod_small (N.shiftr _ _) (2^w)). apply shiftr_sbop.
  rewrite N.shiftr_div_pow2. eapply N.le_lt_trans. apply N_div_le. apply N.mod_lt, N.pow_nonzero. discriminate.
Qed.

Theorem ashiftr_neg:
  forall w n1 n2, 2^N.pred w <= n1 mod 2^w -> ashiftr w n1 n2 = (N.shiftr (N.lor n1 (N.shiftl (N.ones n2) w)) n2) mod 2^w.
Proof.
  symmetry. destruct w as [|w].

    rewrite ashiftr_0_w. apply N.mod_1_r.

    apply N.bits_inj. intro i.
    rewrite ashiftr_spec, <- N.land_ones, N.land_spec, N.shiftr_spec', N.lor_spec, N_ones_spec_ltb, Bool.andb_comm.
    destruct (N.le_gt_cases (i+n2) (N.pred (N.pos w))).
      rewrite N.min_l by assumption. rewrite N.shiftl_spec_low, Bool.orb_false_r. reflexivity.
        eapply N.le_lt_trans. eassumption. apply N.lt_pred_l. discriminate.
      rewrite N.min_r, N.shiftl_spec_high', N_ones_spec_ltb.
        destruct (i <? N.pos w) eqn:H1; [|reflexivity]. replace (_ <? _) with true.
          rewrite Bool.orb_true_r, signbit by discriminate. symmetry. apply Z.ltb_lt. rewrite (proj1 (toZ_neg _ _) H).
            change 2%Z with (Z.of_N 2). rewrite <- N2Z.inj_pow. apply Z.lt_sub_0, N2Z.inj_lt.
            apply N.mod_lt, N.pow_nonzero. discriminate.
          symmetry. eapply N.ltb_lt, N.add_lt_mono_r. rewrite N.sub_add, (N.add_comm n2).
            apply N.add_lt_mono_r. apply N.ltb_lt, H1.
            apply N.lt_pred_le, H0.
        apply N.lt_pred_le, H0.
        apply N.lt_le_incl, H0.
Qed.

Definition N_ashiftr w n1 n2 :=
  (N.shiftr (N.lor (n1 mod 2^w) (if N.testbit n1 (N.pred w) then N.shiftl (N.ones n2) w else 0)) n2) mod 2^w.

Theorem ashiftr_sbop:
  forall w n1 n2, N_ashiftr w n1 n2 = ashiftr w n1 n2.
Proof.
  symmetry. unfold N_ashiftr. destruct w as [|w].
    rewrite N.mod_1_r. apply ashiftr_0_w.
    unfold ashiftr, sbop1. rewrite signbit by discriminate. destruct (_ <? 0)%Z eqn:H.
      rewrite <- toZ_mod_pow2 at 1 by reflexivity. apply ashiftr_neg. rewrite N.mod_mod.
        apply N.nlt_ge. intro H1. apply (proj2 (Bool.not_false_iff_true _) H), Z.ltb_ge, toZ_sign, H1.
        apply N.pow_nonzero. discriminate.
      rewrite N.lor_0_r, N.mod_small.
        apply ashiftr_nonneg, toZ_sign, Z.ltb_ge, H.
        rewrite N.shiftr_div_pow2. eapply N.le_lt_trans. apply N_div_le. apply N.mod_lt, N.pow_nonzero. discriminate.
Qed.

Corollary ofZ_ashiftr:
  forall w z n, ofZ w (Z.shiftr (canonicalZ (Z.of_N w) z) (Z.of_N n)) = N_ashiftr w (ofZ w z) n.
Proof.
  symmetry. rewrite ashiftr_sbop. erewrite <- toZ_ofZ_canonicalZ; reflexivity.
Qed.

Theorem land_sbop:
  forall w n1 n2, (N.land n1 n2) mod 2^w = sbop2 Z.land w n1 n2.
Proof.
  intros. apply nop_sbop2.
    apply N2Z_inj_land.
    symmetry. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite Z.land_assoc, (Z.land_comm _ z2), <- !Z.land_assoc, !Z.land_diag, !Z.land_assoc, (Z.land_comm z2 z1).
      reflexivity.
Qed.

Theorem ofZ_land:
  forall w z1 z2, ofZ w (Z.land z1 z2) = N.land (ofZ w z1) (ofZ w z2).
Proof.
  intros. rewrite <- (N.mod_small (N.land _ _) (2^w)). apply ofZ_zop2.
    apply N2Z_inj_land.
    symmetry. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite Z.land_assoc, (Z.land_comm _ z2), <- !Z.land_assoc, !Z.land_diag, !Z.land_assoc, (Z.land_comm z2 z1).
      reflexivity.
    apply hibits_zero_bound. intros. rewrite N.land_spec, testbit_ofZ, (proj2 (N.ltb_ge b w) H). reflexivity.
Qed.

Theorem toZ_land:
  forall w n1 n2, toZ w (N.land n1 n2) = Z.land (toZ w n1) (toZ w n2).
Proof.
  intros. rewrite <- (canonicalZ_id w (Z.of_N w) (Z.land _ _)).
    apply (toZ_nop Z.land N.land).
      apply N2Z_inj_land.
      intros. rewrite <- !Z.land_ones by apply N2Z.is_nonneg. rewrite (Z.land_comm z1 (Z.ones _)), <- !Z.land_assoc,
        (Z.land_comm (Z.ones _)), <- !Z.land_assoc, !Z.land_diag. reflexivity.
    rewrite N2Z.id. reflexivity.
    apply hibits_signed_range. intros. rewrite !Z.land_spec.
      repeat rewrite (signed_range_hibits i w _ (toZ_bounds w _) H). reflexivity.
Qed.

Theorem lor_sbop:
  forall w n1 n2, (N.lor n1 n2) mod 2^w = sbop2 Z.lor w n1 n2.
Proof.
  intros. apply nop_sbop2.
    apply N2Z_inj_lor.
    symmetry. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite Z.land_lor_distr_l, <- !Z.land_assoc, Z.land_diag. symmetry. apply Z.land_lor_distr_l.
Qed.

Theorem ofZ_lor:
  forall w z1 z2, ofZ w (Z.lor z1 z2) = N.lor (ofZ w z1) (ofZ w z2).
Proof.
  intros. rewrite <- (N.mod_small (N.lor _ _) (2^w)). apply ofZ_zop2.
    apply N2Z_inj_lor.
    symmetry. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite Z.land_lor_distr_l, <- !Z.land_assoc, Z.land_diag. symmetry. apply Z.land_lor_distr_l.
    apply hibits_zero_bound. intros. rewrite !N.lor_spec, !testbit_ofZ, (proj2 (N.ltb_ge b w) H). reflexivity.
Qed.

Theorem toZ_lor:
  forall w n1 n2, toZ w (N.lor n1 n2) = Z.lor (toZ w n1) (toZ w n2).
Proof.
  intros. rewrite <- (canonicalZ_id w (Z.of_N w) (Z.lor _ _)).
    apply (toZ_nop Z.lor N.lor).
      apply N2Z_inj_lor.
      intros. rewrite <- !Z.land_ones, <- Z.land_lor_distr_l, <- Z.land_assoc, Z.land_diag by apply N2Z.is_nonneg.
        reflexivity.
    rewrite N2Z.id. reflexivity.
    apply hibits_signed_range. intros. rewrite !Z.lor_spec.
      repeat erewrite (signed_range_hibits i w _ (toZ_bounds w _) H). reflexivity.
Qed.

Theorem lxor_sbop:
  forall w n1 n2, (N.lxor n1 n2) mod 2^w = sbop2 Z.lxor w n1 n2.
Proof.
  intros. apply nop_sbop2.
    apply N2Z_inj_lxor.
    intros. apply Z.bits_inj. intro i. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. repeat destruct (Z.testbit _ _); reflexivity.
Qed.

Theorem ofZ_lxor:
  forall w z1 z2, ofZ w (Z.lxor z1 z2) = N.lxor (ofZ w z1) (ofZ w z2).
Proof.
  intros. rewrite <- (N.mod_small (N.lxor _ _) (2^w)). apply ofZ_zop2.
    apply N2Z_inj_lxor.
    intros. apply Z.bits_inj. intro i. rewrite <- !Z.land_ones by apply N2Z.is_nonneg.
      rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. repeat destruct (Z.testbit _ _); reflexivity.
    apply hibits_zero_bound. intros. rewrite !N.lxor_spec, !testbit_ofZ, (proj2 (N.ltb_ge b w) H). reflexivity.
Qed.

Theorem toZ_lxor:
  forall w n1 n2, toZ w (N.lxor n1 n2) = Z.lxor (toZ w n1) (toZ w n2).
Proof.
  intros. rewrite <- (canonicalZ_id w (Z.of_N w) (Z.lxor _ _)).
    apply (toZ_nop Z.lxor N.lxor). apply N2Z_inj_lxor.
      intros. apply Z.bits_inj'. intros i H1.
      rewrite <- !Z.land_ones, !Z.land_spec, !Z.lxor_spec, !Z.land_spec by apply N2Z.is_nonneg.
      destruct (Z.lt_ge_cases i (Z.of_N w)) as [H2|H2].
        rewrite Z.ones_spec_low.
          rewrite !Bool.andb_true_r. reflexivity.
          split. exact H1. exact H2.
        rewrite Z.ones_spec_high.
          rewrite !Bool.andb_false_r. reflexivity.
          split. apply N2Z.is_nonneg. exact H2.  
    rewrite N2Z.id. reflexivity.
    apply hibits_signed_range. intros. rewrite !Z.lxor_spec.
      repeat erewrite (signed_range_hibits i w _ (toZ_bounds w _) H). reflexivity.
Qed.

Theorem lnot_sbop:
  forall w n, (N.lnot n w) mod 2^w = ofZ w (Z.lnot (toZ w n)).
Proof.
  intros. destruct w as [|w].
    rewrite ofZ_0_l. apply N.mod_1_r.
    apply N.bits_inj. intro i. unfold N.lnot.
      rewrite <- N.land_ones, N.land_spec, N.lxor_spec, testbit_ofZ, Z.lnot_spec by apply N2Z.is_nonneg.
      rewrite testbit_toZ, N_ones_spec_ltb, Bool.andb_comm by discriminate.
      destruct (i <? N.pos w) eqn:H.
        rewrite N.min_l by apply N.lt_le_pred, N.ltb_lt, H. reflexivity.
        reflexivity.
Qed.

Theorem ofZ_lnot:
  forall w z, ofZ w (Z.lnot z) = N.lnot (ofZ w z) w.
Proof.
  intros. apply N.bits_inj. intro b. destruct (N.lt_ge_cases b w).

    rewrite N.lnot_spec_low by assumption.
    rewrite !testbit_ofZ, Z.lnot_spec by apply N2Z.is_nonneg.
    apply N.ltb_lt in H. rewrite H. reflexivity.

    rewrite N.lnot_spec_high by assumption.
    rewrite !testbit_ofZ. apply N.ltb_ge in H. rewrite H. reflexivity.
Qed.

Theorem toZ_lnot:
  forall w n, w <> 0 -> toZ w (N.lnot n w) = Z.lnot (toZ w n).
Proof.
  intros. apply Z.bits_inj'. intros b H1. rewrite <- (Z2N.id _ H1).
  destruct (N.lt_ge_cases (Z.to_N b) w) as [H2|H2].
    rewrite Z.lnot_spec by apply N2Z.is_nonneg. rewrite !testbit_toZ by exact H. rewrite N.min_l.
      rewrite N.lnot_spec_low by assumption. reflexivity.
      apply N.lt_le_pred. assumption.
    rewrite Z.lnot_spec by apply N2Z.is_nonneg. rewrite !testbit_toZ by exact H. rewrite N.min_r.
      rewrite N.lnot_spec_low. reflexivity. apply N.lt_pred_l, H.
      transitivity w. apply N.le_pred_l. apply H2.
Qed.

Theorem eqb_sbop:
  forall w n1 n2, N.eqb (n1 mod 2^w) (n2 mod 2^w) = Z.eqb (toZ w n1) (toZ w n2).
Proof.
  intros. rewrite <- (toZ_mod_pow2 w _ n1), <- (toZ_mod_pow2 w _ n2) by reflexivity.
  destruct (N.eq_dec (n1 mod 2^w) (n2 mod 2^w)).
    rewrite e. rewrite Z.eqb_refl. apply N.eqb_refl.
    rewrite (proj2 (N.eqb_neq _ _) n). symmetry. apply Z.eqb_neq. intro H. apply n, (toZ_inj w).
      apply N.mod_lt, N.pow_nonzero. discriminate.
      apply N.mod_lt, N.pow_nonzero. discriminate.
      exact H.
Qed.

Theorem eqb_ofZ:
  forall w z1 z2, N.eqb (ofZ w z1) (ofZ w z2) = (Z.eqb (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w))%Z.
Proof.
  intros. unfold ofZ. destruct (Z.eq_dec (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w)).
    rewrite e. rewrite Z.eqb_refl. apply N.eqb_refl.
    rewrite (proj2 (Z.eqb_neq _ _) n). apply N.eqb_neq. intro H. apply n, Z2N.inj.
      apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
      apply Z.mod_pos_bound, Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
      exact H.
Qed.

Theorem ltb_sbop:
  forall w n1 n2, N.ltb ((n1 + 2^N.pred w) mod 2^w) ((n2 + 2^N.pred w) mod 2^w) = Z.ltb (toZ w n1) (toZ w n2).
Proof.
  intros. destruct w as [|w]. rewrite !toZ_0_l, !N.mod_1_r. reflexivity.
  unfold toZ, canonicalZ. change 2%Z with (Z.of_N 2).
  rewrite <- N2Z.inj_pred, <- !N2Z.inj_pow, <- !N2Z.inj_add by reflexivity.
  rewrite <- !N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  assert (H: forall x y z, ((x-y <? z-y) = (x <? z))%Z). intros. destruct (x <? z)%Z eqn:H.
    apply Z.ltb_lt, Z.sub_lt_mono_r, Z.ltb_lt, H.
    apply Z.ltb_ge, Z.sub_le_mono_r, Z.ltb_ge, H.
  rewrite !H, N2Z_inj_ltb. reflexivity.
Qed.

Theorem ltb_ofZ:
  forall w z1 z2, N.ltb (ofZ w z1) (ofZ w z2) = (Z.ltb (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w))%Z.
Proof.
  intros. unfold ofZ. destruct (_ <? _)%Z eqn:H.
    apply N.ltb_lt, Z2N.inj_lt; [ apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ].. |].
      apply Z.ltb_lt, H.
    apply N.ltb_ge, Z2N.inj_le; [ apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ].. |].
      apply Z.ltb_ge, H.
Qed.

Theorem leb_sbop:
  forall w n1 n2, N.leb ((n1 + 2^N.pred w) mod 2^w) ((n2 + 2^N.pred w) mod 2^w) = Z.leb (toZ w n1) (toZ w n2).
Proof.
  intros. destruct w as [|w]. rewrite !toZ_0_l, !N.mod_1_r. reflexivity.
  unfold toZ, canonicalZ. change 2%Z with (Z.of_N 2).
  rewrite <- N2Z.inj_pred, <- !N2Z.inj_pow, <- !N2Z.inj_add by reflexivity.
  rewrite <- !N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
  assert (H: forall x y z, ((x-y <=? z-y) = (x <=? z))%Z). intros. destruct (x <=? z)%Z eqn:H.
    apply Z.leb_le, Z.sub_le_mono_r, Z.leb_le, H.
    apply Z.leb_gt, Z.sub_lt_mono_r, Z.leb_gt, H.
  rewrite !H, N2Z_inj_leb. reflexivity.
Qed.

Theorem leb_ofZ:
  forall w z1 z2, N.leb (ofZ w z1) (ofZ w z2) = (Z.leb (z1 mod 2^Z.of_N w) (z2 mod 2^Z.of_N w))%Z.
Proof.
  intros. unfold ofZ. destruct (_ <=? _)%Z eqn:H.
    apply N.leb_le, Z2N.inj_le; [ apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ].. |].
      apply Z.leb_le, H.
    apply N.leb_gt, Z2N.inj_lt; [ apply Z.mod_pos_bound, Z.pow_pos_nonneg; [ reflexivity | apply N2Z.is_nonneg ].. |].
      apply Z.leb_gt, H.
Qed.

Theorem xbits_ofZ:
  forall w z i j, xbits (ofZ w z) i j = Z.to_N (Z_xbits z (Z.of_N i) (Z.of_N (N.min j w))).
Proof.
  intros. apply N.bits_inj. intro b.
  rewrite <- (N2Z.id b) at 2. rewrite <- Z2N.inj_testbit by apply N2Z.is_nonneg. rewrite Z2N.id.
    rewrite xbits_spec, testbit_ofZ, Z_xbits_spec, <- N2Z.inj_add, N2Z_inj_ltb, Zle_imp_le_bool,
            Bool.andb_true_r, Bool.andb_comm, Bool.andb_assoc, Bool.andb_comm by apply N2Z.is_nonneg.
            apply f_equal. destruct (_ <? N.min _ _) eqn:H.
      apply N.ltb_lt, N.min_glb_lt_iff in H. destruct H. rewrite !(proj2 (N.ltb_lt _ _)) by assumption. reflexivity.
      apply N.ltb_ge, N.min_le in H. destruct H as [H|H]; apply N.ltb_ge in H; rewrite H.
        reflexivity.
        apply Bool.andb_false_r.
    apply Z_xbits_nonneg.
Qed.

Theorem add_mod_same_l:
  forall w n, (2^w + n) mod 2^w = n mod 2^w.
Proof.
  intros.
  rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by (apply N.pow_nonzero; discriminate 1).
  reflexivity.
Qed.

Theorem msub_diag:
  forall w n, (2^w + n - n) mod 2^w = 0.
Proof.
  intros. rewrite N.add_sub. apply N.mod_same, N.pow_nonzero. discriminate 1.
Qed.

Theorem msub_0_r:
  forall w n, (2^w + n - 0) mod 2^w = n mod 2^w.
Proof.
  intros. rewrite N.sub_0_r. apply add_mod_same_l.
Qed.

Theorem msub_add:
  forall w n m, n < 2^w -> (2^w + m - n + n) mod 2^w = m mod 2^w.
Proof.
  intros. rewrite N.sub_add.
    apply add_mod_same_l.
    eapply N.lt_le_incl, N.lt_le_trans. eassumption. apply N.le_add_r.
Qed.

End TwosComplement.



Section BitOps.

Definition bitop_has_spec f g := forall a a' n, N.testbit (f a a') n = g (N.testbit a n) (N.testbit a' n).

Theorem bitop_mod_pow2:
  forall f g (SPEC: bitop_has_spec f g) (PZ: g false false = false),
  forall n1 n2 p, f n1 n2 mod 2^p = f (n1 mod 2^p) (n2 mod 2^p).
Proof.
  intros. rewrite <- !N.land_ones. apply N.bits_inj. intro i. rewrite N.land_spec, !SPEC, !N.land_spec.
  destruct (N.le_gt_cases p i).
    rewrite N.ones_spec_high, !Bool.andb_false_r by assumption. symmetry. apply PZ.
    rewrite N.ones_spec_low, !Bool.andb_true_r by assumption. reflexivity.
Qed.

Definition N_land_mod_pow2 := bitop_mod_pow2 N.land andb N.land_spec (eq_refl false).
Definition N_lor_mod_pow2 := bitop_mod_pow2 N.lor orb N.lor_spec (eq_refl false).
Definition N_lxor_mod_pow2 := bitop_mod_pow2 N.lxor xorb N.lxor_spec (eq_refl false).

Theorem N_mod_mod_pow2_min:
  forall n p1 p2, (n mod 2^p1) mod 2^p2 = n mod 2^N.min p1 p2.
Proof.
  intros. rewrite <- 2!N.land_ones, <- N.land_assoc, N.land_ones. destruct (N.le_gt_cases p2 p1).
    rewrite N.ones_mod_pow2, N.min_r by assumption. apply N.land_ones.
    rewrite N.min_l, N.mod_small. apply N.land_ones.
      rewrite N.ones_equiv. apply N.lt_lt_pred, N.pow_lt_mono_r. reflexivity. assumption.
      apply N.lt_le_incl, H.
Qed.

Theorem N_land_mod_pow2_move:
  forall p x y, N.land (x mod 2^p) y = N.land x (y mod 2^p).
Proof.
  intros.
  rewrite <- N.land_ones, <- N.land_assoc, (N.land_comm _ y), N.land_ones.
  reflexivity.
Qed.

Theorem N_land_mod_pow2_moveout:
  forall p x y, N.land x (y mod 2^p) = (N.land x y) mod 2^p.
Proof.
  intros.
  rewrite N.land_comm, <- N.mod_mod, N_land_mod_pow2_move, N.land_comm by (apply N.pow_nonzero; discriminate).
  symmetry. apply N_land_mod_pow2.
Qed.

Theorem land_mod_min:
  forall p x y, N.land x (y mod 2^p) = N.land (x mod 2^(N.min (N.size y) p)) y.
Proof.
  intros.
  rewrite <- (N.mod_small y (2^N.size y)) at 1 by apply N.size_gt.
  rewrite N_mod_mod_pow2_min.
  symmetry. apply N_land_mod_pow2_move.
Qed.

End BitOps.



Section NInduction.

(* Analogues of theorems about Pos.iter, but for N.iter. *)

Corollary Niter_swap:
  forall n {A} (f: A -> A) x, N.iter n f (f x) = f (N.iter n f x).
Proof. intros. destruct n. reflexivity. apply Pos.iter_swap. Qed.

Corollary Niter_succ:
  forall n {A} (f: A -> A) x, N.iter (N.succ n) f x = f (N.iter n f x).
Proof. intros. destruct n. reflexivity. apply Pos.iter_succ. Qed.

Corollary Niter_invariant:
  forall {A} (Inv: A -> Prop) f x
         (BC: Inv x) (IC: forall x (IH: Inv x), Inv (f x)),
  forall n, Inv (N.iter n f x).
Proof.
  intros. destruct n.
    exact BC.
    simpl. apply Pos.iter_invariant.
      intros. apply IC. assumption.
      exact BC.
Qed.

Corollary Niter_add:
  forall m n {A} (f: A -> A) x,
  N.iter (m+n) f x = N.iter m f (N.iter n f x).
Proof.
  intros. destruct m.
    reflexivity.
    destruct n.
      rewrite N.add_0_r. reflexivity.
      apply Pos.iter_add.
Qed.

End NInduction.



Section InvariantMaps.

(* Sometimes we want to assert that an invariant is present and satisfied, while other times we
   want to more leniently stipulate that an invariant is satisfied if present: *)
Definition true_inv (OP: option Prop) := match OP with Some P => P | None => False end.
Definition trueif_inv (OP: option Prop) := match OP with Some P => P | None => True end.

Lemma trueif_true_inv: forall OP, true_inv OP -> trueif_inv OP.
Proof. unfold true_inv, trueif_inv. intros. destruct OP. assumption. exact I. Qed.

Lemma trueif_some: forall P, trueif_inv (Some P) -> P.
Proof. intros. assumption. Qed.

Lemma trueif_none: trueif_inv None -> True.
Proof. intro. assumption. Qed.

Lemma trueinv_some: forall P, true_inv (Some P) -> P.
Proof. intros. assumption. Qed.

Lemma trueinv_none: ~ true_inv None.
Proof. intro. assumption. Qed.

End InvariantMaps.

(* Tactic "destruct_inv w PRE" divides the inductive case of prove_invs into subgoals,
   one for each invariant point defined by precondition PRE, and puts the goals in
   ascending order by address.  Argument w should be the max bitwidth of addresses to
   consider (e.g., 32 on 32-bit ISAs). *)

Tactic Notation "simpl_trueif" "in" hyp(H) :=
  first [ simple apply trueif_none in H; clear H
        | apply trueif_some in H ].

Tactic Notation "simpl_trueinv" "in" hyp(H) :=
  first [ simple apply trueinv_none in H; exfalso; exact H
        | apply trueinv_some in H ].

Ltac shelve_case H :=
  tryif (simple apply trueinv_none in H) then (exfalso; exact H)
  else tryif (apply trueinv_some in H) then
    (repeat match goal with [ H: true_inv _ |- _ ] => simpl_trueinv in H
                          | [ H: trueif_inv _ |- _ ] => simpl_trueif in H
            end;
     shelve)
  else lazymatch type of H with
  | true_inv (if _ ?a then _ else _) =>
      fail "unable to simplify" H "to an invariant for address" a
  | _ => fail "unable to simplify" H "to an invariant"
  end.

Ltac shelve_cases_loop H a :=
  let g := numgoals in do g (
    (only 1: (case a as [a|a|]; [| |shelve_case H]));
    (unshelve (only 2: shelve; cycle g));
    revgoals; cycle g; revgoals;
    cycle 1
  );
  try (simple apply trueinv_none in H; exfalso; exact H).

Tactic Notation "shelve_cases" int_or_var(i) hyp(H) :=
  lazymatch type of H with true_inv (if ?p ?s ?a then _ else None) =>
    is_var a; case a as [|a]; [ shelve_case H | do i shelve_cases_loop H a ];
    fail "bit width" i "is insufficient to explore the invariant space"
  | _ => fail "hypothesis" H "is not a precondition of the form"
              "(true_inv (if [program] [store] [addr] then [invariant-set] else None))"
  end.

Tactic Notation "destruct_inv" int_or_var(i) hyp(H) :=
  unshelve (shelve_cases i H).

(* Tactic "focus_addr n" brings the goal for the invariant at address n
   to the head of the goal list. *)
Tactic Notation "focus_addr" constr(n) :=
  unshelve (lazymatch goal with |- _ _ _ _ _ (Exit n) _ => shelve
                              | _ => idtac end).



Module Type PICINAE_THEORY (IL: PICINAE_IL).

Import IL.
Open Scope N.

(* Define an alternative inductive principle for structural inductions on stmts
   that works better for proving properties of *executed* stmts that might contain
   repeat-loops.  The cases for all non-repeat forms are the same as Coq's default
   stmt_ind principle, but properties P of repeat-loops are provable from assuming
   that the expansion of the loop into a sequence satisfies P.
 *)
Theorem stmt_ind2 (P: stmt -> Prop):
  P Nop ->
  (forall v e, P (Move v e)) ->
  (forall e, P (Jmp e)) ->
  (forall i, P (Exn i)) ->
  (forall q1 q2 (IHq1: P q1) (IHq2: P q2), P (Seq q1 q2)) ->
  (forall e q1 q2 (IHq1: P q1) (IHq2: P q2), P (If e q1 q2)) ->
  (forall e q (IHq1: P q) (IHq2: forall n, P (N.iter n (Seq q) Nop)), P (Rep e q)) ->
  forall (q:stmt), P q.
Proof.
  intros. induction q.
    assumption.
    apply H0.
    apply H1.
    apply H2.
    apply H3; assumption.
    apply H4; assumption.
    apply H5. assumption. apply Niter_invariant.
      apply H.
      intros. apply H3; assumption.
Qed.


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

(* getmem doesn't read addresses below a, or address at or above a+w. *)
Theorem getmem_frame:
  forall e len m1 m2 a (FR: forall a', (a <= a' < a + len) -> m1 a' = m2 a'),
  getmem e len m1 a = getmem e len m2 a.
Proof.
  intros. revert a FR. induction len using N.peano_ind; intros.
    reflexivity.
    rewrite !getmem_succ. rewrite !IHlen. replace (m2 a) with (m1 a). reflexivity. 
      apply FR. split. reflexivity. apply N.lt_add_pos_r, N.lt_0_succ.
      intros. apply FR. split.
        etransitivity. apply N.le_succ_diag_r. apply H.
        rewrite <- N.add_succ_comm. apply H.
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

Corollary getmem_frame_low:
  forall e1 e2 len1 len2 m a1 a2 v (LT: a1 + len1 <= a2),
  getmem e1 len1 (setmem e2 len2 m a2 v) a1 = getmem e1 len1 m a1.
Proof.
  intros. apply getmem_frame. intros. apply setmem_frame_low. eapply N.lt_le_trans.
    apply H.
    apply LT.
Qed.

Corollary getmem_frame_high:
  forall e1 e2 len1 len2 m a1 a2 v (LT: a2 + len2 <= a1),
  getmem e1 len1 (setmem e2 len2 m a2 v) a1 = getmem e1 len1 m a1.
Proof.
  intros. apply getmem_frame. intros. apply setmem_frame_high. etransitivity.
    apply LT.
    apply H.
Qed.

Lemma shiftr_low_pow2: forall a n, a < 2^n -> N.shiftr a n = 0.
Proof.
  intros. destruct a. apply N.shiftr_0_l.
  apply N.shiftr_eq_0. apply N.log2_lt_pow2. reflexivity. assumption.
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

  exfalso. assumption.
Qed.

Theorem exec_stmt_deterministic:
  forall {h s q s1 x1 s2 x2} (NU: forall_exps_in_stmt not_unknown q)
         (X1: exec_stmt h s q s1 x1) (X2: exec_stmt h s q s2 x2),
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

  apply IHX1.
    destruct NU2. destruct c; assumption.
    assert (H:=eval_exp_deterministic NU1 E E0). injection H; intros; subst. assumption.

  assert (H:=eval_exp_deterministic NU1 E E0). injection H; intros; subst.
  apply IHX1.
    apply Niter_invariant. exact I. split; assumption.
    assumption.
Qed.

Theorem exec_prog_deterministic:
  forall {p a h s n s1 x1 s2 x2} (NU: forall_exps_in_prog not_unknown p)
  (XP1: exec_prog h p a s n s1 x1) (XP2: exec_prog h p a s n s2 x2),
  s1 = s2 /\ x1 = x2.
Proof.
  intros. revert s2 x2 XP2. dependent induction XP1; intros; inversion XP2; subst.

  split; reflexivity.

  rewrite LU in LU0; injection LU0; clear LU0; intros; subst.
  destruct (exec_stmt_deterministic (NU _ _ _ _ LU) XS XS0); subst.
  rewrite EX in EX0; injection EX0; clear EX0; intros; subst.
  apply IHXP1. assumption.

  rewrite LU in LU0; injection LU0; clear LU0; intros; subst.
  destruct (exec_stmt_deterministic (NU _ _ _ _ LU) XS XS0); subst.
  discriminate EX.

  rewrite LU in LU0; injection LU0; clear LU0; intros; subst.
  destruct (exec_stmt_deterministic (NU _ _ _ _ LU) XS XS0); subst.
  discriminate EX.

  rewrite LU in LU0; injection LU0; clear LU0; intros; subst.
  destruct (exec_stmt_deterministic (NU _ _ _ _ LU) XS XS0); injection H0; intro; subst.
  split; reflexivity.
Qed.

End Determinism.


Section Monotonicity.

(* Some monotonicity properties: *)

(* eval_exp, exec_stmt, and exec_prog are monotonic with respect to heaps. *)

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

Theorem exec_stmt_hmono:
  forall h1 h2 s q s' x (HS: h1 ⊆ h2)
         (XS: exec_stmt h1 s q s' x),
  exec_stmt h2 s q s' x.
Proof.
  intros. dependent induction XS; econstructor;
    try eapply eval_exp_hmono; eassumption.
Qed.

Theorem exec_prog_hmono:
  forall h1 h2 p s a n s' x (HS: h1 ⊆ h2)
         (XP: exec_prog h1 p a s n s' x),
  exec_prog h2 p a s n s' x.
Proof.
  intros. revert s a XP. induction n; intros; inversion XP; clear XP; subst.
    apply XDone.
    eapply XStep; try apply PS; try eassumption.
      eapply exec_stmt_hmono; eassumption.
      apply IHn. assumption.
    eapply XAbort; try apply PS; try eassumption.
      eapply exec_stmt_hmono; eassumption.
Qed.

(* exec_prog is monotonic with respect to programs.  Enlarging the space of known
   instructions in memory preserves executions. *)
Theorem exec_prog_pmono:
  forall p1 p2 (PS: forall s, p1 s ⊆ p2 s)
         s h a n s' x (XP: exec_prog h p1 a s n s' x),
  exec_prog h p2 a s n s' x.
Proof.
  intros. dependent induction XP.
    apply XDone.
    eapply XStep; try eassumption.
      erewrite PS. reflexivity. exact LU.
    eapply XAbort; try eassumption.
      erewrite PS. reflexivity. exact LU.
Qed.

End Monotonicity.



Section InvariantProofs.

(* To prove properties of states computed by repeat-loops, it suffices to prove
   that each loop iteration preserves the property. *)
Theorem rep_inv:
  forall (P: store -> Prop)
         h s e q s' x (XS: exec_stmt h s (Rep e q) s' x) (PRE: P s)
         (INV: forall s s' x (PRE: P s) (XS: exec_stmt h s q s' x), P s'),
  P s'.
Proof.
  intros. inversion XS; clear XS; subst.
  clear e w E. revert s PRE XS0. apply Niter_invariant; intros.
    inversion XS0; subst. exact PRE.
    inversion XS0; subst.
      eapply INV; eassumption.
      eapply IH.
        eapply INV. exact PRE. exact XS1.
        exact XS2.
Qed.

(* Append a step to an exec_prog computation. *)
Theorem exec_prog_append:
  forall h p n a s sz q s2 a1 s' x'
         (XP: exec_prog h p a s n s2 (Exit a1))
         (LU: p s2 a1 = Some (sz,q))
         (XS: exec_stmt h s2 q s' x'),
    exec_prog h p a s (S n) s' (match x' with None => Exit (a1+sz)
                                            | Some x' => x' end).
Proof.
  induction n; intros; inversion XP; subst.
    destruct x'; [destruct e|]; econstructor; solve [ eassumption | reflexivity | apply XDone ].
    eapply XStep; try eassumption. eapply IHn; eassumption.
Qed.

(* Split an exec_prog computation into two parts. *)
Theorem exec_prog_split:
  forall h p a s n1 n2 s' x'
         (XP: exec_prog h p a s (n1 + S n2)%nat s' x'),
  exists s1 a1, exec_prog h p a s n1 s1 (Exit a1) /\ exec_prog h p a1 s1 (S n2) s' x'.
Proof.
  intros. revert n2 XP. induction n1; intros.
    exists s,a. split. apply XDone. exact XP.
    rewrite Nat.add_succ_comm in XP. destruct (IHn1 _ XP) as [s1 [a1 [XP1 XP2]]]. inversion XP2; subst. exists s2,a'. split.
      eapply exec_prog_append in XP1; [|exact LU | exact XS]. destruct x1 as [e|]; [destruct e|].
        injection EX as; subst. exact XP1.
        discriminate EX.
        injection EX as; subst. exact XP1.
      assumption.
Qed.

(* Concatenate two exec_prog comptations into one whole. *)
Theorem exec_prog_concat:
  forall h p a s n1 n2 s1 a1 s' x'
         (XP1: exec_prog h p a s n1 s1 (Exit a1)) (XP2: exec_prog h p a1 s1 n2 s' x'),
  exec_prog h p a s (n1 + n2)%nat s' x'.
Proof.
  intros. revert n2 s1 a1 XP1 XP2. induction n1; intros.
    inversion XP1; subst. exact XP2.
    rewrite <- Nat.add_1_r in XP1. apply exec_prog_split in XP1. destruct XP1 as [s2 [a2 [XP0 XP1]]]. rewrite Nat.add_succ_comm. eapply IHn1.
     exact XP0.
     inversion XP1; subst.
       eapply XStep. exact LU. exact XS. exact EX. inversion XP; subst. exact XP2.
Qed.

(* To prove that a property holds at the conclusion of a program's execution, it suffices
   to prove that the property is preserved by every statement in the program. *)
Theorem prog_inv_universal:
  forall (P: exit -> store -> Prop) h p a0 s0 n s' x' (XP: exec_prog h p a0 s0 n s' x')
         (PRE: P (Exit a0) s0)
         (INV: forall a1 s1 sz q s1' x1 (IL: p s1 a1 = Some (sz,q)) (PRE: P (Exit a1) s1)
                      (XS: exec_stmt h s1 q s1' x1),
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
    specialize (INV _ _ _ _ _ _ LU PRE XS). exact INV.
Qed.

(* Alternatively, one may prove that the property is preserved by all the reachable statements.
   (The user's invariant may adopt a precondition of False for unreachable statements.) *)
Theorem prog_inv_reachable:
  forall (P: exit -> store -> nat -> Prop) h p a0 s0 n s' x' (XP: exec_prog h p a0 s0 n s' x')
         (PRE: P (Exit a0) s0 O)
         (INV: forall a1 s1 n1 sz q s1' x1
                      (IL: p s1 a1 = Some (sz,q))
                      (PRE: P (Exit a1) s1 n1)
                      (LT: (n1 < n)%nat)
                      (XP: exec_prog h p a0 s0 n1 s1 (Exit a1))
                      (XS: exec_stmt h s1 q s1' x1)
                      (XP': match x1 with None => exec_prog h p (a1+sz) s1' (n - S n1) s' x'
                                        | Some (Exit a2) => exec_prog h p a2 s1' (n - S n1) s' x'
                                        | Some x2 => x'=x2 end),
               P (exitof (a1 + sz) x1) s1' (S n1)),
  P x' s' n.
Proof.
  intros.
  assert (H: exists a1 s1 n2, (n2 <= n)%nat /\
               exec_prog h p a0 s0 (n - n2) s1 (Exit a1) /\ P (Exit a1) s1 (n - n2)%nat /\
               exec_prog h p a1 s1 n2 s' x').
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
          injection EX. intro. subst a'. apply INV. exact XP.
          discriminate EX.
          injection EX. intro. subst a'. apply INV. exact XP.

        destruct n. inversion LE. apply le_S_n in LE. rewrite Nat.sub_succ_l; [|exact LE].
        replace (Exit a') with (exitof (a1 + sz) x1).
          eapply exec_prog_append. exact XP1. exact LU. exact XS.

        exact XP.
      specialize (INV _ _ (n-1)%nat _ _ _ _ LU PRE1 (Nat.sub_lt n 1 LE Nat.lt_0_1) XP1 XS).
      rewrite minus_Sn_m, Nat.sub_succ, Nat.sub_0_r in INV by exact LE.
      apply INV. reflexivity.
Qed.

(* Rather than assigning and proving an invariant at every machine instruction, we can generalize
   the above to allow users to assign invariants to only a few machine instructions.  To prove that
   all the invariants are satisfied, the user can prove that any execution that starts in an
   invariant-satisfying state and that reaches another invariant always satisfies the latter. *)

(* The "next invariant" property is true if the computation always eventually
   reaches a "next" invariant, and in a state that satisfies that invariant.
   (If the computation is already at an invariant, it is considered its own "next"
   invariant if parameter b=true; otherwise the computation must take at least
   one step before it can satisfy the "next invariant" property.) *)
Inductive nextinv PS p h: bool -> exit -> store -> Prop :=
| NIHere x s (TRU: true_inv (PS p x s)):
    nextinv PS p h true x s
| NIStep (b:bool) s a
         (NOI: (if b then PS p (Exit a) s else None) = None)
         (STEP: forall sz q s1 x1
                       (IL: p s a = Some (sz,q)) (XS: exec_stmt h s q s1 x1),
                nextinv PS p h true (exitof (a+sz) x1) s1):
    nextinv PS p h b (Exit a) s.

(* Proving the "next invariant satisfied" property for all invariant points proves partial
   correctness of the program. *)
Theorem prog_inv:
  forall h p a0 s0 n PS s' x'
         (XP: exec_prog h p a0 s0 n s' x')
         (PRE: true_inv (PS p (Exit a0) s0))
         (INV: forall a1 s1 n1
                      (XP: exec_prog h p a0 s0 n1 s1 (Exit a1))
                      (PRE: true_inv (PS p (Exit a1) s1)),
               nextinv PS p h false (Exit a1) s1),
  trueif_inv (PS p x' s').
Proof.
  intros.
  assert (NI: nextinv PS p h true x' s').
    pattern x', s', n. eapply prog_inv_reachable.
      exact XP.
      apply NIHere. exact PRE.
      intros. inversion PRE0; subst.
        eapply INV in TRU.
          inversion TRU; subst. eapply STEP. exact IL. exact XS.
          exact XP0.
        eapply STEP. exact IL. exact XS.
  inversion NI; subst.
    apply trueif_true_inv. exact TRU.
    rewrite NOI. exact I.
Qed.

(* Subroutine invariants can usually be defined in terms of an invariant-set
   (which is a partial map from addresses and stores to invariants) and a
   post-condition (a property of exits and stores).  The post-condition is
   asserted to be satisfied when execution exits the subroutine either by
   raising an exception or reaching an address outside the subroutine. *)
Definition invs PS Q (p:program) x (s:store) : option Prop :=
  match x with
  | Exit a => match p s a with None => Some (Q x s) | Some _ => PS a s end
  | Raise _ => Some (Q x s)
  end.

(* The following lemmas apply-and-simplify the NIHere rule in tactics. *)
Lemma nextinv_here:
  forall P (PS: program -> exit -> store -> option Prop) p h x s
         (INV: PS p x s = Some P) (TRU: P),
  nextinv PS p h true x s.
Proof. intros. apply NIHere. rewrite INV. exact TRU. Qed.

Lemma nextinv_ret:
  forall PS (Q: exit -> store -> Prop) p h r s
         (IL: p s r = None) (POST: Q (Exit r) s),
  nextinv (invs PS Q) p h true (Exit r) s.
Proof. intros. apply NIHere. unfold invs. rewrite IL. exact POST. Qed.

Lemma nextinv_exn:
  forall PS (Q: exit -> store -> Prop) p h i s
         (POST: Q (Raise i) s),
  nextinv (invs PS Q) p h true (Raise i) s.
Proof. intros. apply NIHere. exact POST. Qed.

(* To prove a subroutine invariant, it suffices to prove that
   (1) the invariant-set is satisfied on entry (precondition), and
   (2) starting at any invariant point in the subroutine always yields a trace
       that reaches another invariant point and satisfies its invariant. *)
Theorem prove_invs:
  forall h a0 s0 PS Q p x s' n
    (XP0: exec_prog h p a0 s0 n s' x)
    (PRE: true_inv (invs PS Q p (Exit a0) s0))
    (CASES: forall a1 s1 n1
      (XP: exec_prog h p a0 s0 n1 s1 (Exit a1))
      (PRE: true_inv (if p s1 a1 then PS a1 s1 else None)),
      nextinv (invs PS Q) p h false (Exit a1) s1),
  trueif_inv (invs PS Q p x s').
Proof.
  intros. eapply prog_inv. exact XP0. exact PRE.
  intros. unfold invs in PRE0. destruct (p s1 a1) eqn:PA1.
    eapply CASES. exact XP. rewrite PA1. exact PRE0.
    apply NIStep. reflexivity. intros. rewrite PA1 in IL. discriminate IL.
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
  forall v h q (NA: noassign v q) (s s':store) x,
  exec_stmt h s q s' x -> s' v = s v.
Proof.
  induction q; intros; inversion H; subst; try reflexivity.
    inversion NA; subst. apply update_frame, not_eq_sym. assumption.
    eapply IHq1; try eassumption. inversion NA. assumption.
    inversion NA. transitivity (s2 v); [ eapply IHq2 | eapply IHq1 ]; eassumption.
    inversion NA. destruct c; [ eapply IHq2 | eapply IHq1 ]; eassumption.

    pattern s'. eapply rep_inv.
      eassumption.
      reflexivity.
      intros. rewrite <- PRE. eapply IHq. inversion NA. assumption. eassumption.
Qed.

Theorem noassign_prog_same:
  forall v h p (NA: prog_noassign v p) s' x
         n a s (EP: exec_prog h p a s n s' x),
  s' v = s v.
Proof.
  intros. pattern x, s'. eapply prog_inv_universal.
    exact EP.
    reflexivity.
    intros. rewrite <- PRE. apply (noassign_stmt_same v) in XS.
      exact XS.
      specialize (NA s1 a1). rewrite IL in NA. exact NA.
Qed.

End FrameTheorems.

(* Prove a goal of the form (prog_noassign v p) for a program p that contains no
   statements having assignments to v. *)
Ltac prove_noassign :=
  try lazymatch goal with [ |- prog_noassign _ _ ] => let a := fresh "a" in
    let s := fresh "s" in let a := fresh "a" in intros s a; destruct a as [|a];
    repeat first [ exact I | destruct a as [a|a|] ]
  end;
  repeat lazymatch goal with [ |- _ <> _ ] => discriminate 1
                           | _ => constructor; let g:=numgoals in guard g<=2 end.

End PICINAE_THEORY.


Module PicinaeTheory (IL: PICINAE_IL) <: PICINAE_THEORY IL.
  Include PICINAE_THEORY IL.
End PicinaeTheory.

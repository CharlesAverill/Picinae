Require Import Arith.
Require Import NArith.
Require Import Picinae_armv8.
Require Import Lia.
Require Import Bool.
Require Import Utf8.
Import ARM8Notations.

(* Require Import strspn_arm8. *)
(*Why doesn't regular import without the notations work*)
(* Require Import -(notations) SMTCoq.SMTCoq. *)

Require Import FunctionalExtensionality.
Import ARM8Notations.
Open Scope N.

(* Extract a bit from a bit-array. *)
Definition bit mem (p:addr) (i:N) := xbits (mem Ⓑ[p + (i >> 3)]) (i mod 2^3) (1 + (i mod 2^3)).

(*EDIT: This tests whether a bit is 0 or 1- used in replacement of bit*)
Definition bit_test mem (bmp:addr) (i:N) := (N.testbit (mem Ⓨ[bmp]) (i) = true).

Definition mem_region_unchanged m m' p len :=
  ∀ i, i < len -> m Ⓑ[ p + i ] = m' Ⓑ[ p + i ].

Lemma mem_eq_region_unchanged :
  forall m p len, mem_region_unchanged m m p len.
Proof.
  intros. unfold mem_region_unchanged. intros. reflexivity.
Qed.


Lemma bit_set_preservation_byte:
  forall m a i_set i
  (LTISET : i_set < 8)
  (LTI : i < 8)
  (NEQ : i <> i_set),
  bit (m [Ⓑ  a := m Ⓑ[ a ] .| (1 << i_set) ]) a i = bit m a i.
Proof.
  intros. unfold bit. unfold xbits. psimpl.
  rewrite! N.shiftr_div_pow2, <-!N.testbit_spec'.
  change (m Ⓑ[ a ].| 1 << i_set) with (N.setbit (m Ⓑ[ a ]) i_set).
  rewrite N.setbit_neq;[reflexivity|now symmetry].
Qed.

(* Define what it means for a nil-terminated string to not have internal nils. *)
Definition nilfree mem p len :=
  ∀ i, i < len -> 0 <> mem Ⓑ[ p + i ].

Definition strlen mem p len :=
  nilfree mem p len /\ mem Ⓑ[ p + len ] = 0.

Require Import ZifyN ZifyBool.
Lemma nflen_lt:
  forall m p len z
  (NF: nilfree m p len)
  (Z:  getmem 64 LittleE 1 m z = 0),
  len < 2 ^ 64.
Proof.
  intros. unfold nilfree in NF.
  destruct (N.lt_ge_cases len (2^64)); try lia; try exfalso.
  remember (msub 64 z p) as offset.
  specialize (NF offset). destruct NF.
    unfold msub in *. lia.
    subst offset; psimpl; congruence.
Qed.

Lemma nilfree_grow:
  forall m p len
  (NF: nilfree m p len)
  (NZ: m Ⓑ[ p + len ] <> 0),
  nilfree m p (1+len).
Proof.
  intros.
  intro; intro. unfold nilfree in NF.
  destruct (N.lt_trichotomy i len) as [Lt | [Eq | Gt]]; try lia; clear H.
  - specialize (NF i); apply NF; assumption.
  - subst i. congruence.
Qed.

(* Define a "correct" bit array.

   Note: `nilfree m p __(1+j)__` so that p[j] != 0.

   This makes it so a bitmap never records the null-terminating character
   as an acceptable character which is the behavior used in this implementation
   of strspn. This is practical in this case but may not be in others. *)
Definition bitarray_nstr mem bitmap_ptr str_ptr len : Prop :=
  ∀ i, i < 256 -> (0 < bit mem bitmap_ptr i <->
                  (∃ j, j < len /\ nilfree mem str_ptr (1+j) /\ mem Ⓑ[str_ptr + j] = i)).

(** ∀ i, i < 256 -> (0 < bit mem bitmap_ptr i <->
                  (∃ j, j < len /\ nilfree mem str_ptr (1+j) /\ mem Ⓑ[str_ptr + j] = i)).*)

(* bitmap bit is on iff the string has a corresponding character before or on \0 *)
Definition bitarray_str mem bitmap_ptr str_ptr : Prop :=
  ∀ i, i < 256 -> (0 < bit mem bitmap_ptr i <->
                  (∃ j, nilfree mem str_ptr (1+j) /\ mem Ⓑ[str_ptr ⊕ j] = i)).


Lemma strlen_incr :
  forall mem p len k
    (LEN : strlen mem p len)
    (LE : k <= len)
    (NNULL : mem Ⓑ[ p + k ] <> 0),
     k < len.
Proof.
  intros. unfold strlen in LEN.
  apply N.lt_eq_cases in LE. destruct LE as [LT | EQ]. easy.
  destruct LEN as [NF NIL]. now subst k.
Qed.

Lemma nilfree_le_len :
  forall mem p len k
    (LEN : strlen mem p len)
    (LE  : k <= len),
    nilfree mem p k.
Proof.
  intros.
  unfold strlen in LEN; destruct LEN as [NF _].
  apply N.lt_eq_cases in LE. destruct LE as [LT | EQ].
  (* LT: k < len *)
  unfold nilfree in NF; unfold nilfree. intros. apply NF. lia.
  (* EQ: k = len *)
  now subst k.
Qed.

Theorem strlen_unchanged:
  forall m m' p len
    (MEM : mem_region_unchanged m m' p (N.succ len))
    (STR : strlen m p len),
  strlen m' p len.
Proof.
  unfold strlen, mem_region_unchanged. intros. destruct STR as [NF NIL].
  split. unfold nilfree in *.
  intros i Lt; specialize (MEM i (N.lt_lt_succ_r _ _ Lt)). rewrite <-MEM; now specialize (NF i Lt).
  specialize (MEM len (N.lt_succ_diag_r len)); now rewrite <-MEM.
Qed.

(* IXB_EDIT
added this lemma *)
Lemma nilfree_le_zero:
  forall mem p len j
    (NIL : mem Ⓑ[ p + len ] = 0)
    (NFj : nilfree mem p j),
    j <= len.
Proof.
  unfold nilfree; intros.
  destruct (N.le_gt_cases j len) as [Le | Gt]; [ assumption | exfalso].
  specialize (NFj len). apply NFj. lia. now symmetry.
Qed.


Lemma bit_update_noverlap_simpl:
  forall m bmp acpt acpt_len bmp_i acpt_i char
  (NO : ~ overlap 64 acpt acpt_len bmp 32)
  (LEN : strlen m acpt acpt_len)
  (BMPI : bmp_i < 256)
  (ACPTI : acpt_i < acpt_len)
  (VAL : m Ⓑ[ acpt + acpt_i ] = char),
  m [Ⓨ bmp := (m Ⓨ[ bmp ] .| (1 << (bmp_i mod 256)) )] Ⓑ[ acpt + acpt_i ] = char.
Proof.
  intros. rewrite <-VAL. eapply getmem_noverlap.
  apply noverlap_index_l with (len1:=acpt_len); try (assumption || lia).
Qed.

Lemma Pos_N_succ_comm: forall p, N.pos (Pos.succ p) = N.succ (N.pos p).
Proof. intro; unfold N.succ; reflexivity. Qed.

Lemma Nshiftr_mono:
  forall x1 x2 shift,
  x1 <= x2 -> N.shiftr x1 shift <= N.shiftr x2 shift.
Proof.
  intros. generalize dependent x2. generalize dependent x1.
  induction shift using N.peano_ind; intros; try assumption.
  unfold N.shiftr. destruct (N.succ shift) eqn:Eqn. apply N.neq_succ_0 in Eqn; contradiction.
  destruct shift. simpl in Eqn. destruct p eqn:Eqnp; try simpl in Eqn; try discriminate.
  simpl; apply N.div2_le_mono; assumption.
  rewrite <-Pos_N_succ_comm in Eqn. injection Eqn; intro Eqnp. subst p.
  do 2 rewrite Pos.iter_succ_r.
  unfold N.shiftr in IHshift. apply IHshift, N.div2_le_mono; assumption.
Qed.

Lemma Nshiftl_mono:
  forall x1 x2 shift,
  x1 <= x2 -> N.shiftl x1 shift <= N.shiftl x2 shift.
Proof.
  intros. generalize dependent x2; generalize dependent x1.
  induction shift using N.peano_ind; intros; simpl; try reflexivity.
  (* 0 *)
  unfold N.shiftl. destruct x1 eqn:Eqx1, x2;
    (reflexivity ||
    apply N.le_0_l ||
    (try  rewrite N.le_0_r in H; discriminate  ) ||
    simpl; assumption) .
  (* N.succ shift *)
  unfold N.shiftl. destruct x1 eqn:Eqx1, x2;
    try (reflexivity ||
    apply N.le_0_l ||
    (try  rewrite N.le_0_r in H; discriminate  )) .
  unfold Pos.shiftl. destruct shift eqn:Eqshift. simpl.
  apply N.double_le_mono in H. simpl in H. assumption.
  simpl. unfold N.shiftl in IHshift; specialize (IHshift (N.pos p~0) (N.pos p0~0)); simpl in IHshift.
  apply IHshift in H.
  do 2 rewrite Pos.iter_succ_r; assumption.
Qed.
(*
  The bitmap update doesn't change any of the characters in the accept string.

  m - memory
  bmp - bitmap pointer
  acpt - accept pointer
  acpt_len - the length of the accept string (acpt[acpt_len] = 0)
  bmp_i - the index of the bitmap we're updating. In the code this corresponds
          to `L`
  acpt_i - an index ranging over all of acpt
  char - value of acpt[acpt_i] used to prove it is the same after the update
*)
Lemma bit_update_noverlap:
  forall m bmp acpt acpt_len L char acpt_i any_char
  (NO : ~ overlap 64 acpt acpt_len bmp 32)
  (LEN : strlen m acpt acpt_len)
  (BMPI : m Ⓑ[ acpt + L ] = char)
  (ACPTI : acpt_i < acpt_len)
  (ACPT_RANGE : m Ⓑ[ acpt + acpt_i ] = any_char),
  m [Ⓠ bmp + (char >> 6 << 3) := 1 << char mod 64
      .| m Ⓠ[ bmp + (char >> 6 << 3) ] ] Ⓑ[ acpt + acpt_i ] = any_char.
Proof.
  intros. rewrite <-ACPT_RANGE. eapply getmem_noverlap.
  apply noverlap_index_index with (len1:=acpt_len) (len2:=32).
  all: try (assumption || lia).
  assert (H:char < 256). { rewrite <-BMPI. apply getmem_bound. }
  assert (Htemp: 32 = 24 + 8) by lia. rewrite Htemp; clear Htemp.
  apply N.add_le_mono; try lia.
  apply N.lt_le_pred in H; simpl in H.
  apply (Nshiftr_mono _ _ 6), (Nshiftl_mono _ _ 3) in H. simpl (255 >> 6 << 3) in H.
  assumption.
Qed.


Lemma Nsucc_le__lt:
  forall x a, N.succ x <= a -> x < a.
Proof.
  intros.
  apply N.lt_le_trans with (n:=x) (m:=N.succ x) (p:=a).
  apply N.lt_succ_diag_r.
  assumption.
Qed.

Lemma add_sub_cancel:
  forall x a
    (LE: x <= a),
  x + (a - x) = a.
Proof.
  intro x. induction x using N.peano_ind; intros.
  - destruct a; reflexivity.
  - rewrite N.sub_succ_r.
    remember (Nsucc_le__lt _ _ LE) as LT; clear HeqLT.
    rewrite N.add_succ_comm. rewrite (N.succ_pred_pos (a-x)).
    apply IHx. now apply N.lt_le_incl in LT.
    lia.
Qed.


Lemma Nshiftl_mono_lt_iff:
  forall x1 x2 shift,
  x1 < x2 <-> N.shiftl x1 shift < N.shiftl x2 shift.
Proof.
  split.
  (* -> *)
  generalize dependent x2; generalize dependent x1.
  induction shift using N.peano_ind; intros; simpl; try reflexivity.
  (* 0 *)
  unfold N.shiftl. destruct x1 eqn:Eqx1, x2;
    (reflexivity ||
    apply N.le_0_l ||
    (try  rewrite N.le_0_r in H; discriminate  ) ||
    simpl; assumption) .
  (* N.succ shift *)
  unfold N.shiftl. destruct x1 eqn:Eqx1, x2;
    try (reflexivity ||
    apply N.le_0_l ||
    (try  rewrite N.le_0_r in H; discriminate  )) .
  unfold Pos.shiftl. destruct shift eqn:Eqshift. simpl.
  apply N.double_lt_mono in H. simpl in H. assumption.
  simpl. unfold N.shiftl in IHshift; specialize (IHshift (N.pos p~0) (N.pos p0~0)); simpl in IHshift.
  apply IHshift in H.
  do 2 rewrite Pos.iter_succ_r; assumption.

  (* <- *)
  intro H.
  generalize dependent x2. generalize dependent x1.
  induction shift using N.peano_ind; intros.
  - unfold N.shiftl in H; simpl in H.
    destruct x1; destruct x2; try discriminate; try lia.
  - destruct shift.
    + (* shift = 0 *)
      simpl in H. destruct x1; destruct x2; try discriminate; try lia.
      unfold N.shiftl in H. unfold Pos.shiftl in H. simpl in H.
      unfold N.lt, N.compare, Pos.compare, Pos.compare_cont in H |- *.
      assumption.
    + simpl in H; destruct x1; destruct x2; try discriminate; try lia.
      assert (H2: forall p p2, N.pos p << N.pos (Pos.succ p2) = N.pos p~0 << N.pos p2) by (
        intros x shift; unfold N.shiftl, Pos.shiftl; simpl; now rewrite Pos.iter_succ_r).
      rewrite H2 in H; rewrite H2 in H. now apply IHshift in H.
Qed.

Lemma pos_div2_lt:
  forall x y, (N.pos x~1 < N.pos y~0) \/ (N.pos x~0 < N.pos y~0) -> N.pos x < N.pos y.
Proof.
  intros x. induction x using positive_ind.
  3: intros y [H1 | H0]; repeat (discriminate || reflexivity || destruct y).
  intros.
    destruct y; [
      apply N.lt_trans with (m:=N.pos y~0); try lia
      |
      | destruct H; discriminate].
    destruct H; unfold N.lt, N.compare, Pos.compare, Pos.compare_cont in H |- *; assumption.
    intros.
    destruct y; [
      |
      | destruct H; discriminate].
    destruct H; unfold N.lt, N.compare, Pos.compare, Pos.compare_cont in H |- *; try assumption.
    destruct H; [apply (N.lt_trans (N.pos x~0~0) (N.pos x~0~1) (N.pos y~0~0)) in H; try lia | ].
    now unfold N.lt, N.compare, Pos.compare, Pos.compare_cont in H |- *.
Qed.

Lemma Possucc_inj:
  forall x y, x = y <-> Pos.succ x = Pos.succ y.
Proof.
  intros; split; intros.
    + rewrite H; reflexivity.
    + generalize dependent y. induction x using Pos.peano_ind; intros.
      - repeat (discriminate || reflexivity || destruct y).
      - rewrite <-Pos.add_1_r in H.
        assert (H1: Pos.succ x = (Pos.succ y - 1)%positive). lia.
        rewrite Pos.sub_1_r in H1. now rewrite Pos.pred_succ in H1.
Qed.

Lemma Pospred_inj:
  forall x y, x <> 1%positive -> y <> 1%positive -> x = y <-> Pos.pred x = Pos.pred y.
Proof.
  intros; split; intros.
  + rewrite H1; reflexivity.
  + generalize dependent y. induction x using Pos.peano_ind; intros.
      - repeat (discriminate || reflexivity || contradiction || destruct y).
      - rewrite <-Pos.add_1_r in H.
        assert (H2: Pos.succ x = (Pos.succ y - 1)%positive); try lia.
Qed.

Lemma pos_exp_double:
  forall p, 2 ^ (N.double p) = 4 ^ p.
Proof.
  intro. rewrite N.double_spec.
  apply N.pow_mul_r.
Qed.

Lemma Pos_succ_mul:
  forall a b c, N.pos (a * (Pos.succ b * c)) = N.pos a * (N.pos c + N.pos b * N.pos c).
Proof.
  intros.
  apply N.eq_stepl with (x:=N.pos a * (N.succ (N.pos b) * N.pos c)); try reflexivity.
  assert (H: N.succ (N.pos b) * N.pos c = N.pos c + N.pos b * N.pos c) by lia.
  rewrite H. reflexivity.
Qed.
(*  2 * (Pos.succ x * 2 ^ p)  *)

Lemma Nshiftr_mono_strong:
  forall x y shift,
    x < y * 2 ^ shift -> x >> shift < (y * 2 ^ shift) >> shift.
Proof.
  intros. generalize dependent y. generalize dependent x.
  induction shift using N.strong_induction_le; simpl; intros x y LT.
  (* 0 *)
  assumption.
  (* N.succ shift *)
  rewrite <-?N.shiftl_mul_pow2 in *.
  replace (y << N.succ shift) with ((2*y) * 2^shift) in LT
    by (rewrite N.shiftl_mul_pow2, <-N.add_1_l, N.pow_add_r; lia).
  pose proof (H1:=H shift (N.le_refl _) _ _ LT).
  rewrite <-?N.shiftl_mul_pow2 in *.
  rewrite N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r in *; try lia.
  destruct (N.eq_0_gt_0_cases shift).
    (* shift = 0 *)
    {
      subst. simpl. rewrite N.shiftl_0_r in *.
      unfold N.lt in LT |- *. destruct x. destruct y; (discriminate || apply LT).
      clear - LT.
      destruct y as [|y];[discriminate|].
      replace (2*N.pos y) with (N.pos (xO y)) in LT by lia.
      destruct p; simpl; try reflexivity.
      all: apply POrderedType.Positive_as_DT.compare_lt_iff.
      all: unfold N.compare, Pos.compare in LT; cbn in LT.
        apply Pos.compare_cont_Gt_Lt. assumption.
        apply Pnat.nat_of_P_lt_Lt_compare_morphism in LT. lia.
    }
    (* 0 < shift *)
    replace (2*y) with (y*2^1) in H1; try lia.
    rewrite <-N.le_succ_l in H0; simpl in H0.
    specialize (H _ H0 _ _ H1); clear - H.
    rewrite N.shiftr_shiftr, N.add_1_r, <-N.shiftl_mul_pow2 in H.
    rewrite N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r in H; try lia.
Qed.

(* Useful:
N.succ_inj: ∀ n1 n2 : N, N.succ n1 = N.succ n2 → n1 = n2
N.pow_succ_r': ∀ a b : N, a ^ N.succ b = a * a ^ b
N.pow_mul_r: ∀ a b c : N, a ^ (b * c) = (a ^ b) ^ c
Pos.succ_pred: ∀ p : positive, p ≠ 1%positive → Pos.succ (Pos.pred p) = p
Possucc_inj2
     : ∀ x y : positive, x = y → Pos.succ x = Pos.succ y
Pos_N_succ_comm: ∀ p : positive, N.pos (Pos.succ p) = N.succ (N.pos p)
*)

Theorem setmem_split_swap:
  forall w e i j m a v (LEN: i+j < 2 ^ w), setmem w e (i+j) m a v =
    match e with BigE => setmem w e i (setmem w e j m (a+i) v) a (N.shiftr v (8*j))
               | LittleE => setmem w e i (setmem w e j m (a+i) (N.shiftr v (8*i))) a (v mod 2^(8*i))
    end.
Proof.
  intros. rewrite setmem_split. rewrite setmem_swap. rewrite setmem_swap with (len2:=j).
  rewrite! (N.mul_comm 8 ).
  reflexivity.
  all: apply noverlap_sum; rewrite msub_diag, N.add_0_r; now apply N.lt_le_incl.
Qed.

Corollary msbits_indexed_section_contained:
  forall m n, (m Ⓑ[ n ] >> 6 << 3) + 8 <= 32.
Proof.
  intros.
  change 32 with ((3 << 3) + 8).
  rewrite <- N.add_le_mono_r.
  apply Nshiftl_mono.
  change 3 with (N.pred ((4 * 2^6) >> 6)).
  apply N.lt_le_pred.
  apply Nshiftr_mono_strong. change (4 * 2 ^ 6) with 256.
  apply getmem_bound.
Qed.

Lemma nilfree_lte :
  ∀ mem accept_ptr j len,
  nilfree mem accept_ptr j /\ mem Ⓑ[ accept_ptr + len ] = 0
  -> j <= len.
Proof.
  intros mem accept_ptr j len [J Len].
  unfold nilfree in J.
  specialize (N.le_gt_cases j len); intro Disj.
  destruct Disj as [Lte | Gt].
  assumption.
  specialize J with len. apply J in Gt. rewrite Len in Gt. now contradiction Gt.
Qed.

Lemma nilfree_shrink :
  ∀ mem p x y
    (NILFREE : nilfree mem p x)
    (LT : y < x),
  nilfree mem p y.
Proof.
  intros. unfold nilfree in NILFREE; unfold nilfree.
  intros. apply NILFREE. apply (N.lt_trans i y x); repeat assumption.
Qed.


Lemma bla:
  forall w e m a1 a2 n v,
  msub w a1 a2 > n ->
  msub w a2 a1 > n ->
    getmem w e n (setmem w e n m a2 v) a1 = getmem w e n m a1.
Proof.
  intros.
  apply getmem_noverlap.
  clear - H H0.
  apply sep_noverlap; try (left; lia || right; lia).
Qed.

Lemma getbyte_shiftr8__zero:
  forall w m a, getbyte m a w >> 8 = 0.
Proof.
  intros. Search "bound" "getbyte".
  assert (LT:=getbyte_bound m a w).
  remember (getbyte m a w) as x. clear Heqx.
  now apply shiftr_low_pow2.
  (* vm_compute (_^_) in LT. *)
  (* veriT. - doesn't work... *)
  (*TODO: make this work as an example of using
    verit: intros. unfold getbyte. unfold xbits. verit.*)
Qed.

Lemma brute_bitmap_lookup_eq_bit:
  forall  str_ptr sp m L,
   (m Ⓠ[ sp + (m Ⓑ[ str_ptr + L ] >> 6 << 3) ] >> m Ⓑ[ str_ptr + L ] mod 64) mod 2 =
     bit m sp (m Ⓑ[ str_ptr + L ]).
Proof.
  intros.
  unfold bit.
  assert (BOUND:=getmem_bound 64 LittleE 1 m (str_ptr + L)); change (2 ^ (8 * 1)) with 256 in BOUND.
  remember (m Ⓑ[ str_ptr + L ]) as char. unfold xbits. psimpl.
  destruct char. psimpl; reflexivity.
  repeat (discriminate || destruct p); clear BOUND Heqchar.
  all:psimpl.
  all: try (match goal with
  | [ |- N.shiftr _ ?SHIFT = N.shiftr _ ?S ] =>
        change SHIFT with (7 * 8 + S) ||
        change SHIFT with (6 * 8 + S) ||
        change SHIFT with (5 * 8 + S) ||
        change SHIFT with (4 * 8 + S) ||
        change SHIFT with (3 * 8 + S) ||
        change SHIFT with (2 * 8 + S) ||
        change SHIFT with (1 * 8 + S)
  end; rewrite <-N.shiftr_shiftr; rewrite getmem_shiftr8;
    simpl N.iter; psimpl; reflexivity
  ).
  all: try reflexivity.
  all: try (match goal with
  | [ |- N.modulo (N.shiftr _ ?SHIFT) _ = N.modulo (N.shiftr _ ?S) _ ] =>
        change SHIFT with (7 * 8 + S) ||
        change SHIFT with (6 * 8 + S) ||
        change SHIFT with (5 * 8 + S) ||
        change SHIFT with (4 * 8 + S) ||
        change SHIFT with (3 * 8 + S) ||
        change SHIFT with (2 * 8 + S) ||
        change SHIFT with (1 * 8 + S)
  end; rewrite <-N.shiftr_shiftr; rewrite getmem_shiftr8;
    simpl N.iter; psimpl; reflexivity
  ).
  all: try (match goal with
  | [ |- N.modulo (N.shiftr _ ?SHIFT) _ = N.modulo _ _ ] =>
        change SHIFT with (7 * 8) ||
        change SHIFT with (6 * 8) ||
        change SHIFT with (5 * 8) ||
        change SHIFT with (4 * 8) ||
        change SHIFT with (3 * 8) ||
        change SHIFT with (2 * 8) ||
        change SHIFT with (1 * 8)
  end; rewrite getmem_shiftr8;
    simpl N.iter; psimpl; reflexivity
  ).
Qed.

Lemma map_checker_n_helper:
  forall m bitmap_ptr str_ptr L
  (LOOKUP_HIT : (((m Ⓠ[ bitmap_ptr + (((m Ⓑ[ str_ptr + L ]) >> 6) << 3) ]) >>
        ((m Ⓑ[ str_ptr + L ]) mod 64)) mod 2) ≠ 0)
  ,
  (bit m bitmap_ptr (m Ⓑ[ str_ptr + L ])) = 1.
Proof.
  intros. rewrite brute_bitmap_lookup_eq_bit in LOOKUP_HIT. unfold bit in *.
  psimpl. unfold xbits in *. psimpl. psimpl in LOOKUP_HIT. remember (m Ⓑ[ bitmap_ptr + (m Ⓑ[ str_ptr + L ] >> 3) ] >>
       m Ⓑ[ str_ptr + L ] mod 8) as x. clear - LOOKUP_HIT.
  enough (H: x mod 2 <> 0 -> x mod 2 = 1).
  auto. clear LOOKUP_HIT.

  intros. rewrite <- N.bit0_mod in *. destruct x; try contradiction.
  destruct p; simpl; try (reflexivity || contradiction).
Qed.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                                               *)
(*             Experimental Section              *)
(*                                               *)
(* v v v v v v v v v v v v v v v v v v v v v v v *)


Lemma byte0_bits0:
  ∀ m bp i, i<8 /\ m Ⓑ[ bp ] = 0 -> bit m bp i = 0.
Proof.
  intros. destruct H.
  unfold bit. unfold xbits. psimpl. destruct i.
    psimpl. rewrite H0. psimpl. reflexivity.
    rewrite H0. psimpl. reflexivity.
Qed.

(* ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ *)
(*                                               *)
(*          END OF Experimental Section          *)
(*                                               *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*Beginning of EDIT*)

(*EDIT: These are the new versions of bitarray_nstr and bitarray_str*)
Definition bitarray_nstr_new mem bitmap_ptr str_ptr len : Prop :=
  ∀ i, i < 256 -> (bit_test mem bitmap_ptr i <->
                  (∃ j, j < len /\ nilfree mem str_ptr (1+j) /\ mem Ⓑ[str_ptr + j] = i)).

(* IXB_EDIT
changed the -> to <-> *)
Definition bitarray_str_new mem bitmap_ptr str_ptr : Prop :=
  ∀ i, i < 256 -> (bit_test mem bitmap_ptr i <->
                  (∃ j, nilfree mem str_ptr (1+j) /\ mem Ⓑ[str_ptr ⊕ j] = i)).

(*represent complicated memory*)
Definition changed_mem bitmap_ptr accept_ptr L m:=
  (m [Ⓠ bitmap_ptr + (m Ⓑ[ accept_ptr + L ] >> 6 << 3) := 1 <<
  m Ⓑ[ accept_ptr + L ] mod 64 .| m Ⓠ[ bitmap_ptr + (m Ⓑ[ accept_ptr + L ] >>6 <<3)]]).

(*The following Lemmas help us write the changed memory as
  a change in 256 bits directly.*)

Lemma quad_less_than:
forall m x y
, (64 < y)->
(m Ⓠ[ x ] <  2 ^ y) .
Proof with try nia.
intros.
rewrite getmem_bound; try nia.
psimpl (8*8); try nia.
rewrite <- N.pow_lt_mono_r_iff; try nia.
Qed.

Lemma lor_der_1 :
forall a b c d e,
b .| c .| a.| d .| e = a .| b .| c .| d .| e .
Proof. intros.
do 2 rewrite <- N.lor_assoc.
replace (a .| (d .| e)) with ((d .| e) .| a).
rewrite N.lor_assoc. rewrite <- N.lor_comm.
repeat rewrite N.lor_assoc. reflexivity.

rewrite <- N.lor_comm. reflexivity.
Qed.

Lemma lor_der_2 :
forall a b c d e,
a .| b .| c .| d .| e = b .| c .| d.| a .| e.
Proof.
intros. do 3 rewrite <- N.lor_assoc. rewrite <- N.lor_comm.
do 2 rewrite N.lor_assoc. rewrite <- N.lor_assoc.
replace (e .| a) with (a .| e). rewrite N.lor_assoc. reflexivity.
apply N.lor_comm.
Qed.

Lemma range_eq :
forall k b
(HYP0: k <= 4)
(HYP1: 64*k <= b < 64*(k + 1) )
,
((b >> 6 << 3) = 8*k).
Proof.
intros.  rewrite N.shiftl_mul_pow2. psimpl (2^3). rewrite N.mul_comm.
rewrite N.mul_cancel_l. destruct HYP1. rewrite N.shiftr_div_pow2.
rewrite <- N.mul_cancel_l with (p:= 64). psimpl (2^6).
apply N.div_le_lower_bound with (a:= b) (b:= 64) (q:= k) in H.
apply N.Div0.div_lt_upper_bound in H0.
assert (b / 64 = k).
lia. rewrite H1. reflexivity.
all:lia.

Qed.

Lemma helper_2 :
forall m x y, (64 < y)->
(m Ⓠ[ x ] mod  2 ^ y) = m Ⓠ[ x ] .
Proof.
intros.
rewrite N.mod_small. reflexivity.
rewrite getmem_bound.
 psimpl (8*8).
rewrite <- N.pow_lt_mono_r_iff. assumption. lia.
Qed.

Lemma helper_3 :
forall m a x k
(EQ1: x = 1 \/ x = 2 \/ x =3)
(EQ2: k = 8*x),
(m Ⓠ[ (k) + a ] << 8 * (k)) mod 2 ^ 256 = (m Ⓠ[ (k) + a ] << 8 * (k)).
Proof.
intros.
rewrite EQ2.
rewrite N.mod_small. reflexivity.

rewrite N.mul_assoc. psimpl (8*8).
rewrite N.shiftl_mul_pow2.

destruct EQ1.
rewrite H. psimpl (8*1). psimpl (64*1).
replace (2^256) with (2^192 * 2^64).
rewrite <- N.mul_lt_mono_pos_r with (p:= 2^64).
apply quad_less_than. lia. lia. lia.

destruct H.
rewrite H. psimpl (8*2). psimpl (2^(64*2)).
replace (2^256) with (2^128 * 2^128).
rewrite <- N.mul_lt_mono_pos_r with (p:= 2^128).
apply quad_less_than. lia. lia. lia.

rewrite H. psimpl (8*3). psimpl (2^(64*3)).
replace (2^256) with (2^64 * 2^192).
rewrite <- N.mul_lt_mono_pos_r with (p:= 2^192).
apply getmem_bound. lia. lia.
Qed.

Lemma b_eq :
forall b k
(HYP1: b >> 6 << 3 = 8*k)
(HYP2: 64*k <= b)
(HYP4: b < 256)
,
2 ^ b mod 2 ^ (8 * 32) = 2 ^ (b mod 64) * 2 ^ (8 * 8*k).
Proof.
intros.

psimpl. repeat rewrite N.shiftl_1_l. rewrite <- N.pow_add_r.

assert (forall a b, 2^a = 2^b <-> a = b).
intuition. apply N.pow_inj_r with(a:=2) (b:=a)(c:=b0) in H. assumption. lia.
rewrite H. reflexivity.

assert(2^b < 2^256).
rewrite <- N.pow_lt_mono_r_iff with (a:= 2). assumption. lia.

rewrite H.
replace (b = b mod 64 + 64*k) with (b + 64*k - 64*k = b mod 64 + 64*k).
rewrite N.add_sub_swap with (p:= 64*k).
rewrite N.add_cancel_r.
rewrite N.Div0.mod_eq.
rewrite N.shiftl_mul_pow2 in HYP1. psimpl (2^3) in HYP1. rewrite N.mul_comm in HYP1.
rewrite N.mul_cancel_l in HYP1. rewrite N.shiftr_div_pow2 in HYP1.
psimpl (2^6) in HYP1. rewrite HYP1. reflexivity.
lia. assumption. psimpl (b + 64 * k - 64 * k). reflexivity.

Qed.

Lemma b_eq_2 :
forall b k
(HYP1: b >> 6 << 3 = 8*k)
(HYP2: 64*k <= b)
(HYP4: b < 256)
,
2 ^ b = 2 ^ (b mod 64) * 2 ^ (8 * 8*k).
Proof.
intros.
assert (forall a b, 2^a = 2^b <-> a = b).
intuition. apply N.pow_inj_r with(a:=2) (b:=a)(c:=b0) in H. assumption. lia.
rewrite H. reflexivity. repeat rewrite N.shiftl_1_l. rewrite <- N.pow_add_r.

rewrite H. psimpl (8*8).
replace (b = b mod 64 + 64*k) with (b + 64*k - 64*k = b mod 64 + 64*k).
rewrite N.add_sub_swap with (p:= 64*k).
rewrite N.add_cancel_r.
rewrite N.Div0.mod_eq.
rewrite N.shiftl_mul_pow2 in HYP1. psimpl (2^3) in HYP1. rewrite N.mul_comm in HYP1.
rewrite N.mul_cancel_l in HYP1. rewrite N.shiftr_div_pow2 in HYP1.
psimpl (2^6) in HYP1. rewrite HYP1. reflexivity.
lia. assumption. psimpl (b + 64 * k - 64 * k). reflexivity.
Qed.


(* TODO: Prove this with veriT. *)
Theorem getmem_eq:
  forall  m a b
  (H: b < 256),
    getmem 64 LittleE 32 (setmem 64 LittleE 32 m a (N.setbit (getmem 64 LittleE 32 m (a)) (b)))(a)=
  getmem 64 LittleE 32 (setmem 64 LittleE 8 m (a + (b >> 6 << 3)) (N.setbit (getmem 64 LittleE 8 m (a + (b >> 6 << 3))) (b mod (8*8))))((a))
.
Proof.
intros.
rewrite N.setbit_spec' .
rewrite getmem_setmem.

(*TODO: automate pls*)

replace 32 with (24 + 8).
rewrite getmem_split.
replace 24 with (16 + 8).
rewrite getmem_split.
replace 16 with (8 + 8).
rewrite getmem_split.

replace 32 with (24 + 8).
rewrite getmem_split.
replace 24 with (16 + 8).
rewrite getmem_split.
replace 16 with (8 + 8).
rewrite getmem_split.
psimpl.

repeat rewrite N.setbit_spec'.

assert (b < 256 -> 64*0<= b /\ b < 64*1 \/ (64*1 <= b /\ b <64*2) \/ (64*2 <= b /\ b<64*3) \/ (64*3 <= b /\ b<64*4)). lia.

specialize (H0 H).

destruct H0. inversion H0. apply range_eq in H0.
psimpl (8*0) in H0. rewrite H0. psimpl.

rewrite N.lor_comm.
repeat rewrite N.lor_assoc.
replace (1 << b .| (m Ⓠ[ a ])) with ((m Ⓠ[ a ]).|1 << b).
all: try lia.

repeat rewrite N.shiftl_1_l. rewrite N.mod_small.
(* broken: *) reflexivity.
1-2: try assumption. apply N.lor_comm.
(* TODO: SMT Testing *)
(* Ltac eqbits :=
  repeat match goal with
  | |- eq _ _ => apply N.bits_inj; unfold N.eqf; intro
  | |- context[N.testbit (N.lor ?x ?y)] => rewrite (N.lor_spec x y)
  | [ H: ?x < ?b |- context[?x mod ?b]] => rewrite (N.mod_small x b)
  | [ H: _ <= ?x < ?b |- context[?x mod ?b]] => rewrite (N.mod_small x b)
  | [ H: _ < ?x < ?b |- context[?x mod ?b]] => rewrite (N.mod_small x b)
  | |- context[_ .| (2 ^ ?b)] => rewrite <-N.setbit_spec'
  end; try (easy || lia).
eqbits.
now rewrite N.lor_comm. *)

destruct H0. inversion H0. apply range_eq in H0.
psimpl (8*1) in H0. rewrite H0. psimpl.
repeat rewrite N.shiftl_1_l.
rewrite N.shiftl_lor. rewrite N.lor_assoc.
rewrite N.lor_comm. repeat rewrite N.lor_assoc.
rewrite <- lor_der_1.

rewrite b_eq_2 with (k:=1). psimpl (8*8*1).
rewrite N.shiftl_mul_pow2 with (a:= (2^(b mod 64))) (n:=64). reflexivity. psimpl. assumption.
1-2: assumption. lia.

destruct H0. inversion H0. apply range_eq in H0.
psimpl (8*2) in H0. rewrite H0. psimpl.
repeat rewrite N.shiftl_1_l.
rewrite N.shiftl_lor. rewrite N.lor_assoc. rewrite N.lor_comm. repeat rewrite N.lor_assoc.
rewrite lor_der_2. change (2^7) with 128.
rewrite b_eq_2 with (k:=2). change (8*8*2) with 128.
rewrite N.shiftl_mul_pow2 with (a:= (2^(b mod 64))) (n:=128). reflexivity. 1-3: psimpl; assumption. lia.

pose proof H0. apply range_eq in H0. destruct H1.
psimpl (8*3) in H0. rewrite H0. psimpl.
repeat rewrite N.shiftl_1_l.
rewrite N.shiftl_lor. rewrite N.lor_assoc. change (2^7) with 128.
rewrite b_eq_2 with (k:=3). change (8*8*3) with 192.
rewrite N.shiftl_mul_pow2 with (a:= (2^(b mod 64))) (n:=192). reflexivity. psimpl (8*3). 1-3: try psimpl; assumption. lia.
Qed.

(*Made some small tweaks to the one we already have for greater ease of use*)
Lemma bit_update_noverlap_new:
  forall m bmp acpt acpt_len L acpt_i
  (NO : ~ overlap 64 acpt acpt_len bmp 32)
  (LEN : strlen m acpt acpt_len)
  (ACPTI : acpt_i < acpt_len),
  m [Ⓠ bmp + (m Ⓑ[ acpt + L ]  >> 6 << 3) := 1 << m Ⓑ[ acpt + L ]  mod 64
      .| m Ⓠ[ bmp + (m Ⓑ[ acpt + L ]  >> 6 << 3) ] ] Ⓑ[ acpt + acpt_i ] = m Ⓑ[ acpt + acpt_i ].
Proof.
  intros. eapply getmem_noverlap.
  apply noverlap_index_index with (len1:=acpt_len) (len2:=32).
  all: try (assumption || lia).
  assert (H:(m Ⓑ[ acpt + L ]) < 256). apply getmem_bound.
  assert (Htemp: 32 = 24 + 8) by lia. rewrite Htemp; clear Htemp.
  apply N.add_le_mono; try lia.
  apply N.lt_le_pred in H; simpl in H.
  apply (Nshiftr_mono _ _ 6), (Nshiftl_mono _ _ 3) in H. simpl (255 >> 6 << 3) in H.
  assumption.
Qed.

Lemma nilfree_change :
forall m acpt L bmp acpt_len
(ACPT_SAME : mem_region_unchanged m
(changed_mem bmp acpt L m) acpt acpt_len),
nilfree (changed_mem bmp acpt L m) acpt acpt_len <->  nilfree m acpt acpt_len.
Proof.
intros. intuition. unfold mem_region_unchanged in ACPT_SAME.
unfold nilfree. intros. specialize (ACPT_SAME i H0). rewrite ACPT_SAME. unfold nilfree in H. specialize (H i H0). assumption.
unfold mem_region_unchanged in ACPT_SAME.
unfold nilfree. intros. specialize (ACPT_SAME i H0). rewrite <- ACPT_SAME. unfold nilfree in H. specialize (H i H0). assumption.
Qed.

Lemma acpt_same_shrink:
forall m acpt L bmp acpt_len
(LT_LEN: L < acpt_len),
mem_region_unchanged m
  (changed_mem bmp acpt L m) acpt acpt_len -> mem_region_unchanged m
  (changed_mem bmp acpt L m) acpt L.
Proof.
unfold mem_region_unchanged. intros. assert (i < acpt_len). lia.
specialize (H i H1). assumption.
Qed.

(*changed bitarray_nstr_incr *)
Lemma bitarray_nstr_incr_new:
forall m acpt acpt_len bmp (L : N)
  (ACPT_LEN : strlen m acpt acpt_len)
  (NO : ¬ overlap 64 acpt acpt_len bmp 32)
  (BITNSTR : bitarray_nstr_new m bmp acpt L)
  (BC : m Ⓑ[ acpt + L ] ≠ 0)
  (ACPT_SAME: mem_region_unchanged m (changed_mem bmp acpt L m) acpt acpt_len)
  (L_LT_LEN : L < acpt_len)
,
bitarray_nstr_new (changed_mem bmp acpt L m) bmp acpt (L+1).
Proof.

  unfold bitarray_nstr_new, bit_test.
  intros.

  unfold changed_mem at 1. rewrite testbit_xbits, N.shiftl_1_l, N.lor_comm.

  rewrite <- N.setbit_spec'. rewrite <- getmem_eq.
  rewrite <- testbit_xbits, getmem_setmem.
  psimpl (2 ^ (32 * 8)). rewrite N.setbit_spec', N_lor_mod_pow2, getmem_mod_r, N.mod_small.
  rewrite <- N.setbit_spec'. rewrite N.setbit_iff.

  split; intros.
  destruct H0.

  - specialize (BITNSTR i H).
  exists L. split. lia. split. apply nilfree_grow.
  unfold strlen in ACPT_LEN. destruct ACPT_LEN as [NF ZERO].
  apply nilfree_shrink  with (y:= L) in NF.
  rewrite <- nilfree_change with (bmp:=bmp) (L:= L) in NF.
  assumption. apply acpt_same_shrink in ACPT_SAME. 1-3: assumption.

  rewrite <- ACPT_SAME. 1-2: assumption.
  rewrite <- ACPT_SAME. 1-2: assumption.

  - apply BITNSTR in H0. destruct H0 as [j [H0 [H1 H2]]].
  exists j. split. lia. split. unfold nilfree in H1. unfold nilfree.
  intros. pose proof H3. apply H1 in H3. unfold changed_mem.
  rewrite bit_update_noverlap_new with (bmp:= bmp)(acpt_len:=acpt_len) (acpt_i:= i0).
  assumption.
  assumption. assumption. lia.
  rewrite <- ACPT_SAME. 1-3: try lia.

  - destruct H0 as [j [H0 [H1 H2]]].
  specialize (BITNSTR i H).
  unfold changed_mem in H2.
  rewrite bit_update_noverlap_new with (bmp:= bmp)(acpt_len:=acpt_len) (acpt_i:= j) in H2.

  assert (j < L + 1 -> j = L \/ j < L) by lia.
  specialize (H3 H0). destruct H3.
  left. rewrite H3 in H2. assumption.

  right. apply BITNSTR. exists j. split. assumption.
  split.
    unfold nilfree in H1. unfold nilfree.
    intros. pose proof H4. apply H1 in H4. unfold changed_mem in H4. rewrite bit_update_noverlap_new with (bmp:= bmp)(acpt_len:=acpt_len) (acpt_i:= i0) in H4.
    assumption. assumption. assumption. lia.
  (*current indx is less than acpt_len*)

  all: try assumption. lia.
  - rewrite <- N.pow_lt_mono_r_iff.
  apply getmem_bound. lia.
  - lia.
  - apply getmem_bound.
Qed.

Lemma succ_sub_exact:
  forall n, N.succ n - n = 1.
Proof. lia. Qed.

(* This theorem is for interfacing with testbit_xbits *)
Theorem xbits_odd_gtz:
  forall n i, N.odd (xbits n i (N.succ i)) = true <->  0 < xbits n i (N.succ i).
Proof.
  split; intros. all:unfold xbits in *. all:rewrite succ_sub_exact in *.
  - destruct (N.lt_trichotomy ((n >> i) mod 2 ^ (1)) 1) as [Lt | [Eq | Gt]];
    [exfalso| |exfalso].
    + destruct (N.eq_0_gt_0_cases ((n >> i) mod 2 ^ 1));[|exfalso].
      rewrite H0 in *. unfold N.odd in H. simpl in H. discriminate. lia.
    + rewrite Eq in *. lia.
    + change (2^1) with 2 in *. remember (n>>i) as x. clear - Gt.
      assert (Help: 2 <> 0) by lia. assert (H':=N.mod_upper_bound x 2 Help). lia.
  - destruct (N.lt_trichotomy ((n >> i) mod 2 ^ (1)) 1) as [Lt | [Eq | Gt]];
    [exfalso | |exfalso].
    + remember ((n >> i) mod 2 ^ 1) as x; lia.
    + rewrite Eq in *. unfold N.odd; now simpl.
    + assert (Help: 2 ^ 1 <> 0) by lia; remember (n >> i) as x;
      apply (N.mod_upper_bound x (2^1)) in Help. clear - Gt Help; remember (x mod 2 ^ 1) as y; lia.
Qed.

(*To address and simplify changed memory*)
Lemma bit_test_xbits_conversion:
  forall m p i (Lt : i < 8 * 32),
  0 < xbits (m Ⓑ[ p + (i >> 3) ]) (i mod 2 ^ 3) (1 + i mod 2 ^ 3) <-> 0 < xbits (m Ⓨ[ p ]) i (N.succ i).
Proof.
intros.
assert(forall k, k < 32-> (xbits(m Ⓨ[ p ]) (8*k) (8*k+8)) = m Ⓑ[ p + k ]).
intros. unfold xbits. psimpl (8 * k + 8 - 8 * k).
replace (8*k) with (k*8). rewrite shiftr_getmem.
change (2 ^ 8) with (2 ^ (1*8)). rewrite getmem_mod.
rewrite N.min_r. reflexivity. 1-2: lia.

unfold xbits. psimpl. rewrite <- N.add_1_r.  psimpl.
pose proof Lt. apply N.Div0.div_lt_upper_bound in H0.
change 8 with (2^3) in H0. rewrite <- N.shiftr_div_pow2 in H0.
specialize (H (i >> 3) H0). rewrite <- H.
unfold xbits. psimpl. replace (i >> 3) with (i / 8).
rewrite <- N.Div0.div_mod with (b:= 8) (a:=i).

reflexivity.

rewrite N.shiftr_div_pow2. psimpl (2^3). reflexivity.
Qed.

Lemma bit_test_xbits_conversion_2:
  forall m p i (Lt : i < 8 * 32),
  0 < xbits (m Ⓠ[ p + (i >> 6 << 3) ]) (i mod 2 ^ 6) (1 + i mod 2 ^ 6) <-> 0 < xbits (m Ⓨ[ p ]) i (N.succ i).
Proof.
intros.
assert(forall k, k <= 24-> (xbits(m Ⓨ[ p ]) (8*k) (8*k+64)) = m Ⓠ[ p + k ]).
intros. unfold xbits. psimpl (8 * k + 64 - 8 * k).
replace (8*k) with (k*8). rewrite shiftr_getmem.
change (2 ^ 64) with (2 ^ (8*8)).
rewrite getmem_mod. rewrite N.min_r. reflexivity. 1-2: lia.

unfold xbits. psimpl. rewrite <- N.add_1_r.  psimpl.
assert(INEQ: i <= 255). lia.

assert ((i >> 6 << 3) <= 24). apply Nshiftr_mono with (shift:= 6) in INEQ.
apply Nshiftl_mono with (shift:= 3) in INEQ. psimpl in INEQ. assumption.

specialize (H (i >> 6 << 3) H0). rewrite <- H.
unfold xbits. psimpl.
rewrite N.shiftl_mul_pow2. psimpl (2^3).
replace (8 * ((i >> 6) * 8)) with (64 * (i >> 6)) by lia.
rewrite N.shiftr_div_pow2 with (n:=6). psimpl (2^6).
rewrite <- N.Div0.div_mod with (b:= 64) (a:=i).

reflexivity.
Qed.

(*Building a bridge between bit and testbit*)
Lemma bit_test_bit_equiv:
  forall mem p i (Lt : i < 8 * 32), 0 < bit mem p i <-> N.testbit (getmem 64 LittleE 32 mem p) i = true.
Proof.
  intros. unfold bit. rewrite testbit_xbits. rewrite xbits_odd_gtz.
  eapply bit_test_xbits_conversion. assumption.
Qed.

Lemma bitarray_bridge:
forall bitmap_ptr accept_ptr L m,
bitarray_nstr m bitmap_ptr accept_ptr L <-> bitarray_nstr_new m bitmap_ptr accept_ptr L.
Proof.
unfold bitarray_nstr, bitarray_nstr_new. split; intros.
- split; intros. apply bit_test_bit_equiv in H1.
specialize (H i H0). apply H in H1. intuition. lia.
specialize (H i H0). apply H in H1. apply bit_test_bit_equiv. lia. assumption.
- split; intros. specialize (H i H0). eapply H. apply bit_test_bit_equiv. lia. assumption.
specialize (H i H0). apply H in H1. apply bit_test_bit_equiv in H1. assumption. lia.
Qed.

(*Helper for nstr_str_final*)
Lemma memory_checker :
forall m' m bitmap_ptr acpt_ptr acpt_len L
(NO : ¬ overlap 64 acpt_ptr (N.succ acpt_len) bitmap_ptr 32)
(ACPT_0_NNULL : m' Ⓑ[ acpt_ptr ] <> 0)
(ACPT_1_NNULL : m' Ⓑ[ 1 + acpt_ptr ] <> 0)
(STRLEN : strlen m' acpt_ptr acpt_len)
(L_LT_STRLEN : L <= acpt_len)
(MEM_REG : mem_region_unchanged m m' acpt_ptr acpt_len)
(BC : m' Ⓑ[ acpt_ptr + L ] <> 0)
(NO' : ¬ overlap 64 acpt_ptr acpt_len bitmap_ptr 32),
mem_region_unchanged m' (changed_mem bitmap_ptr acpt_ptr L m')
  acpt_ptr acpt_len.
Proof.
unfold mem_region_unchanged, changed_mem.
intros.

assert(LEN_NEQ: L <> acpt_len ).
unfold strlen in STRLEN. destruct STRLEN.
assert(L = acpt_len \/ L <> acpt_len). lia.
destruct H2. rewrite H2 in BC. contradiction. assumption.

apply noverlap_index_index with (len1:= acpt_len) (len2:= 32) (index1:= i) (index2:= (m Ⓑ[ acpt_ptr + L ] >> 6 << 3)) (size1:= 1) (size2:= 8) in NO'.

rewrite getmem_frame. reflexivity.

apply noverlap_sep. apply noverlap_symmetry. rewrite <- MEM_REG. assumption. lia.
apply noverlap_sep. rewrite <- MEM_REG. assumption. lia. lia.
assert (m Ⓑ[ acpt_ptr + L ] < 256). apply getmem_bound.
apply msbits_indexed_section_contained.
Qed.

Lemma bitarray_nstr_str_final :
  ∀ L m' acpt_ptr bitmap_ptr acpt_len
(NO : ¬ overlap 64 acpt_ptr (N.succ acpt_len) bitmap_ptr 32)
(ACPT_0_NNULL : m' Ⓑ[ acpt_ptr ] ≠ 0)
(ACPT_1_NNULL : m' Ⓑ[ 1 + acpt_ptr ] ≠ 0)
(STRLEN : strlen m' acpt_ptr acpt_len)
(L_LT_STRLEN : L <= acpt_len)
(BITNSTR : bitarray_nstr m' bitmap_ptr acpt_ptr L)
(BC : m' Ⓑ[ acpt_ptr + L ] ≠ 0)
(NO' : ¬ overlap 64 acpt_ptr acpt_len bitmap_ptr 32),

bitarray_nstr
  (m' [Ⓠ bitmap_ptr + (m' Ⓑ[ acpt_ptr + L ] >> 6 << 3):= 1 << m' Ⓑ[ acpt_ptr + L ] mod 64 .| m' Ⓠ[ bitmap_ptr +
(m' Ⓑ[ acpt_ptr +L] >>6 <<3)]])bitmap_ptr acpt_ptr (1 + L).

Proof. intros.
assert(LEN_NEQ: L <> acpt_len ).
unfold strlen in STRLEN. destruct STRLEN.
assert(L = acpt_len \/ L <> acpt_len). lia.
destruct H1. rewrite H1 in BC. contradiction. assumption.

change ((m' [Ⓠ
bitmap_ptr + (m' Ⓑ[ acpt_ptr + L ] >> 6 << 3)
:= 1 << m' Ⓑ[ acpt_ptr + L ] mod 64 .| m' Ⓠ[ bitmap_ptr +
(m'Ⓑ[ acpt_ptr + L] >>6 <<3)]]))
with (changed_mem bitmap_ptr acpt_ptr L m').

apply bitarray_bridge. apply bitarray_bridge in BITNSTR.
replace (1+L) with (L +1).


apply bitarray_nstr_incr_new with (acpt_len:= acpt_len).
all: try assumption.
apply memory_checker with (m:= m').
all: try assumption. unfold mem_region_unchanged. intros. reflexivity. lia.
lia.
Qed.

(*EDIT: had to change this for the new definition*)
Lemma bitmap_0_new:
forall acpt_ptr acpt_len sp m
(ACPT_LEN : strlen m acpt_ptr acpt_len)
(NO : ¬ overlap 64 acpt_ptr (N.succ acpt_len) sp 32)
(BITMAP_0 : m Ⓨ[ sp ] = 0)
(BC : (m Ⓑ[ acpt_ptr ] =? 0) = false)
(ACPT_0_NULL : m Ⓑ[ acpt_ptr ] ≠ 0)
(LEN_GT_2 : m Ⓑ[ 1 + acpt_ptr ] ≠ 0)
,
bitarray_nstr m sp acpt_ptr 0.
Proof. intros.
unfold bitarray_nstr.
intros. split;intros.
apply bit_test_bit_equiv in H0.
assert (m Ⓨ[ sp ] > 0).
apply N.testbit_true in H0.
assert (m Ⓨ[ sp ] = 0 \/ m Ⓨ[ sp ] > 0). lia.
destruct H1. rewrite H1 in H0. rewrite mp2_div_0_l in H0.
psimpl in H0. congruence.
assumption.
assert(m Ⓨ[ sp ] <> 0). lia.
contradiction.
lia.

destruct H0 as [j [J1 [NF ACPT]]].
lia.
Qed.


Lemma bit_test_equivalence_2:
  forall m bitmap_ptr i
  (HYP1: i < 256),
  (N.testbit (m Ⓠ[ bitmap_ptr + (i >> 6 << 3)]) (i mod 64) = true) <->
  N.testbit (m Ⓨ[ bitmap_ptr ])
  (i) = true.
Proof.
intros.
repeat rewrite testbit_xbits, xbits_odd_gtz.
replace (N.succ (i mod 64)) with (1 + (i mod 64)) by lia.
rewrite bit_test_xbits_conversion_2. reflexivity. lia.

Qed.


Lemma bit_test_equivalence_3:
  forall m bitmap_ptr i
  (HYP1: i < 256),
  (N.testbit (m Ⓑ[ bitmap_ptr + (i >> 3) ]) (i mod 2 ^ 3) = true) <->
  N.testbit (m Ⓨ[ bitmap_ptr ]) (i) = true.
Proof.
intros.
rewrite testbit_xbits. rewrite xbits_odd_gtz.
replace (N.succ (i mod 2 ^ 3)) with (1 + (i mod 2 ^ 3)) by lia.
rewrite bit_test_xbits_conversion.

rewrite testbit_xbits. rewrite xbits_odd_gtz.
reflexivity.
lia.
Qed.


Lemma map_no_value:
  forall  str_ptr sp m L
  (BC: (m Ⓠ[ sp + (m Ⓑ[ str_ptr + L ] >> 6 << 3) ] >> m Ⓑ[ str_ptr + L ] mod 64) mod (2^1) = 0),
    not(0 < bit m sp (m Ⓑ[ str_ptr + L ])).
Proof.
intros.
erewrite shiftr_mod_xbits with (i:= m Ⓑ[ str_ptr + L ] mod 64) in BC.
unfold bit.

replace (1 + m Ⓑ[ str_ptr + L ] mod 2 ^ 3) with (N.succ (m Ⓑ[ str_ptr + L ] mod 2 ^ 3)) by lia.

rewrite <- xbits_odd_gtz. rewrite <- testbit_xbits.
replace (m Ⓑ[ str_ptr + L ] mod 64 + 1) with (N.succ (m Ⓑ[ str_ptr + L ] mod 64)) in BC by lia.

unfold not.
assert(forall a, a = 0 -> not(0 < a)). lia. apply H in BC.
rewrite <- xbits_odd_gtz in BC. rewrite <- testbit_xbits in BC.
unfold not in BC.


rewrite bit_test_equivalence_2 in BC.
rewrite bit_test_equivalence_3. assumption. all: apply getmem_bound.
Qed.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                                               *)
(*             From Proofs File Section          *)
(*                                               *)
(* v v v v v v v v v v v v v v v v v v v v v v v *)
(* acpt string contains all characters of str's i-length prefix.
 *)
 Definition post_satis_i (i:N) (m:memory) (str_ptr:addr) (acpt_ptr:addr):=
  ∀j, j < i ->
  (∃ k : N, nilfree m acpt_ptr (k + 1)
    ∧ m Ⓑ[ acpt_ptr ⊕ k ] = m Ⓑ[ str_ptr ⊕ j ]).

(* If the post condition is satisfied for a prefix of length i, and the next character (index i)
   is not zero and in the bitmap then the post condition is satisfied for a prefix of length i+1
 *)
Lemma post_satis_incr :
  ∀ i char mem str_ptr acpt_ptr bitmap_ptr
     (POST:   post_satis_i i mem str_ptr acpt_ptr   )
     (BITMAP: bitarray_str mem bitmap_ptr acpt_ptr  )
     (NEXT:   mem Ⓑ[ str_ptr ⊕ i ] = char            )
     (CHAR_BIT:     bit mem bitmap_ptr char = 1       )
     (CHAR_NOT_NIL: 0 < char                          ),
     post_satis_i (1+i) mem str_ptr acpt_ptr.
Proof.
  intros.
  remember BITMAP as BITMAP2. clear HeqBITMAP2.
  unfold post_satis_i. intros.
  rewrite N.add_1_l, N.lt_succ_r in H.
  rename H into H'.
  destruct (N.lt_trichotomy j i) as [H | [H | Gt]];[ clear H' | clear H' | rewrite N.lt_nge in Gt; contradiction].
    unfold post_satis_i in POST. specialize (POST j). apply POST in H. assumption.
    unfold bitarray_str in BITMAP. specialize (BITMAP char). destruct BITMAP as [H0 _].
    rewrite <-NEXT; apply getmem_bound.
    rewrite CHAR_BIT in H0; destruct H0. apply N.lt_0_1. subst j.
    destruct H0 as [NILFREE CHAR].
    exists x. split.
    assert (H: ∃ j : N, nilfree mem acpt_ptr j ∧ mem Ⓑ[ acpt_ptr ⊕ j ] = char).
      { exists x. split; repeat assumption.
        apply (nilfree_shrink mem acpt_ptr (1+x) x). assumption. lia. }
      rewrite N.add_comm; assumption.
    subst char; assumption.
Qed.

Lemma bitarray_nstr_str :
  ∀ len mem acpt_ptr bitmap_ptr
     (BITNSTR: bitarray_nstr mem bitmap_ptr acpt_ptr len)
     (NIL: mem Ⓑ[ acpt_ptr + len ] = 0),
     bitarray_str mem bitmap_ptr acpt_ptr.
Proof.
unfold bitarray_nstr.
unfold bitarray_str.
intros.
split.
  * intro BIT. apply BITNSTR in BIT. destruct BIT as [j [LEN [NILFREE MEM]]]. exists j. split.
  assumption. rewrite getmem_mod_l. assumption. assumption.
  *
 intro H2; destruct H2 as [j [NILFREE MEM]]. apply BITNSTR. assumption. exists j. split.
  assert (TRI:= N.lt_trichotomy j len). destruct TRI as [LT | [EQ | GT]].
    assumption.
    subst j. unfold nilfree in NILFREE. specialize (NILFREE len). assert (H1: len < 1 + len). { lia. } apply NILFREE in H1.
      rewrite NIL in H1. now contradiction H1.
    unfold nilfree in NILFREE. specialize (NILFREE len). assert (H1: len < 1 + j). { lia. } apply NILFREE in H1.
      rewrite  NIL in H1. now contradiction H1.
  split. assumption. rewrite getmem_mod_l in MEM; assumption.
Qed.

Theorem noverlap_mod_idemp_l:
  forall w a1 len1 a2 len2,
    ~ overlap w (a1 mod 2 ^ w) len1 a2 len2 <->
    ~ overlap w  a1            len1 a2 len2.
Proof.
  intros. unfold overlap.
  split; intro H; intro H'. destruct H' as [i [j [LTi [LTj EQ]]]]. rewrite <-(N.Div0.add_mod_idemp_l a1) in EQ.
  apply H; exists i, j; repeat split; assumption.
  destruct H' as [i [j [LTi [LTj EQ]]]]. rewrite N.Div0.add_mod_idemp_l in EQ.
  apply H; exists i, j; repeat split; assumption.
Qed.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                                               *)
(*             Proofs File Cleanup Section       *)
(*                    ixb                        *)
(* v v v v v v v v v v v v v v v v v v v v v v v *)

Lemma prefix_no_wrap:
  forall L m' m0 acpt_ptr acpt_len str_ptr
    (ACPT_LEN: strlen m0 acpt_ptr acpt_len)
    (ACPT_SAME: mem_region_unchanged m0 m' acpt_ptr (N.succ acpt_len))
    (NF: nilfree m' str_ptr L),
    (L mod 2 ^ 64) = L.
Proof.
  intros.
  enough (H: L mod 2 ^ 64 = L); try now rewrite H.
  apply N.mod_small.
  unfold strlen in ACPT_LEN; destruct ACPT_LEN as [_ ZERO].
  apply (nflen_lt m' str_ptr L (acpt_ptr+acpt_len)). assumption.
  unfold mem_region_unchanged in ACPT_SAME.
  specialize (ACPT_SAME acpt_len (N.lt_succ_diag_r acpt_len)); rewrite <-ACPT_SAME.
  assumption.
Qed.

Lemma map_lookup_fail_postfix_fail:
    forall L m' str_ptr acpt_ptr bitmap_ptr
    (BITARRAY_STR: bitarray_str m' bitmap_ptr acpt_ptr)
    (LOOKUP_FAIL: (m' Ⓠ[ bitmap_ptr + (m' Ⓑ[ str_ptr + L ] >> 6 << 3) ] >>
       m' Ⓑ[ str_ptr + L ] mod 64) mod 2 = 0),

    ¬ post_satis_i (L + 1) m' str_ptr acpt_ptr.
Proof.
  intros.
  unfold post_satis_i. intro H'. specialize (H' L). assert (HELP:L<L+1) by lia; apply H' in HELP; clear H'. (*; destruct HELP as [k [NF' CHAREQ']].*)
  clear - BITARRAY_STR HELP LOOKUP_FAIL.
  unfold bitarray_str in BITARRAY_STR. specialize (BITARRAY_STR (m' Ⓑ[ str_ptr + L ])). assert (HELP':= getmem_bound 64 LittleE 1 m' (str_ptr + L )).
  change (2 ^ (8 * 1)) with 256 in HELP'.
  apply BITARRAY_STR in HELP'.
  rewrite getmem_mod_l in HELP.
  destruct HELP as [k [HNF HMEQ]]. rewrite N.add_comm in HNF.
  assert (HELP: ∃ j : N, nilfree m' acpt_ptr (1 + j) ∧ m' Ⓑ[ acpt_ptr ⊕ j ] = m' Ⓑ[ str_ptr + L ])
    by (exists k; split; assumption).
  rewrite <-HELP' in HELP; clear - HELP LOOKUP_FAIL.
  eapply map_no_value in LOOKUP_FAIL.
  contradiction.
Qed.

Lemma nil_terminator_postfix_fail:
forall L m' str_ptr acpt_ptr
(NIL: m' Ⓑ[ str_ptr + L ] = 0),
¬ post_satis_i (L + 1) m' str_ptr acpt_ptr.
Proof.
  intros.
  unfold post_satis_i. intro H1.
  specialize (H1 L). assert (HELP:L < L+1) by lia. apply H1 in HELP. destruct HELP as [x H2].
  destruct H2 as [NFAcpt Z]. unfold nilfree in NFAcpt. specialize (NFAcpt x). assert (HELP:x<x+1) by lia; apply NFAcpt in HELP.
  do 2 rewrite getmem_mod_l in Z. rewrite NIL in Z; congruence.
Qed.

Lemma post_satis_incr':
  ∀ i char mem str_ptr acpt_ptr bitmap_ptr
  (POST:   post_satis_i i mem str_ptr acpt_ptr   )
  (BITMAP: bitarray_str mem bitmap_ptr acpt_ptr  )
  (NEXT:   mem Ⓑ[ str_ptr + i ] = char            )
  (NNULL:  mem Ⓑ[ str_ptr + i ] ≠ 0              )
  (CHAR_BIT: (mem Ⓠ[ bitmap_ptr + (mem Ⓑ[ str_ptr + i ] >> 6 << 3) ] >>
       mem Ⓑ[ str_ptr + i ] mod 64) mod 2 ≠ 0       )
  (CHAR_NOT_NIL: 0 <> char                          ),
  post_satis_i (1+i) mem str_ptr acpt_ptr.
Proof.
  intros.
  apply post_satis_incr with (char:=mem Ⓑ[ str_ptr + i ]) (bitmap_ptr:=bitmap_ptr);
    try (assumption || rewrite getmem_mod_l; reflexivity).
    apply map_checker_n_helper; assumption.
    destruct (mem Ⓑ[ str_ptr + i ]) ; (congruence || lia).
Qed.

Lemma single_char_ret:
  forall m L acpt_ptr str_ptr
  (ACPT_0_NNULL: m Ⓑ[ acpt_ptr ] ≠ 0)
  (PREFIX: ∀ i : N, i < L → m Ⓑ[ acpt_ptr ] = m Ⓑ[ str_ptr + i ]),
  post_satis_i L m str_ptr acpt_ptr.
Proof.
  intros.
  unfold post_satis_i. intros. exists 0. split.
  psimpl. unfold nilfree. intros. destruct i.
    psimpl; now symmetry.
    destruct p; discriminate.
  psimpl. apply PREFIX. assumption.
Qed.

Lemma single_char_ret_fail:
  forall L m str_ptr acpt_ptr
  (BC: (m Ⓑ[ str_ptr + L ] =? m Ⓑ[ acpt_ptr ]) = false)
  (ACPT_1_NULL: m Ⓑ[ 1 + acpt_ptr ] = 0),
  ¬ post_satis_i (L + 1) m str_ptr acpt_ptr.
Proof.
  intros.
  unfold post_satis_i. unfold not. intros H1. apply N.eqb_neq in BC. specialize (H1 L).
  destruct H1 as [k [NILFREE NIL]]. lia.
  assert (KZERO: k = 0). { destruct k. reflexivity. unfold nilfree in NILFREE. specialize (NILFREE 1).
    destruct NILFREE; try lia. symmetry; rewrite N.add_comm. assumption.
  }
  rewrite KZERO in NIL; psimpl in NIL. symmetry in NIL. contradiction.
Qed.

Ltac MS0 H:=
  let a := fresh "memsame" in
  assert (a:=H 0 (N.lt_0_succ _)); psimpl in a.

Lemma empty_accept_exit:
  forall m0 m str_ptr acpt_ptr acpt_len
    (MEMSAME: mem_region_unchanged m0 m acpt_ptr (N.succ acpt_len))
    (BC: m0 Ⓑ[ acpt_ptr ] = 0),
  ¬ post_satis_i (0 + 1) m str_ptr acpt_ptr.
Proof.
intros.
unfold post_satis_i. unfold not. intros.
specialize (H 0). simpl N.add in H. destruct H. apply N.lt_0_1.
psimpl in H. assert (Disj:= N.lt_trichotomy x 0). destruct Disj as [Lt | [Eq | Gt]].
apply N.nlt_0_r in Lt. contradiction.
subst x. psimpl in H. destruct H as [NILFREE _]. unfold nilfree in NILFREE. specialize (NILFREE 0).
  assert (H:= N.lt_0_1). apply NILFREE in H. psimpl in H.
  MS0 MEMSAME. rewrite memsame in *; congruence.

destruct H as [NILFREE _]. unfold nilfree in NILFREE. specialize (NILFREE 0). assert (H: 0<1+x). lia.
  apply NILFREE in H.  psimpl in H.
  MS0 MEMSAME. rewrite memsame in *; congruence.
Qed.

Lemma entry_memory_unchanged:
  forall acpt_ptr acpt_len sp m0
    (NO: ¬ overlap 64 acpt_ptr (N.succ acpt_len) (sp ⊖ 32) 32)
  ,
  mem_region_unchanged m0
  (m0 [Ⓧ sp ⊖ 32 := m0 Ⓧ[ 1048752 ] ] [Ⓧ sp ⊖ 16
   := m0 Ⓧ[ 1048768 ] ]) acpt_ptr (N.succ acpt_len).
Proof.
intros.
assert (Help: sp ⊖ 16 = sp ⊖ 32 ⊕ 16) by (now psimpl).
rewrite Help.
unfold mem_region_unchanged. intros.
rewrite getmem_noverlap, getmem_noverlap. reflexivity.
  (* TODO: make noverlap_symmetry an iff so we can use it with rewrite *)
  apply noverlap_index with (len1:=N.succ acpt_len). apply noverlap_symmetry.
  apply (noverlap_shrink _ (sp ⊖ 32) 32). psimpl; lia.
  apply noverlap_symmetry; assumption. lia.
  apply noverlap_symmetry, noverlap_mod_idemp_l, noverlap_symmetry.
  apply noverlap_index_index with (len1:=N.succ acpt_len) (len2:=32); try (assumption || lia).
Qed.

(*Shreya EDIT Cleanup Section*)
Lemma noverlap_arg_sum_rewrite:
  forall w a1 i1 len1 a2 i2 len2 size1 size2
  (NO: ~overlap w (a1) len1 (a2) len2)
  (LE: (i1 + size1 <= len1) /\ (i2 + size2 <= len2)),
   ~overlap w (a1 + i1) size1 (a2 + i2) size2 <-> ~overlap w (a1) (i1 + size1) (a2) (i2 + size2) .
  Proof.
  intros. destruct LE. split; intros.
  {
  assert(~overlap w a1 (i1 + size1) a2 len2).
  eapply (noverlap_shrink w a1 len1 a2 len2 a1 (i1 + size1)).
  assert(a1 mod 2 ^ w = a1 mod 2 ^ w). lia. rewrite <- msub_move_0_r in H2. rewrite H2. psimpl. assumption.
  assumption.
  apply noverlap_symmetry in H2, NO. apply noverlap_symmetry.
  eapply (noverlap_shrink w a2 len2 a1 (i1 + size1) a2 (i2 + size2)).
  assert(a2 mod 2 ^ w = a2 mod 2 ^ w). lia. rewrite <- msub_move_0_r in H3. rewrite H3. psimpl. all : assumption.
  }
  eapply noverlap_index_index with (len1:=len1) (len2:=len2). all: assumption.
Qed.

Definition sp' sp := sp ⊖ 32.

Lemma overlap_transform_rewrite:
  forall acpt_ptr acpt_len sp m' bitmap_ptr L
  (NO : ¬ overlap 64 acpt_ptr (N.succ acpt_len) (sp ⊖ 32) 32)
  (ACPT_0_NNULL : m' Ⓑ[ acpt_ptr ] ≠ 0)
  (ACPT_1_NNULL : m' Ⓑ[ 1 + acpt_ptr ] ≠ 0)
  (STRLEN : strlen m' acpt_ptr acpt_len)
  (L_LT_STRLEN : L <= acpt_len)
  (H0 : bitmap_ptr = sp ⊖ 32)
  ,
  (*+0, +1, +i, +acpt_len*)
  (forall i, ((i < N.succ acpt_len)) ->
  ¬ overlap 64 (acpt_ptr + i) 1 (sp ⊖ 32 + (m' Ⓑ[ acpt_ptr + L ] >> 6 << 3)) 8) /\
  ¬ overlap 64 (acpt_ptr + 0) acpt_len (sp ⊖ 32 + (m' Ⓑ[ acpt_ptr + L ] >> 6 << 3)) 8.
  Proof.
  intros. repeat split.
  intros.
  rewrite <- H0 in *.
    apply noverlap_index_index with (len1:=N.succ acpt_len) (len2:=32); try (assumption || lia).
    apply msbits_indexed_section_contained.

  rewrite <- H0 in *.
    apply noverlap_index_index with (len1:=N.succ acpt_len) (len2:=32); try (assumption || lia).
    apply msbits_indexed_section_contained.

Qed.

Lemma accept_len_gte_2:
  forall acpt_ptr acpt_len m' L
  (ACPT_0_NNULL : m' Ⓑ[ acpt_ptr ] ≠ 0)
  (ACPT_1_NNULL : m' Ⓑ[ 1 + acpt_ptr ] ≠ 0)
  (STRLEN : strlen m' acpt_ptr acpt_len)
  (L_LT_STRLEN : L <= acpt_len),
  1 < acpt_len + 1.
  Proof.
  intros.
  assert(2 <= acpt_len).
    simpl. destruct (N.lt_ge_cases acpt_len 2); try assumption.
    (* showing a contradiction if acpt_len < 2 *)
    destruct acpt_len. unfold strlen in STRLEN; destruct STRLEN as [NF ZERO].
      rewrite N.add_0_r in ZERO; contradiction. destruct p; try (destruct p; discriminate).
    unfold strlen in STRLEN. destruct STRLEN as [NF F]; rewrite N.add_comm in F.
    destruct L; contradiction.
  lia.
Qed.

Lemma L_lte_acpt_len:
  forall acpt_ptr acpt_len m' L
  (ACPT_0_NNULL : m' Ⓑ[ acpt_ptr ] ≠ 0)
  (ACPT_1_NNULL : m' Ⓑ[ 1 + acpt_ptr ] ≠ 0)
  (STRLEN : nilfree m' acpt_ptr acpt_len ∧ m' Ⓑ[ acpt_ptr + acpt_len ] = 0)
  (L_LT_STRLEN : L <= acpt_len)
  (BC : m' Ⓑ[ acpt_ptr + L ] ≠ 0),
1 + L <= acpt_len.
Proof.
  intros.
  unfold strlen in STRLEN.
  destruct (N.lt_trichotomy (1+L) acpt_len) as [Lt | [Eq | Gt]];[apply N.lt_le_incl; assumption | | ].
  now rewrite Eq. destruct (N.lt_trichotomy L acpt_len) as [Lt' | [Eq' | Gt']]; try lia. subst L. now destruct STRLEN.
Qed.

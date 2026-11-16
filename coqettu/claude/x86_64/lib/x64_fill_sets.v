Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_memcpy_sets.
Open Scope N.

(* Lemmas for the memset proofs, in the style of amd64_memcpy_sets.v.  memset
   stores the byte c in overlapping pieces of up to 32 bytes, so we track the
   set W of destination offsets written so far:

     fil m m' d c W:  m' holds c at d+i for every i in W, and agrees with m at
                      every address whose offset from d is not in W.

   One store of a value whose bytes are all c adds its offsets to W
   (fil_store).  Written by Claude Opus 5.5 (claude-opus-5-5) and checked by
   Rocq. *)

(* The postcondition: m' holds c at dest[0,n) and agrees with m elsewhere. *)
Definition filled (m m':memory) (d c n:N) :=
  (forall i, i < n -> m' Ⓑ[d ⊕ i] = c) /\
  (forall b, ~ (msub 64 b d < n) -> m' Ⓑ[b] = m Ⓑ[b]).

Definition fil (m m':memory) d c (W:N->Prop) :=
  (forall i, W i -> m' Ⓑ[d ⊕ i] = c) /\
  (forall b, ~ W (msub 64 b d) -> m' Ⓑ[b] = m Ⓑ[b]).

(* Every one of the L bytes of v is c. *)
Definition bytes_are (v L c:N) := forall k, k < L -> xbits v (8*k) (8*k+8) = c.

Lemma fil_empty: forall m d c, fil m m d c (fun _ => False).
Proof. intros. split. intros i []. reflexivity. Qed.

Lemma fil_equiv:
  forall m m' d c (W W':N->Prop), (forall i, W i <-> W' i) -> fil m m' d c W -> fil m m' d c W'.
Proof.
  intros m m' d c W W' E [C F]. split.
  intros i I. apply C, E, I.
  intros b B. apply F. rewrite E. exact B.
Qed.

Lemma fil_filled:
  forall m m' d c n (W:N->Prop), (forall i, W i <-> i < n) -> fil m m' d c W -> filled m m' d c n.
Proof.
  intros m m' d c n W E [C F]. split.
  intros i I. apply C, E, I.
  intros b B. apply F. rewrite E. exact B.
Qed.

Lemma fil_store:
  forall m m' d c (W:N->Prop) o L a v,
  fil m m' d c W -> (forall i, W i -> i < 2^64) -> 0 < L -> o + L <= 2^64 ->
  a mod 2^64 = (d + o) mod 2^64 -> bytes_are v L c ->
  fil m (setmem 64 LittleE L m' a v) d c (fun i => W i \/ o <= i < o + L).
Proof.
  intros m m' d c W o L a v [C F] WB L0 OL A V.
  assert (O: o < 2^64) by lia.
  assert (OFF: forall i, i < 2^64 -> (msub 64 (d ⊕ i) a <? L) = (o <=? i) && (i <? o + L)).
    intros i I. rewrite (msub_off d i o a) by assumption.
    change (2^64) with 18446744073709551616 in *.
    destruct (N.leb_spec o i), (N.ltb_spec i (o + L)); cbn [andb];
      [apply N.ltb_lt | apply N.ltb_ge | apply N.ltb_ge | apply N.ltb_ge]; lia.
  split.
  - intros i Wi.
    assert (Ib: i < 2^64) by (destruct Wi as [Wi|Wi]; [apply WB, Wi | lia]).
    rewrite byte_setmem_cases, OFF by lia.
    destruct (N.leb_spec o i), (N.ltb_spec i (o + L)); cbn [andb].
    + rewrite (msub_off d i o a) by assumption. destruct (N.leb_spec o i); [|lia].
      apply V. lia.
    + destruct Wi as [Wi|Wi]. apply C, Wi. lia.
    + destruct Wi as [Wi|Wi]. apply C, Wi. lia.
    + destruct Wi as [Wi|Wi]. apply C, Wi. lia.
  - intros b B. set (j := msub 64 b d) in B.
    assert (Bj: b mod 2^64 = d ⊕ j) by (subst j; rewrite add_msub; reflexivity).
    assert (J: j < 2^64) by apply msub_lt.
    rewrite byte_setmem_cases by lia.
    rewrite <- (msub_mod_l 64 64 b) by reflexivity. rewrite Bj, OFF by exact J.
    destruct (N.leb_spec o j), (N.ltb_spec j (o + L)); cbn [andb].
    + exfalso. apply B. right. lia.
    + apply F. intro Wb. apply B. left. exact Wb.
    + apply F. intro Wb. apply B. left. exact Wb.
    + apply F. intro Wb. apply B. left. exact Wb.
Qed.

(* A value whose bytes are all c keeps that property in its low part. *)
Lemma bytes_are_mod: forall v L L' c, L' <= L -> bytes_are v L c -> bytes_are (v mod 2^(8*L')) L' c.
Proof.
  intros v L L' c LL V k K. rewrite <- (V k) by lia.
  apply N.bits_inj. intro j. rewrite !xbits_spec.
  destruct (N.ltb_spec (j + 8*k) (8*k+8)).
  - rewrite N.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Bool.andb_false_r. reflexivity.
Qed.

(* The broadcast byte: VPBROADCASTB / the lifted MOVs build c's byte repeated
   as  (...((c << 8 .| c mod 2^8) << 8 .| c mod 2^8)...). *)
Lemma bytes_are_one: forall c, bytes_are c 1 (c mod 2^8).
Proof.
  intros c k K. replace k with 0 by lia. cbn [N.mul N.add].
  unfold xbits. rewrite N.shiftr_0_r. reflexivity.
Qed.

Lemma bytes_are_step: forall v L c,
  bytes_are v L (c mod 2^8) -> bytes_are (v << 8 .| c mod 2^8) (N.succ L) (c mod 2^8).
Proof.
  intros v L c V k K. apply N.bits_inj. intro j. rewrite xbits_spec.
  destruct (N.eq_0_gt_0_cases k) as [->|KP].
  - destruct (N.ltb_spec (j + 8*0) (8*0+8)) as [J|J]; cbn [andb].
    + rewrite Bool.andb_true_r, N.lor_spec, N.shiftl_spec_low by lia.
      cbn [orb]. replace (j + 8*0) with j by lia. reflexivity.
    + rewrite Bool.andb_false_r. symmetry. apply N.bits_above_log2.
      destruct (N.eq_0_gt_0_cases (c mod 2^8)) as [->|P]. cbn. lia.
      apply N.log2_lt_pow2. exact P. eapply N.lt_le_trans. apply N.mod_lt. discriminate.
      apply N.pow_le_mono_r; lia.
  - specialize (V (k - 1) ltac:(lia)).
    assert (E: N.testbit (c mod 2^8) j = N.testbit (xbits v (8*(k-1)) (8*(k-1)+8)) j) by (rewrite V; reflexivity).
    rewrite E, xbits_spec.
    rewrite N.lor_spec, N.shiftl_spec_high by lia.
    rewrite (N.mod_pow2_bits_high c 8 (j + 8*k)) by lia. rewrite Bool.orb_false_r.
    replace (j + 8*k - 8) with (j + 8*(k-1)) by lia.
    replace (j + 8*k <? 8*k + 8) with (j + 8*(k-1) <? 8*(k-1) + 8); [reflexivity|].
    destruct (N.ltb_spec (j + 8*(k-1)) (8*(k-1) + 8)), (N.ltb_spec (j + 8*k) (8*k + 8)); lia.
Qed.

Lemma bytes_are_step': forall v L L' c, L = N.succ L' ->
  bytes_are v L' (c mod 2^8) -> bytes_are (v << 8 .| c mod 2^8) L (c mod 2^8).
Proof. intros v L L' c ->. apply bytes_are_step. Qed.

(* bytes_are for a lifted broadcast value of L bytes. *)
Ltac rep_bytes :=
  lazymatch goal with
  | |- bytes_are (_ << 8 .| _ mod 2^8) ?L _ =>
      let L' := eval compute in (N.pred L) in
      apply (bytes_are_step' _ L L'); [reflexivity | rep_bytes]
  | |- bytes_are _ 1 _ => apply bytes_are_one
  end.

(* ---- Tactics for chains of fill stores (shared by the memset-like proofs) ---- *)

Require Import CoqEtTu.lib.x64_abi.

(* The tail store address d - L + n is offset n - L from d. *)
Lemma tail_off: forall d L n, L <= n -> L < 2^64 -> (msub 64 d L + n) mod 2^64 = (d + (n - L)) mod 2^64.
Proof.
  intros d L n LN LB. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small L) by exact LB.
  replace (d + (2^64 - L) + n) with (d + (n - L) + 1 * 2^64) by lia.
  apply N.mod_add. discriminate.
Qed.

Lemma bytes_are_rep:
  forall K L c, rep_ok K L = true -> bytes_are (c mod 2^8 * K) L (c mod 2^8).
Proof.
  intros K L c R k Hk. apply (rep_ok_xbits K L R). apply N.mod_lt. discriminate. exact Hk.
Qed.

(* The offset from d of a lifted store address. *)
Ltac off_of a d :=
  lazymatch a with
  | msub 64 d ?k + ?n => constr:(n - k)
  | ?k + (d + ?x) => constr:(k + x)
  | (?j + d) + ?x => constr:(j + x)
  | d + ?x => constr:(x)
  | ?k + d => constr:(k)
  | d => constr:(0)
  end.

Ltac fil_side :=
  lazymatch goal with
  | |- bytes_are (_ mod 2^8 * _) _ _ => apply bytes_are_rep; vm_compute; reflexivity
  | |- bytes_are _ _ _ => first [assumption | apply bytes_are_one | rep_bytes]
  | |- forall i, _ -> i < 2^64 =>
      let i := fresh "i" in let Hi := fresh "Hi" in
      intros i Hi; cbv beta in Hi; repeat destruct Hi as [Hi|Hi];
      change (2^64) with 18446744073709551616 in *; lia
  | |- 0 < _ => reflexivity
  | |- _ + _ <= 2^64 => change (2^64) with 18446744073709551616 in *; lia
  | |- (msub 64 _ _ + _) mod 2^64 = _ =>
      rewrite tail_off by (change (2^64) with 18446744073709551616 in *; lia); reflexivity
  | |- (_ + _) mod 2^64 = (_ + _) mod 2^64 => f_equal; lia
  | |- (?x) mod 2^64 = (?x + 0) mod 2^64 => rewrite N.add_0_r; reflexivity
  | |- _ mod 2^64 = (_ + 0) mod 2^64 => rewrite N.add_0_r; reflexivity
  end.

(* Build the fil chain for a nest of stores of the broadcast byte. *)
Ltac fil_chain d :=
  lazymatch goal with
  | |- fil ?m0 (setmem 64 LittleE ?L ?M ?a ?v) d _ _ =>
      let o := off_of a d in
      eapply (fil_store m0 M d _ _ o L a v); [fil_chain d | fil_side ..]
  | |- fil ?m0 ?m0 d _ _ => apply fil_empty
  | |- fil ?m0 ?M d _ _ =>
      first [match goal with H: M = m0 |- _ => rewrite H; apply fil_empty end | eassumption]
  end.

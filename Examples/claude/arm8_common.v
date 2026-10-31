(* arm8_common -- shared, architecture-neutral lemmas for the AArch64 glibc
   port.  These are pure facts about N/Z and the Picinae word operations; they
   mirror helpers used across the amd64 proofs and absorb the extra
   normalization (mod 2^w, msub _ 0, sign tests) that AArch64 W-register writes
   introduce. *)

Require Import Picinae_armv8.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith List.
Open Scope N.

(* msub against zero is just reduction mod 2^w. *)
Lemma msub_0_r: forall w x, msub w x 0 = x mod 2^w.
Proof.
  intros. unfold msub. rewrite N.mod_0_l by (apply N.pow_nonzero; discriminate).
  rewrite N.sub_0_r. replace (x + 2^w) with (x + 1 * 2^w) by lia.
  rewrite N.mod_add by (apply N.pow_nonzero; discriminate). reflexivity.
Qed.

(* Signed comparison only sees the low w bits. *)
Lemma slt_mod: forall w x, slt w (x mod 2^w) 0 = slt w x 0.
Proof. intros. unfold slt. rewrite (toZ_mod_pow2 w w x) by apply N.le_refl. reflexivity. Qed.

(* Modular subtraction is zero exactly when the (in-range) operands are equal. *)
Lemma msub_eqb_0: forall a b, a < 2^64 -> b < 2^64 -> (msub 64 a b =? 0) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (N.eqb_spec a b) as [E|E].
  - subst. rewrite msub_diag. reflexivity.
  - apply N.eqb_neq. intro H. apply E.
    pose proof (add_msub 64 b a) as AM. rewrite H, N.add_0_r in AM.
    rewrite (N.mod_small b), (N.mod_small a) in AM by assumption. symmetry; exact AM.
Qed.

(* cneg produces |x| in both the negate and the keep branch (any width). *)
Lemma cneg_abs: forall w x,
  (slt w x 0 = true  -> msub w 0 x = ofZ w (Z.abs (toZ w x))) /\
  (slt w x 0 = false -> x mod 2^w = ofZ w (Z.abs (toZ w x))).
Proof.
  intros w x. set (j := toZ w x).
  assert (V: msub w 0 x = ofZ w (- j)) by (rewrite msub_sbop, toZ_0_r; reflexivity).
  assert (N: ofZ w j = x mod 2^w) by (unfold j; apply ofZ_toZ).
  unfold slt. rewrite !toZ_0_r. fold j.
  split; intro BC.
  - apply Z.ltb_lt in BC. rewrite V, Z.abs_neq by lia. reflexivity.
  - apply Z.ltb_ge in BC. rewrite Z.abs_eq by lia. symmetry; exact N.
Qed.

(* ASCII mask: the top 25 bits are clear iff the value is below 128. *)
Lemma land_mask7:
  forall x, (x .& 4294967168 =? 0) = (x mod 2^32 <? 128).
Proof.
  intro x.
  replace (x .& 4294967168) with (N.shiftl (N.shiftr (x mod 2^32) 7) 7).
    rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2.
    destruct (N.ltb_spec (x mod 2^32) 128) as [H|H].
      rewrite N.div_small by exact H. reflexivity.
      apply N.eqb_neq. intro H0. apply N.eq_mul_0_l in H0; [|discriminate].
      apply N.div_small_iff in H0; [|discriminate]. lia.
  apply N.bits_inj. intro i. rewrite N.land_spec.
  change 4294967168 with (N.shiftl (N.ones 25) 7).
  destruct (N.lt_ge_cases i 7) as [I|I].
    rewrite !N.shiftl_spec_low by exact I. symmetry. apply Bool.andb_false_r.
    rewrite !N.shiftl_spec_high' by exact I. rewrite N.shiftr_spec', N.sub_add by exact I.
    rewrite Nmod_pow2_bits.
    destruct (N.lt_ge_cases i 32) as [J|J].
      rewrite (proj2 (N.ltb_lt _ _) J), N.ones_spec_low by lia. apply Bool.andb_comm.
      rewrite (proj2 (N.ltb_ge _ _) J), N.ones_spec_high by lia. symmetry. apply Bool.andb_false_r.
Qed.

Lemma toZ32_ascii:
  forall n, andb (Z.leb 0 (toZ 32 n)) (Z.leb (toZ 32 n) 127) = (n mod 2^32 <? 128).
Proof.
  intro n. destruct (N.lt_ge_cases (n mod 2^32) (2^31)) as [H|H].
    rewrite (proj1 (toZ_nonneg 32 n) H).
    destruct (N.ltb_spec (n mod 2^32) 128); destruct (Z.leb_spec 0 (Z.of_N (n mod 2^32)));
    destruct (Z.leb_spec (Z.of_N (n mod 2^32)) 127); simpl; lia.
    assert (NEG: Z.lt (toZ 32 n) 0).
      apply Z.nle_gt. intro H1. apply toZ_sign in H1. simpl in H1. lia.
    destruct (Z.leb_spec 0 (toZ 32 n)); [lia|].
    simpl. symmetry. apply N.ltb_ge. change (2^31) with 2147483648 in H. lia.
Qed.

(* FP (IEEE-754) helpers, shared with the amd64 proofs. *)
Lemma shr_msub64: forall c a, c < 2^63 -> a < 2^63 -> msub 64 c a >> 63 = if c <? a then 1 else 0.
Proof.
  intros c a C A. rewrite N.shiftr_div_pow2.
  change (2^63) with 9223372036854775808 in *.
  destruct (N.ltb_spec c a) as [H|H].
  - rewrite msub_wrap by (rewrite !N.mod_small; change (2^64) with 18446744073709551616; lia).
    rewrite !N.mod_small by (change (2^64) with 18446744073709551616; lia).
    change (2^64) with 18446744073709551616.
    symmetry. apply N.div_unique with (r := 18446744073709551616 + c - a - 9223372036854775808); lia.
  - rewrite msub_nowrap by (rewrite !N.mod_small; change (2^64) with 18446744073709551616; lia).
    rewrite !N.mod_small by (change (2^64) with 18446744073709551616; lia).
    apply N.div_small. lia.
Qed.

Lemma shr_msub32: forall c a, c < 2^31 -> a < 2^31 -> msub 32 c a >> 31 = if c <? a then 1 else 0.
Proof.
  intros c a C A. rewrite N.shiftr_div_pow2.
  change (2^31) with 2147483648 in *.
  destruct (N.ltb_spec c a) as [H|H].
  - rewrite msub_wrap by (rewrite !N.mod_small; change (2^32) with 4294967296; lia).
    rewrite !N.mod_small by (change (2^32) with 4294967296; lia).
    change (2^32) with 4294967296.
    symmetry. apply N.div_unique with (r := 4294967296 + c - a - 2147483648); lia.
  - rewrite msub_nowrap by (rewrite !N.mod_small; change (2^32) with 4294967296; lia).
    rewrite !N.mod_small by (change (2^32) with 4294967296; lia).
    apply N.div_small. lia.
Qed.
Definition dev_make (maj min:N) :=
  (min .& 0xff) .| ((maj .& 0xfff) << 8) .| ((min .& 0xffffff00) << 12) .|
  ((maj .& 0xfffff000) << 32).
Definition dev_major (dev:N) := ((dev >> 8) .& 0xfff) .| ((dev >> 32) .& 0xfffff000).
Definition dev_minor (dev:N) := (dev .& 0xff) .| ((dev >> 12) .& 0xffffff00).

(* IPv4 classful address split (inet_netof / inet_lnaof), shared with amd64. *)
Definition ntohl32 (x:N) :=
  (xbits x 0 8 << 24) .| (xbits x 8 16 << 16) .| (xbits x 16 24 << 8) .| xbits x 24 32.
Definition is_classA (a:N) := a .& 0x80000000 =? 0.
Definition is_classB (a:N) := a .& 0xc0000000 =? 0x80000000.
Definition inet_net (a:N) :=
  if is_classA a then a >> 24 else if is_classB a then a >> 16 else a >> 8.
Definition inet_lna (a:N) :=
  if is_classA a then a .& 0xffffff else if is_classB a then a .& 0xffff else a .& 0xff.

Lemma land_bit31: forall y, y .& 0x80000000 = if N.testbit y 31 then 2^31 else 0.
Proof.
  intro y. change 0x80000000 with (2^31). apply N.bits_inj. intro i.
  rewrite N.land_spec, N.pow2_bits_eqb.
  destruct (N.eqb_spec 31 i) as [<-|NE]; destruct (N.testbit y 31) eqn:B.
    reflexivity. reflexivity.
    rewrite N.pow2_bits_eqb, (proj2 (N.eqb_neq _ _) NE). apply Bool.andb_false_r.
    rewrite N.bits_0. apply Bool.andb_false_r.
Qed.

Lemma ifb31_eqb0: forall b:bool, ((if b then 2^31 else 0) =? 0) = negb b.
Proof. destruct b; reflexivity. Qed.

(* The tbz/sign test `(y >> 31) mod 2` is exactly bit 31. *)
Lemma shr31_mod2: forall y, (y >> 31) mod 2 = (if N.testbit y 31 then 1 else 0).
Proof.
  intro y. rewrite N.shiftr_div_pow2, <- N.testbit_spec'.
  destruct (N.testbit y 31); reflexivity.
Qed.

(* The sign-copy bit insert: replace bit w of x with bit w of y. *)
Lemma copysign_insert: forall x y w,
  (x .^ ((x .^ y) .& 2^w)) mod 2^(N.succ w) = x mod 2^w .| (y .& 2^w).
Proof.
  intros x y w. apply N.bits_inj. intro i.
  rewrite Nmod_pow2_bits, N.lxor_spec, N.land_spec, N.lxor_spec.
  rewrite N.lor_spec, Nmod_pow2_bits, N.land_spec.
  rewrite !N.pow2_bits_eqb.
  destruct (N.eqb_spec i w) as [->|NE].
  - replace (w <? N.succ w) with true by (symmetry; apply N.ltb_lt; lia).
    replace (w <? w) with false by (symmetry; apply N.ltb_ge; lia).
    rewrite N.eqb_refl.
    destruct (N.testbit x w), (N.testbit y w); reflexivity.
  - assert (WI: (w =? i) = false) by (apply N.eqb_neq; lia). rewrite WI.
    destruct (N.ltb_spec i (N.succ w)) as [H|H].
    + replace (i <? w) with true by (symmetry; apply N.ltb_lt; lia).
      destruct (N.testbit x i), (N.testbit y i); reflexivity.
    + replace (i <? w) with false by (symmetry; apply N.ltb_ge; lia).
      destruct (N.testbit x i), (N.testbit y i); reflexivity.
Qed.

(* Extract a shifted byte-field: (h & (ones m << k)) >> k = (h >> k) mod 2^m. *)
Lemma shr_land_shl: forall h m k, (h .& (N.ones m << k)) >> k = (h >> k) mod 2^m.
Proof.
  intros h m k. apply N.bits_inj. intro i.
  rewrite N.shiftr_spec', N.land_spec, N.shiftl_spec_high' by lia.
  replace (i + k - k) with i by lia.
  rewrite Nmod_pow2_bits, N.shiftr_spec'.
  destruct (N.ltb_spec i m) as [H|H].
  - rewrite N.ones_spec_low by lia. apply Bool.andb_comm.
  - rewrite N.ones_spec_high by lia. apply Bool.andb_false_r.
Qed.

(* --- Bit-blasting tactics (shared with amd64_common; arch-neutral N facts). --- *)

Lemma testbit_shiftl_ltb:
  forall a n m, N.testbit (a << n) m = if m <? n then false else N.testbit a (m - n).
Proof.
  intros. destruct (N.ltb_spec m n).
    apply N.shiftl_spec_low. assumption.
    apply N.shiftl_spec_high'. assumption.
Qed.

Lemma testbit_const_high:
  forall c i, N.size c <= i -> N.testbit c i = false.
Proof.
  intros. destruct c as [|c]. apply N.bits_0.
  apply N.bits_above_log2. rewrite N.size_log2 in H by discriminate. lia.
Qed.

(* Rewrite N.testbit of a bitwise expression into N.testbit of its leaves. *)
Ltac bits_rewrite :=
  repeat first
    [ rewrite N.lor_spec | rewrite N.land_spec | rewrite N.lxor_spec
    | rewrite N.shiftr_spec' | rewrite testbit_shiftl_ltb | rewrite Nmod_pow2_bits
    | rewrite xbits_spec | rewrite revbytes_spec ].

(* Close a goal between boolean combinations of testbits at concrete indices. *)
(* Normalize the (closed) index of every non-constant testbit leaf. *)
Ltac bits_norm_idx :=
  repeat match goal with |- context [N.testbit ?x ?k] =>
    lazymatch x with Npos _ => fail | N0 => fail | _ =>
      let k' := eval vm_compute in k in
      tryif constr_eq k k' then fail else change (N.testbit x k) with (N.testbit x k')
    end end.

Ltac bits_close :=
  bits_rewrite; bits_norm_idx;
  repeat match goal with |- context [N.testbit ?x ?k] =>
    lazymatch x with Npos _ => fail | N0 => fail | _ =>
      destruct (N.testbit x k) end end;
  reflexivity.

(* Decide every comparison in the goal by case analysis + lia, then every
   remaining testbit leaf. *)
Ltac bits_cases :=
  repeat match goal with |- context [?a <? ?b] =>
    destruct (N.ltb_spec a b); try (exfalso; lia) end;
  repeat match goal with |- context [N.testbit ?c ?k] =>
    lazymatch c with Npos _ =>
      lazymatch k with Npos _ => fail | N0 => fail | _ =>
        let sz := eval vm_compute in (N.size c) in
        rewrite (testbit_const_high c k) by (change (N.size c) with sz; lia)
      end end end;
  cbn [andb orb negb];
  rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r, ?Bool.orb_true_r;
  cbn [andb orb negb];
  repeat match goal with |- context [N.testbit ?x ?k] =>
    lazymatch x with Npos _ => fail | N0 => fail | _ =>
      destruct (N.testbit x k) end end;
  cbn [andb orb negb];
  rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r, ?Bool.orb_true_r;
  try reflexivity.

(* Prove an equation between two bitwise expressions of width at most w
   whose leaves are opaque numbers or constants, by checking each of the
   w bits.  Bits at and above w must be shown false by the side tactic. *)
Ltac bitblast_upto w :=
  apply N.bits_inj; let i := fresh "i" in intro i;
  let IW := fresh "IW" in
  destruct (N.lt_ge_cases i w) as [IW|IW];
  [ let rec go k :=
      lazymatch eval compute in (k <? w) with
      | true => destruct (N.eq_dec i k) as [->|?];
                [ bits_close | let k1 := eval compute in (N.succ k) in go k1 ]
      | false => exfalso; lia
      end in go 0
  | bits_rewrite; bits_cases ].


(* ntohl32 facts (need bitblast_upto, defined above). *)
Lemma ntohl32_mod: forall x, ntohl32 x mod 2^32 = ntohl32 x.
Proof. intro x. unfold ntohl32. bitblast_upto 32. Qed.

Lemma ntohl32_lt: forall x, ntohl32 x < 2^32.
Proof. intro x. rewrite <- ntohl32_mod. apply N.mod_lt. discriminate. Qed.

(* musl's word-at-a-time zero-byte test.

   musl's string functions (strlen, memchr, strchrnul, stpcpy, ...) scan
   eight bytes at a time with
       #define ONES ((size_t)-1/UCHAR_MAX)          0x0101010101010101
       #define HIGHS (ONES * (UCHAR_MAX/2+1))       0x8080808080808080
       #define HASZERO(x) ((x)-ONES & ~(x) & HIGHS)
   The lifted form is  N.lnot x 64 .& (x ⊕ 0xfefefefefefefeff) .& HIGHS.
   HASZERO can report a zero byte that is not there (a 0x80 byte above a
   zero byte), but it never misses one, and that is the direction the loops
   rely on: haszero x = 0 implies all eight bytes of x are nonzero.

   Model:   Written by Claude Opus 5.5 (claude-opus-5-5), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi.
Open Scope N.

Definition haszero (x:N) :=
  (N.lnot x 64 .& (x ⊕ 0xfefefefefefefeff)) .& 0x8080808080808080.

Definition byte_of (x j:N) := xbits x (8*j) (8*j+8).

(* x mod 2^(8(k+1)) splits into its low k bytes and byte k. *)
Lemma mod_split_byte:
  forall x k, x mod 2^(8*k+8) = x mod 2^(8*k) + 2^(8*k) * byte_of x k.
Proof.
  intros. unfold byte_of, xbits. rewrite N.shiftr_div_pow2.
  replace (8*k+8 - 8*k) with 8 by lia.
  replace (2^(8*k+8)) with (2^(8*k) * 2^8) by (rewrite <- N.pow_add_r; reflexivity).
  apply N.mod_mul_r; apply N.pow_nonzero; discriminate.
Qed.

Fixpoint ones_nat (k:nat) : N :=
  match k with O => 0 | S k' => ones_nat k' + 2^(8 * N.of_nat k') end.
Definition ones_upto (k:N) := ones_nat (N.to_nat k).

(* sum_{j<k} 2^(8j) *)
Lemma ones_upto_succ: forall k, ones_upto (N.succ k) = ones_upto k + 2^(8*k).
Proof. intros. unfold ones_upto. rewrite N2Nat.inj_succ. cbn [ones_nat]. rewrite N2Nat.id. reflexivity. Qed.

Lemma low_bytes_ge:
  forall x k, (forall j, j < k -> byte_of x j <> 0) -> ones_upto k <= x mod 2^(8*k).
Proof.
  intros x k. induction k using N.peano_ind; intro NZ.
  - apply N.le_0_l.
  - rewrite ones_upto_succ. replace (8 * N.succ k) with (8*k+8) by lia.
    rewrite mod_split_byte.
    assert (B: byte_of x k <> 0) by (apply NZ; lia).
    specialize (IHk ltac:(intros; apply NZ; lia)).
    assert (P: 0 < 2^(8*k)) by (apply N.neq_0_lt_0, N.pow_nonzero; discriminate).
    nia.
Qed.

Lemma byte_of_lt: forall x j, byte_of x j < 256.
Proof. intros. unfold byte_of, xbits. replace (8*j+8-8*j) with 8 by lia. apply N.mod_lt. discriminate. Qed.

Lemma testbit_by_div: forall a n, (a / 2^n) mod 2 = 1 -> N.testbit a n = true.
Proof.
  intros a n H. pose proof (N.testbit_spec' a n) as T. rewrite H in T.
  destruct (N.testbit a n). reflexivity. discriminate.
Qed.

Ltac cases8 k K :=
  assert (KC: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia;
  repeat destruct KC as [KC|KC]; subst k.

(* The borrow lemma: if bytes 0..k-1 of x are nonzero and byte k is zero, then
   x - ONES has bit 8k+7 set. *)
Lemma borrow_bit:
  forall x k, x < 2^64 -> k < 8 ->
  (forall j, j < k -> byte_of x j <> 0) -> byte_of x k = 0 ->
  N.testbit (x ⊕ 0xfefefefefefefeff) (8*k+7) = true.
Proof.
  intros x k X K NZ Z.
  pose proof (low_bytes_ge x k NZ) as GE.
  pose proof (mod_split_byte x k) as SPL. rewrite Z, N.mul_0_r, N.add_0_r in SPL.
  apply testbit_by_div.
  clear NZ Z. cases8 k K; unfold ones_upto in GE; vm_compute ones_nat in GE;
    change (2^64) with 18446744073709551616 in *;
    repeat match goal with |- context [2^?n] =>
      let v := eval vm_compute in (2^n) in change (2^n) with v end;
    repeat match goal with H: context [2^?n] |- _ =>
      let v := eval vm_compute in (2^n) in change (2^n) with v in H end;
    lia.
Qed.

Lemma byte_zero_bit7: forall x k, byte_of x k = 0 -> N.testbit x (8*k+7) = false.
Proof.
  intros x k Z. unfold byte_of in Z.
  assert (T: N.testbit (xbits x (8*k) (8*k+8)) 7 = false) by (rewrite Z; reflexivity).
  rewrite xbits_spec in T. replace (7 + 8*k) with (8*k+7) in T by lia.
  replace (8*k+7 <? 8*k+8) with true in T by (symmetry; apply N.ltb_lt; lia).
  rewrite Bool.andb_true_r in T. exact T.
Qed.

(* HASZERO never misses a zero byte. *)
Theorem haszero_bytes:
  forall x, x < 2^64 -> haszero x = 0 -> forall j, j < 8 -> byte_of x j <> 0.
Proof.
  intros x X H.
  assert (ALL: forall k, k <= 8 -> forall j, j < k -> byte_of x j <> 0).
  { induction k using N.peano_ind; intros K j J. lia.
    destruct (N.lt_ge_cases j k) as [JK|JK]. apply IHk; lia.
    replace j with k by lia. intro Z.
    assert (B: N.testbit (haszero x) (8*k+7) = true).
    { unfold haszero. rewrite !N.land_spec, N.lnot_spec_low by (cases8 k K; vm_compute; reflexivity).
      rewrite byte_zero_bit7 by exact Z.
      rewrite borrow_bit by (try assumption; try lia; intros; apply IHk; lia).
      cases8 k K; reflexivity. }
    rewrite H in B. discriminate. }
  intros. apply (ALL 8); lia.
Qed.

(* The bytes of a loaded quadword are the bytes of memory. *)
Lemma byte_of_load: forall (m:memory) a j, j < 8 -> byte_of (m Ⓠ[a]) j = m Ⓑ[a ⊕ j].
Proof. intros. apply byte_of_getmem. assumption. Qed.

(* The form psimpl produces: x - ONES as msub. *)
Theorem haszero_bytes_msub:
  forall x, x < 2^64 ->
  N.lnot x 64 .& (x ⊖ 0x0101010101010101) .& 0x8080808080808080 = 0 ->
  forall j, j < 8 -> byte_of x j <> 0.
Proof.
  intros x X H. apply haszero_bytes. assumption.
  unfold haszero. rewrite <- H. reflexivity.
Qed.

(* Advancing a nil-free prefix by one HASZERO-clean quadword. *)
Theorem nilfree_add8:
  forall (m:memory) p k,
  (forall i, i < k -> m Ⓑ[p ⊕ i] <> 0) ->
  N.lnot (m Ⓠ[p + k]) 64 .& (m Ⓠ[p + k] ⊖ 0x0101010101010101) .& 0x8080808080808080 = 0 ->
  forall i, i < k + 8 -> m Ⓑ[p ⊕ i] <> 0.
Proof.
  intros m p k NF H i I. destruct (N.lt_ge_cases i k) as [IK|IK]. apply NF, IK.
  pose proof (haszero_bytes_msub _ (getmem_bound 64 LittleE 8 m (p + k)) H (i - k) ltac:(lia)) as B.
  rewrite byte_of_load in B by lia.
  rewrite !getmem_mod_l in *. replace (p + k + (i - k)) with (p + i) in B by lia. exact B.
Qed.

Lemma byte_of_lxor: forall a b j, byte_of (a .^ b) j = byte_of a j .^ byte_of b j.
Proof.
  intros. unfold byte_of. apply N.bits_inj. intro i.
  rewrite N.lxor_spec, !xbits_spec, N.lxor_spec.
  destruct (_ <? _); [rewrite !Bool.andb_true_r|rewrite !Bool.andb_false_r]; reflexivity.
Qed.

Lemma byte_of_bcast:
  forall c j, c < 256 -> j < 8 -> byte_of (c * 0x0101010101010101) j = c.
Proof. intros. apply (bcast8_byte c j); assumption. Qed.

Lemma lxor_neq0: forall a b, a .^ b <> 0 -> a <> b.
Proof. intros a b H E. subst. rewrite N.lxor_nilpotent in H. contradiction. Qed.

(* musl's strchrnul/memchr test HASZERO(w) | HASZERO(w ^ (c * ONES)). *)
Theorem haszero2_bytes:
  forall w c, w < 2^64 -> c < 256 ->
  ((w ⊖ 0x0101010101010101 .& N.lnot w 64) .|
   (N.lnot (w .^ c * 0x0101010101010101) 64 .& (w .^ c * 0x0101010101010101) ⊖ 0x0101010101010101))
  .& 0x8080808080808080 = 0 ->
  forall j, j < 8 -> byte_of w j <> 0 /\ byte_of w j <> c.
Proof.
  intros w c W C H j J.
  rewrite N.land_lor_distr_l in H. apply N.lor_eq_0_iff in H. destruct H as [H1 H2].
  rewrite (N.land_comm (w ⊖ _)) in H1.
  assert (X: w .^ c * 0x0101010101010101 < 2^64).
  { apply N.ltb_lt. destruct (N.ltb_spec (w .^ c * 0x0101010101010101) (2^64)) as [|G]. reflexivity.
    exfalso. assert (B: c * 0x0101010101010101 < 2^64) by lia.
    pose proof (lxor_bound 64 w (c * 0x0101010101010101) W B). lia. }
  split.
  - apply (haszero_bytes_msub w W H1 j J).
  - pose proof (haszero_bytes_msub _ X H2 j J) as B.
    rewrite byte_of_lxor, byte_of_bcast in B by assumption. apply lxor_neq0, B.
Qed.

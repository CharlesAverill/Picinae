(* Grok Bot (agent coqettu): memory extensionality helpers.
   getmem_ext: a multi-byte read only depends on the bytes it covers. *)
From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokStr GrokFrame.
Import ARM8Notations.
Open Scope N.

Lemma getmem_ext: ∀ w e len m1 m2 a,
  (∀ i, i < len -> getmem w LittleE 1 m1 (a + i) = getmem w LittleE 1 m2 (a + i)) ->
  getmem w e len m1 a = getmem w e len m2 a.
Proof.
  intros w e len. induction len using N.peano_ind; intros m1 m2 a H.
  - rewrite !getmem_0. reflexivity.
  - rewrite !getmem_succ.
    assert (B: getbyte m1 a w = getbyte m2 a w).
    { rewrite <- !(getmem_1 w LittleE). specialize (H 0). rewrite N.add_0_r in H. apply H. lia. }
    assert (R: getmem w e len m1 (N.succ a) = getmem w e len m2 (N.succ a)).
    { apply IHlen. intros i I. replace (N.succ a + i) with (a + N.succ i) by lia. apply H. lia. }
    rewrite B, R. reflexivity.
Qed.

(* byte i < k of the destination of a k-byte forward copy holds the source byte
   as read by the i-th copy step *)
Lemma bcp_read_in: ∀ m d q k i, i < N.of_nat k -> d + N.of_nat k <= 2^64 ->
  getmem 64 LittleE 1 (bcp m d q k) (d + i) = getmem 64 LittleE 1 (bcp m d q (N.to_nat i)) (q + i).
Proof.
  induction k; intros i I B. simpl in I; lia.
  change (2^64) with 18446744073709551616 in *. rewrite Nat2N.inj_succ in I, B.
  cbn [bcp]. destruct (N.eq_dec i (N.of_nat k)) as [->|NE].
  - rewrite getmem_setmem by (vm_compute; discriminate). rewrite Nat2N.id. apply N.mod_small. apply getmem_bound.
  - rewrite getmem_setmem_above by (change (2^64) with 18446744073709551616; lia). apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

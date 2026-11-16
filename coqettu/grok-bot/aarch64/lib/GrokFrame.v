From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokStr.
Import ARM8Notations.
Open Scope N.

(* A read of [a, a+len) is unaffected by a store to [b, b+lb) lying entirely
   below it (no address wrap). *)
Lemma getmem_setmem_below: ∀ len lb m a b v, 0 < lb -> b + lb <= a -> a < 2^64 -> a + len <= 2^64 ->
  getmem 64 LittleE len (setmem 64 LittleE lb m b v) a = getmem 64 LittleE len m a.
Proof.
  intros len lb m a b v H0 H1 A H2. change (2^64) with 18446744073709551616 in *.
  apply getmem_frame.
  - left. destruct (N.eq_dec len 0) as [->|NZ]. apply N.le_0_l.
    unfold msub; change (2^64) with 18446744073709551616. rewrite (N.mod_small a), N.mod_small by lia. lia.
  - left. unfold msub; change (2^64) with 18446744073709551616. rewrite (N.mod_small b) by lia.
    replace (a + (18446744073709551616 - b)) with ((a - b) + 1 * 18446744073709551616) by lia.
    rewrite N.Div0.mod_add, N.mod_small by lia. lia.
Qed.

Lemma getmem_setmem_above: ∀ len lb m a b v, a + len <= b -> b + lb <= 2^64 ->
  getmem 64 LittleE len (setmem 64 LittleE lb m b v) a = getmem 64 LittleE len m a.
Proof.
  intros len lb m a b v H1 H2. change (2^64) with 18446744073709551616 in *.
  destruct (N.eq_dec len 0) as [->|NZ]. apply getmem_frame; [left; apply N.le_0_l | right; reflexivity].
  destruct (N.eq_dec lb 0) as [->|NZ2]. apply getmem_frame; [right; reflexivity | left; apply N.le_0_l].
  apply getmem_frame.
  - left. unfold msub; change (2^64) with 18446744073709551616. rewrite (N.mod_small a) by lia.
    replace (b + (18446744073709551616 - a)) with ((b - a) + 1 * 18446744073709551616) by lia.
    rewrite N.Div0.mod_add, N.mod_small by lia. lia.
  - left. unfold msub; change (2^64) with 18446744073709551616. rewrite (N.mod_small b) by lia.
    rewrite N.mod_small by lia. lia.
Qed.

Lemma bcp_read_above: ∀ m e q k len a, e + N.of_nat k <= a -> a < 2^64 -> a + len <= 2^64 ->
  getmem 64 LittleE len (bcp m e q k) a = getmem 64 LittleE len m a.
Proof.
  induction k; intros len a H1 H0 H2. reflexivity.
  change (2^64) with 18446744073709551616 in *.
  cbn [bcp]. rewrite getmem_setmem_below by lia. apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

Lemma bcp_read_below: ∀ m e q k len a, a + len <= e -> e + N.of_nat k <= 2^64 ->
  getmem 64 LittleE len (bcp m e q k) a = getmem 64 LittleE len m a.
Proof.
  induction k; intros len a H1 H2. reflexivity.
  change (2^64) with 18446744073709551616 in *.
  cbn [bcp]. rewrite getmem_setmem_above by lia. apply IHk; change (2^64) with 18446744073709551616; lia.
Qed.

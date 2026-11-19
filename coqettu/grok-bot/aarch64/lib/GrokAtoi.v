(* GrokAtoi: specification helpers for musl's atoi/atol/atoll (Grok Bot /
   agent coqettu).  Written by Grok Bot (agent coqettu) and machine-checked
   by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia Bool.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokCtype GrokBits.
Import ARM8Notations.
Open Scope N.

(* C-locale isspace / isdigit on a byte value. *)
Definition is_ws (b:N) : bool := (b =? 32) || ((9 <=? b) && (b <=? 13)).
Definition is_dig (b:N) : bool := (48 <=? b) && (b <=? 57).

(* The i bytes at p are white space; the n bytes at q are decimal digits. *)
Definition ws_run (m:memory) (p:addr) (i:N) := ∀ j, j < i -> is_ws (m Ⓑ[p + j]) = true.
Definition dig_run (m:memory) (q:addr) (n:N) := ∀ j, j < n -> is_dig (m Ⓑ[q + j]) = true.

(* musl accumulates the NEGATIVE value: n = 10*n - (digit), in w-bit
   two's-complement arithmetic. *)
Fixpoint acc (w:N) (m:memory) (q:addr) (n:nat) : N :=
  match n with
  | O => 0
  | S n' => msub w (10 * acc w m q n') (m Ⓑ[q + N.of_nat n'] - 48)
  end.

(* Sign handling: index of the first digit and the final result. *)
Definition sgn_len (c:N) : N := if (c =? 43) || (c =? 45) then 1 else 0.
Definition atox_result (w:N) (m:memory) (p i:addr) (n:nat) : N :=
  let c := m Ⓑ[p + i] in
  let a := acc w m (p + i + sgn_len c) n in
  if c =? 45 then a else msub w 0 a.

Lemma ws_run_0: ∀ m p, ws_run m p 0.
Proof. intros m p j J. lia. Qed.

Lemma ws_run_succ: ∀ m p i, ws_run m p i -> is_ws (m Ⓑ[p + i]) = true -> ws_run m p (i+1).
Proof.
  intros m p i R W j J. destruct (N.lt_ge_cases j i). apply R; assumption.
  replace j with i by lia. exact W.
Qed.

Lemma dig_run_0: ∀ m q, dig_run m q 0.
Proof. intros m q j J. lia. Qed.

Lemma dig_run_succ: ∀ m q n, dig_run m q n -> is_dig (m Ⓑ[q + n]) = true -> dig_run m q (n+1).
Proof.
  intros m q n R W j J. destruct (N.lt_ge_cases j n). apply R; assumption.
  replace j with n by lia. exact W.
Qed.

Lemma acc_lt: ∀ w m q n, acc w m q n < 2^w.
Proof.
  intros w m q n. destruct n; simpl. apply N.neq_0_lt_0, N.pow_nonzero. discriminate.
  unfold msub. apply N.mod_lt, N.pow_nonzero. discriminate.
Qed.

(* Branch conditions as psimpl leaves them. *)
Lemma ws_bc: ∀ b, b < 2^8 ->
  N.lor (if 4 <=? msub 32 b 9 then 0 else 1) (if b =? 13 then 1 else 0) =
  if (9 <=? b) && (b <=? 13) then 1 else 0.
Proof.
  intros b B. pose proof (ls_test b 9 4 ltac:(lia) ltac:(lia)) as H.
  rewrite N.mod_small in H by lia. exact H.
Qed.

Lemma dig_bc: ∀ b, b < 2^8 ->
  N.lor (if 9 <=? msub 32 b 48 then 0 else 1) (if b =? 57 then 1 else 0) =
  if is_dig b then 1 else 0.
Proof.
  intros b B. pose proof (ls_test b 48 9 ltac:(lia) ltac:(lia)) as H.
  rewrite N.mod_small in H by lia. exact H.
Qed.

Lemma ptr_succ: ∀ p i, (1 + (p + i) mod 2^64) mod 2^64 = (p + (i + 1)) mod 2^64.
Proof. intros. rewrite N.add_mod_idemp_r by discriminate. f_equal. lia. Qed.

Lemma acc_step32: ∀ a b, 48 <= b <= 57 ->
  msub 32 (48 + ((a + (a << 2)) << 1)) b = msub 32 (10 * a) (b - 48).
Proof.
  intros a b B. rewrite !N.shiftl_mul_pow2. change (2^2) with 4. change (2^1) with 2.
  unfold msub. rewrite (N.mod_small b), (N.mod_small (b - 48)) by lia. f_equal. lia.
Qed.

Lemma acc_step64: ∀ a b, 48 <= b <= 57 ->
  msub 64 (48 + ((a + (a << 2)) << 1)) b = msub 64 (10 * a) (b - 48).
Proof.
  intros a b B. rewrite !N.shiftl_mul_pow2. change (2^2) with 4. change (2^1) with 2.
  unfold msub. rewrite (N.mod_small b), (N.mod_small (b - 48)) by lia. f_equal. lia.
Qed.

Lemma ptr_succ_nat: ∀ q n, (1 + (q + N.of_nat n) mod 2^64) mod 2^64 = (q + N.of_nat (S n)) mod 2^64.
Proof. intros. rewrite ptr_succ. f_equal. lia. Qed.

Lemma is_dig_bounds: ∀ b, is_dig b = true -> 48 <= b <= 57.
Proof. unfold is_dig. intros b H. apply andb_prop in H as [H1 H2]. apply N.leb_le in H1, H2. lia. Qed.

Lemma ws_from_bc: ∀ b, (b =? 32) = true \/ (if (9 <=? b) && (b <=? 13) then 1 else 0) ≠ 0 -> is_ws b = true.
Proof.
  unfold is_ws. intros b [H|H]. rewrite H. reflexivity.
  destruct ((9 <=? b) && (b <=? 13)). apply orb_true_r. contradiction.
Qed.

Lemma nws_from_bc: ∀ b, (b =? 32) = false -> (if (9 <=? b) && (b <=? 13) then 1 else 0) = 0 -> is_ws b = false.
Proof.
  unfold is_ws. intros b H1 H2. rewrite H1. destruct ((9 <=? b) && (b <=? 13)). discriminate. reflexivity.
Qed.

(* atol/atoll: "sub x1,x1,w2,SXTW" leaves a sign-extension of the digit. *)
Lemma acc_step64sx: ∀ a b, 48 <= b <= 57 ->
  msub 64 ((a + (a << 2)) << 1) (scast 32 64 ((msub 32 b 48 >> 0) mod 2^32)) =
  msub 64 (10 * a) (b - 48).
Proof.
  intros a b B. rewrite (msub_small 32 b 48) by lia. rewrite N.shiftr_0_r, (N.mod_small (b - 48)) by lia.
  rewrite scast_small32 by lia.
  rewrite !N.shiftl_mul_pow2. change (2^2) with 4. change (2^1) with 2.
  f_equal. lia.
Qed.

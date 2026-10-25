Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import amd64_common.
Open Scope N.

(* Shared definitions for the termios speed setters (cfsetospeed,
   cfsetispeed).  Written by Claude Opus 5.5 (claude-opus-5-5) and checked by
   Rocq.

   glibc's struct termios on Linux/x86-64: c_iflag at 0, c_oflag at 4,
   c_cflag at 8, c_lflag at 12, c_line at 16, c_cc[32] at 17, c_ispeed at 52,
   c_ospeed at 56.  CBAUD = 0x100f; ~CBAUD = 0xffffeff0.  IBAUD0 = 2^31 is a
   glibc-private c_iflag bit meaning "input speed follows output speed". *)

Definition errno_slot := 0x319e10.
Definition einval (m:memory) (fs:N) := m [Ⓓ fs ⊕ m Ⓠ[errno_slot] := 22].

(* A speed the binary accepts: anything inside CBAUD (B0..B38400, and also
   0x1000 = BOTHER), or B57600..B4000000 (0x1001..0x100f). *)
Definition speed_ok (n:N) := n .& 0xffffeff0 = 0 \/ 0x1001 <= n <= 0x100f.

(* The lifted unsigned "speed - 0x1001 <= 14" test (JA not taken). *)
Lemma speed_range: forall b,
  ((msub 32 b 4097 <? 14) || (b mod 2^32 =? 4111)) = (4097 <=? b mod 2^32) && (b mod 2^32 <=? 4111).
Proof.
  intro b. unfold msub. rewrite <- N.add_mod_idemp_l by discriminate.
  pose proof (N.mod_lt b (2^32) ltac:(discriminate)).
  remember (b mod 2^32) as n. clear Heqn. change (2^32) with 4294967296 in *.
  change (4097 mod 4294967296) with 4097.
  destruct (N.ltb_spec n 4097).
  - rewrite N.mod_small by lia. destruct (N.ltb_spec (n + (4294967296 - 4097)) 14); [lia|].
    destruct (N.eqb_spec n 4111); [lia|]. destruct (N.leb_spec 4097 n); [lia|reflexivity].
  - replace (n + (4294967296 - 4097)) with ((n - 4097) + 1 * 4294967296) by lia.
    rewrite N.mod_add, N.mod_small by lia.
    destruct (N.ltb_spec (n - 4097) 14), (N.eqb_spec n 4111), (N.leb_spec n 4111); cbn; lia.
Qed.

Lemma mask_mod: forall b, b .& 0xffffeff0 = (b mod 2^32) .& 0xffffeff0.
Proof. intro. symmetry. apply land_mod32. reflexivity. Qed.

(* The stored c_cflag: (old & ~CBAUD) | speed, truncated to 32 bits. *)
Lemma cflag_mod: forall x b,
  (x .& 0xffffeff0 .| b) mod 2^32 = x .& 0xffffeff0 .| b mod 2^32.
Proof.
  intros x b. apply N.bits_inj. intro i. rewrite N.lor_spec.
  destruct (N.ltb_spec i 32).
  - rewrite !N.mod_pow2_bits_low by lia. apply N.lor_spec.
  - rewrite !N.mod_pow2_bits_high by lia. rewrite N.land_spec.
    rewrite (N.bits_above_log2 0xffffeff0 i), Bool.andb_false_r. reflexivity.
    replace (N.log2 0xffffeff0) with 31 by reflexivity. lia.
Qed.

(* The JA after "CMP speed-0x1001, 14", as lifted (CF | ZF). *)
Lemma ja_speed_not_taken: forall b,
  ((if msub 32 b 4097 <? 14 then 1 else 0) .| (if b mod 2^32 =? 4111 then 1 else 0)) .^ 1 = 0 ->
  4097 <= b mod 2^32 <= 4111.
Proof.
  intros b H. pose proof (speed_range b) as R.
  destruct (msub 32 b 4097 <? 14), (b mod 2^32 =? 4111); try discriminate H;
  symmetry in R; apply Bool.andb_true_iff in R; destruct R as [R1 R2];
  apply N.leb_le in R1, R2; lia.
Qed.

Lemma ja_speed_taken: forall b p,
  ((if msub 32 b 4097 <? 14 then 1 else 0) .| (if b mod 2^32 =? 4111 then 1 else 0)) .^ 1 = N.pos p ->
  ~ (4097 <= b mod 2^32 <= 4111).
Proof.
  intros b p H. pose proof (speed_range b) as R.
  destruct (msub 32 b 4097 <? 14), (b mod 2^32 =? 4111); try discriminate H.
  symmetry in R. apply Bool.andb_false_iff in R.
  destruct R as [R|R]; apply N.leb_gt in R; lia.
Qed.

(* Rewriting a dword store of the raw register into one of its low 32 bits. *)
Lemma setmem_dword: forall (m:memory) p v, m [Ⓓ p := v] = m [Ⓓ p := v mod 2^32].
Proof. intros. symmetry. apply (setmem_mod_r 64 LittleE 4). Qed.

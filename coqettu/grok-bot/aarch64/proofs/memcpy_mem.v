(* memcpy (n <= 128): the memory effect of each size class.
   Written by Grok Bot (agent coqettu); machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokStr GrokFill GrokCopy.
From Grok.proofs Require Import memcpy_defs.
Import ARM8Notations.
Open Scope N.

Ltac copied_tac :=
  intros; unfold copied; split;
  [ intros i I; addr_norm; copy_byte | intros a A O; addr_norm; copy_byte ].

Lemma cp_16_32: ∀ mem d src n, 16 <= n <= 32 -> d + n < 2^64 -> src + n < 2^64 ->
  copied mem (mem [Ⓠ d := mem Ⓠ[src]] [Ⓠ 8 + d := mem Ⓠ[8 + src]] [Ⓠ d ⊖ 16 + n := mem Ⓠ[src ⊖ 16 + n]] [Ⓠ d ⊖ 8 + n := mem Ⓠ[src ⊖ 8 + n]]) src d n.
Proof.
  intros mem d src n C D S.
  copied_tac.
Qed.

Lemma cp_8_15: ∀ mem d src n, 8 <= n < 16 -> d + n < 2^64 -> src + n < 2^64 ->
  copied mem (mem [Ⓠ d := mem Ⓠ[src]] [Ⓠ d ⊖ 8 + n := mem Ⓠ[src ⊖ 8 + n]]) src d n.
Proof.
  intros mem d src n C D S.
  copied_tac.
Qed.

Lemma cp_4_7: ∀ mem d src n, 4 <= n < 8 -> d + n < 2^64 -> src + n < 2^64 ->
  copied mem (mem [Ⓓ d := mem Ⓓ[src]] [Ⓓ d ⊖ 4 + n := mem Ⓓ[src ⊖ 4 + n]]) src d n.
Proof.
  intros mem d src n C D S.
  copied_tac.
Qed.

Lemma cp_1_3: ∀ mem d src n, 1 <= n < 4 -> d + n < 2^64 -> src + n < 2^64 ->
  copied mem (mem [Ⓑ d := mem Ⓑ[src]] [Ⓑ d + n / 2^1 := mem Ⓑ[src + n / 2^1]] [Ⓑ d ⊖ 1 + n := mem Ⓑ[src ⊖ 1 + n]]) src d n.
Proof.
  intros mem d src n C D S.
  pose proof (N.div_mod n (2^1) ltac:(discriminate)); pose proof (N.mod_lt n (2^1) ltac:(discriminate));
  change (2^1) with 2 in *.
  copied_tac.
Qed.

Lemma cp_33_64: ∀ mem d src n, 32 < n <= 64 -> d + n < 2^64 -> src + n < 2^64 ->
  copied mem (mem [Ⓠ d := mem Ⓠ[src]] [Ⓠ 8 + d := mem Ⓠ[8 + src]] [Ⓠ 16 + d := mem Ⓠ[16 + src]] [Ⓠ 24 + d := mem Ⓠ[24 + src]] [Ⓠ d ⊖ 32 + n := mem Ⓠ[src ⊖ 32 + n]] [Ⓠ d ⊖ 24 + n := mem Ⓠ[src ⊖ 24 + n]] [Ⓠ d ⊖ 16 + n := mem Ⓠ[src ⊖ 16 + n]] [Ⓠ d ⊖ 8 + n := mem Ⓠ[src ⊖ 8 + n]]) src d n.
Proof.
  intros mem d src n C D S.
  copied_tac.
Qed.

Lemma cp_65_96: ∀ mem d src n, 64 < n <= 96 -> d + n < 2^64 -> src + n < 2^64 ->
  copied mem (mem [Ⓠ d := mem Ⓠ[src]] [Ⓠ 8 + d := mem Ⓠ[8 + src]] [Ⓠ 16 + d := mem Ⓠ[16 + src]] [Ⓠ 24 + d := mem Ⓠ[24 + src]] [Ⓠ 32 + d := mem Ⓠ[32 + src]] [Ⓠ 40 + d := mem Ⓠ[40 + src]] [Ⓠ 48 + d := mem Ⓠ[48 + src]] [Ⓠ 56 + d := mem Ⓠ[56 + src]] [Ⓠ d ⊖ 32 + n := mem Ⓠ[src ⊖ 32 + n]] [Ⓠ d ⊖ 24 + n := mem Ⓠ[src ⊖ 24 + n]] [Ⓠ d ⊖ 16 + n := mem Ⓠ[src ⊖ 16 + n]] [Ⓠ d ⊖ 8 + n := mem Ⓠ[src ⊖ 8 + n]]) src d n.
Proof.
  intros mem d src n C D S.
  copied_tac.
Qed.

Lemma cp_97_128: ∀ mem d src n, 96 < n <= 128 -> d + n < 2^64 -> src + n < 2^64 ->
  copied mem (mem [Ⓠ d ⊖ 64 + n := mem Ⓠ[src ⊖ 64 + n]] [Ⓠ d ⊖ 56 + n := mem Ⓠ[src ⊖ 56 + n]] [Ⓠ d ⊖ 48 + n := mem Ⓠ[src ⊖ 48 + n]] [Ⓠ d ⊖ 40 + n := mem Ⓠ[src ⊖ 40 + n]] [Ⓠ d := mem Ⓠ[src]] [Ⓠ 8 + d := mem Ⓠ[8 + src]] [Ⓠ 16 + d := mem Ⓠ[16 + src]] [Ⓠ 24 + d := mem Ⓠ[24 + src]] [Ⓠ 32 + d := mem Ⓠ[32 + src]] [Ⓠ 40 + d := mem Ⓠ[40 + src]] [Ⓠ 48 + d := mem Ⓠ[48 + src]] [Ⓠ 56 + d := mem Ⓠ[56 + src]] [Ⓠ d ⊖ 32 + n := mem Ⓠ[src ⊖ 32 + n]] [Ⓠ d ⊖ 24 + n := mem Ⓠ[src ⊖ 24 + n]] [Ⓠ d ⊖ 16 + n := mem Ⓠ[src ⊖ 16 + n]] [Ⓠ d ⊖ 8 + n := mem Ⓠ[src ⊖ 8 + n]]) src d n.
Proof.
  intros mem d src n C D S.
  copied_tac.
Qed.

Lemma cp_0: ∀ mem d src n, n = 0 -> copied mem mem src d n.
Proof. intros mem d src n Z. subst n. split; intros; [lia | reflexivity]. Qed.

Ltac pow_lits := repeat match goal with H: context [2 ^ ?k] |- _ =>
  let v := eval compute in (2 ^ k) in change (2 ^ k) with v in H end.

Ltac nstores M := match M with setmem _ _ _ ?m _ _ => let k := nstores m in constr:(S k) | _ => constr:(O) end.

(* pick the size-class lemma by the shape of the store chain *)
Ltac apply_cp :=
  match goal with |- copied _ ?M _ _ _ =>
    let k := nstores M in
    lazymatch k with
    | 0%nat => apply cp_0
    | 3%nat => apply cp_1_3
    | 2%nat => lazymatch M with setmem _ _ 4 _ _ _ => apply cp_4_7 | _ => apply cp_8_15 end
    | 4%nat => apply cp_16_32
    | 8%nat => apply cp_33_64
    | 12%nat => apply cp_65_96
    | 16%nat => apply cp_97_128
    end
  end.

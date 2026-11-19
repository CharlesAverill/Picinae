(* memcpy n > 128: store-chain coverage lemmas.
   Written by Grok Bot (agent coqettu); machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokStr GrokFrame GrokFill GrokMem GrokCopy.
From Grok.proofs Require Import memcpy_defs.
From Grok.lib Require Import GrokCov.
Import ARM8Notations.
Open Scope N.

Lemma cov_step: ∀ mem M s d n C C' j, cov mem M s d n C ->
  (∀ i, i < n -> C' i -> C i \/ (j <= i /\ i < j + 8)) -> j + 8 <= n -> d + n < 2^64 ->
  cov mem (setmem 64 LittleE 8 M (d + j) (mem Ⓠ[s + j])) s d n C'.
Proof.
  intros mem M s d n C C' j H HC J D. eapply cov_mono. apply cov_store8; eassumption. exact HC.
Qed.

Lemma cov_entry2: ∀ mem M s d n L b1 v1 b2 v2, cov mem M s d n (fun i => i < L) -> 16 + L <= n -> d + n < 2^64 ->
  b1 = d + (L) -> v1 = mem Ⓠ[s + (L)] -> b2 = d + (L + 8) -> v2 = mem Ⓠ[s + (L + 8)] ->
  cov mem (M [Ⓠ b1 := v1] [Ⓠ b2 := v2]) s d n (fun i => i < L + 16).
Proof.
  intros mem M s d n L b1 v1 b2 v2 C0 HY D E1 F1 E2 F2.
  subst b1 v1. subst b2 v2.
  apply (cov_mono _ _ _ _ _ (fun i => i < L + 16)); [| intros i I Ci; cbv beta in *; lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 8) _ (L + 8)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L) _ (L)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  exact C0.
Qed.

Lemma cov_loop8: ∀ mem M s d n L b1 v1 b2 v2 b3 v3 b4 v4 b5 v5 b6 v6 b7 v7 b8 v8, cov mem M s d n (fun i => i < L) -> L + 64 <= n -> d + n < 2^64 ->
  b1 = d + (L) -> v1 = mem Ⓠ[s + (L)] -> b2 = d + (L + 8) -> v2 = mem Ⓠ[s + (L + 8)] -> b3 = d + (L + 16) -> v3 = mem Ⓠ[s + (L + 16)] -> b4 = d + (L + 24) -> v4 = mem Ⓠ[s + (L + 24)] -> b5 = d + (L + 32) -> v5 = mem Ⓠ[s + (L + 32)] -> b6 = d + (L + 40) -> v6 = mem Ⓠ[s + (L + 40)] -> b7 = d + (L + 48) -> v7 = mem Ⓠ[s + (L + 48)] -> b8 = d + (L + 56) -> v8 = mem Ⓠ[s + (L + 56)] ->
  cov mem (M [Ⓠ b1 := v1] [Ⓠ b2 := v2] [Ⓠ b3 := v3] [Ⓠ b4 := v4] [Ⓠ b5 := v5] [Ⓠ b6 := v6] [Ⓠ b7 := v7] [Ⓠ b8 := v8]) s d n (fun i => i < L + 64).
Proof.
  intros mem M s d n L b1 v1 b2 v2 b3 v3 b4 v4 b5 v5 b6 v6 b7 v7 b8 v8 C0 HY D E1 F1 E2 F2 E3 F3 E4 F4 E5 F5 E6 F6 E7 F7 E8 F8.
  subst b1 v1. subst b2 v2. subst b3 v3. subst b4 v4. subst b5 v5. subst b6 v6. subst b7 v7. subst b8 v8.
  apply (cov_mono _ _ _ _ _ (fun i => i < L + 64)); [| intros i I Ci; cbv beta in *; lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 56) _ (L + 56)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 48) _ (L + 48)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 40) _ (L + 40)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 32) _ (L + 32)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 24) _ (L + 24)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 16) _ (L + 16)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 8) _ (L + 8)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L) _ (L)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  exact C0.
Qed.

Lemma cov_tail16: ∀ mem M s d n L b1 v1 b2 v2 b3 v3 b4 v4 b5 v5 b6 v6 b7 v7 b8 v8 b9 v9 b10 v10 b11 v11 b12 v12 b13 v13 b14 v14 b15 v15 b16 v16, cov mem M s d n (fun i => i < L) -> (L + 64 < n /\ n <= L + 128) -> d + n < 2^64 ->
  b1 = d + (L) -> v1 = mem Ⓠ[s + (L)] -> b2 = d + (L + 8) -> v2 = mem Ⓠ[s + (L + 8)] -> b3 = d + (L + 16) -> v3 = mem Ⓠ[s + (L + 16)] -> b4 = d + (L + 24) -> v4 = mem Ⓠ[s + (L + 24)] -> b5 = d + (L + 32) -> v5 = mem Ⓠ[s + (L + 32)] -> b6 = d + (L + 40) -> v6 = mem Ⓠ[s + (L + 40)] -> b7 = d + (L + 48) -> v7 = mem Ⓠ[s + (L + 48)] -> b8 = d + (L + 56) -> v8 = mem Ⓠ[s + (L + 56)] -> b9 = d + (n - 64) -> v9 = mem Ⓠ[s + (n - 64)] -> b10 = d + (n - 56) -> v10 = mem Ⓠ[s + (n - 56)] -> b11 = d + (n - 48) -> v11 = mem Ⓠ[s + (n - 48)] -> b12 = d + (n - 40) -> v12 = mem Ⓠ[s + (n - 40)] -> b13 = d + (n - 32) -> v13 = mem Ⓠ[s + (n - 32)] -> b14 = d + (n - 24) -> v14 = mem Ⓠ[s + (n - 24)] -> b15 = d + (n - 16) -> v15 = mem Ⓠ[s + (n - 16)] -> b16 = d + (n - 8) -> v16 = mem Ⓠ[s + (n - 8)] ->
  copied mem (M [Ⓠ b1 := v1] [Ⓠ b2 := v2] [Ⓠ b3 := v3] [Ⓠ b4 := v4] [Ⓠ b5 := v5] [Ⓠ b6 := v6] [Ⓠ b7 := v7] [Ⓠ b8 := v8] [Ⓠ b9 := v9] [Ⓠ b10 := v10] [Ⓠ b11 := v11] [Ⓠ b12 := v12] [Ⓠ b13 := v13] [Ⓠ b14 := v14] [Ⓠ b15 := v15] [Ⓠ b16 := v16]) s d n.
Proof.
  intros mem M s d n L b1 v1 b2 v2 b3 v3 b4 v4 b5 v5 b6 v6 b7 v7 b8 v8 b9 v9 b10 v10 b11 v11 b12 v12 b13 v13 b14 v14 b15 v15 b16 v16 C0 HY D E1 F1 E2 F2 E3 F3 E4 F4 E5 F5 E6 F6 E7 F7 E8 F8 E9 F9 E10 F10 E11 F11 E12 F12 E13 F13 E14 F14 E15 F15 E16 F16.
  subst b1 v1. subst b2 v2. subst b3 v3. subst b4 v4. subst b5 v5. subst b6 v6. subst b7 v7. subst b8 v8. subst b9 v9. subst b10 v10. subst b11 v11. subst b12 v12. subst b13 v13. subst b14 v14. subst b15 v15. subst b16 v16.
  apply (cov_copied _ _ _ _ _ (fun i => i < L + 64 \/ (n - 64 <= i /\ i < n - 0))); [| intros i I; lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 64 \/ (n - 64 <= i /\ i < n - 8)) _ (n - 8)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 64 \/ (n - 64 <= i /\ i < n - 16)) _ (n - 16)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 64 \/ (n - 64 <= i /\ i < n - 24)) _ (n - 24)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 64 \/ (n - 64 <= i /\ i < n - 32)) _ (n - 32)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 64 \/ (n - 64 <= i /\ i < n - 40)) _ (n - 40)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 64 \/ (n - 64 <= i /\ i < n - 48)) _ (n - 48)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 64 \/ (n - 64 <= i /\ i < n - 56)) _ (n - 56)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 64) _ (n - 64)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 56) _ (L + 56)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 48) _ (L + 48)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 40) _ (L + 40)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 32) _ (L + 32)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 24) _ (L + 24)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 16) _ (L + 16)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L + 8) _ (L + 8)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  apply (cov_step _ _ _ _ _ (fun i => i < L) _ (L)); [| intros i I Ci; cbv beta in *; lia | lia | lia].
  exact C0.
Qed.

Ltac cov_side := first [ lia | apply (f_equal (getmem 64 LittleE 8 _)); lia ].

Ltac cov_close :=
  first
  [ eapply cov_mono;
    [ first [ eapply cov_loop8 | eapply cov_entry2 ];
      [ first [ eassumption | apply cov_init0 ] | cov_side .. ]
    | intros i I Ci; cbv beta in *; lia ]
  | eapply cov_tail16; [ eassumption | cov_side .. ] ].

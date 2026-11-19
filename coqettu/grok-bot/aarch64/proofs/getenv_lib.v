(* getenv: helper lemmas (scan uniqueness, frame reads, skip/match, strncmp result) and closers.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in getenv_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokFrame.
From Grok.proofs Require strchrnul_proof.
From Grok.proofs Require Import getenv_defs.
Import ARM8Notations.
Open Scope N.

Lemma scan_unique: ∀ m p c k L,
  strchrnul_proof.scan m p c k -> (m Ⓑ[p + k] = 0 \/ m Ⓑ[p + k] = c) ->
  strchrnul_proof.scan m p c L -> (m Ⓑ[p + L] = 0 \/ m Ⓑ[p + L] = c) -> k = L.
Proof.
  intros m p c k L SK TK SL TL.
  destruct (N.lt_trichotomy k L) as [H|[H|H]]; [|exact H|].
  - destruct (SL k H) as [A B]. destruct TK; contradiction.
  - destruct (SK L H) as [A B]. destruct TL; contradiction.
Qed.

Lemma gv_rd: ∀ sp mem raddr x19 x20 x21 x29, 48 <= sp -> sp < 2^64 ->
  raddr < 2^64 -> x19 < 2^64 -> x20 < 2^64 -> x21 < 2^64 -> x29 < 2^64 ->
  gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 48] = x29 /\
  gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 40] = raddr /\
  gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 32] = x19 /\
  gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 24] = x20 /\
  gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 16] = x21.
Proof.
  intros. unfold gv_M, gv_frame. rewrite !msub_small by lia.
  repeat split;
  repeat first
   [ rewrite getmem_setmem by (rewrite ?N.mod_small; lia); apply N.mod_small; assumption
   | rewrite getmem_setmem_below by lia
   | rewrite getmem_setmem_above by lia ].
Qed.

Lemma skip_0: ∀ m name E l, gv_skip m name E l 0.
Proof. intros m name E l i H. destruct i; discriminate. Qed.

Lemma skip_succ: ∀ m name E l j, gv_skip m name E l j -> env_entry m E j ≠ 0 ->
  ¬ gv_match m name (env_entry m E j) l -> gv_skip m name E l (j+1).
Proof.
  intros m name E l j SK NZ NM i I. destruct (N.lt_ge_cases i j). apply SK; assumption.
  replace i with j by lia. split; assumption.
Qed.

Lemma env_adv: ∀ E j, (E ⊕ 8 * j) ⊕ 8 = E ⊕ 8 * (j + 1).
Proof. intros. rewrite N.Div0.add_mod_idemp_l. f_equal. lia. Qed.

Lemma msub32_byte0: ∀ a b, a < 2^8 -> b < 2^8 -> msub 32 a b = 0 -> a = b.
Proof.
  intros a b A B H. unfold msub in H.
  destruct (N.le_gt_cases b a).
  - replace (a + (2^32 - b mod 2^32)) with ((a - b) + 1 * 2^32) in H.
    rewrite N.Div0.mod_add, N.mod_small in H by (change (2^32) with 4294967296 in *; lia). lia.
    rewrite (N.mod_small b) by (change (2^32) with 4294967296 in *; lia). change (2^32) with 4294967296 in *; lia.
  - rewrite (N.mod_small b), N.mod_small in H; change (2^32) with 4294967296 in *; lia.
Qed.

(* strncmp(name, e, L) == 0 with name nil-free over L bytes iff the first L bytes agree. *)
Lemma sn_zero: ∀ m p q L k, 0 < L -> nilfree m p L -> k < L -> mem_eq m p q k ->
  (m Ⓑ[p + k] ≠ m Ⓑ[q + k] \/ m Ⓑ[p + k] = 0 \/ k = L - 1) ->
  msub 32 (m Ⓑ[p + k]) (m Ⓑ[q + k]) = 0 -> mem_eq m p q L.
Proof.
  intros m p q L k LP NF KL EQ ST Z.
  apply msub32_byte0 in Z; try apply byte_lt8.
  destruct ST as [ST|[ST|ST]]. contradiction. exfalso; exact (NF k KL ST).
  replace L with (k+1) by lia. apply mem_eq_succ; assumption.
Qed.

Lemma sn_nonzero: ∀ m p q L k, k < L ->
  msub 32 (m Ⓑ[p + k]) (m Ⓑ[q + k]) ≠ 0 -> ¬ mem_eq m p q L.
Proof.
  intros m p q L k KL NZ EQ. apply NZ. rewrite (EQ k KL).
  pose proof (byte_lt8 m (q + k)) as B. unfold msub.
  rewrite (N.mod_small (m Ⓑ[q + k])) by (change (2^32) with 4294967296; change (2^8) with 256 in B; lia).
  replace (m Ⓑ[q + k] + (2^32 - m Ⓑ[q + k])) with (2^32) by (change (2^32) with 4294967296; change (2^8) with 256 in B; lia).
  apply N.Div0.mod_same.
Qed.

Ltac gv_bools :=
  repeat match goal with
  | H: negb _ = false |- _ => apply Bool.negb_false_iff in H
  | H: negb _ = true |- _ => apply Bool.negb_true_iff in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end;
  rewrite ?N.shiftr_0_r in *;
  repeat match goal with H: context [ (getmem 64 LittleE 1 ?m ?a) mod 2^32 ] |- _ =>
    rewrite (N.mod_small (getmem 64 LittleE 1 m a) (2^32)) in H by apply byte_lt32 end.

(* Different strncmp argument q / saved X19 per loop iteration: same invariant-set family. *)
Lemma gv_sf: ∀ sp mem raddr x19 x20 x21 x29 name L q k19 q' k19',
  same_invset_family (invs sp mem raddr x19 x20 x21 x29 name L q k19) (invs sp mem raddr x19 x20 x21 x29 name L q' k19').
Proof. intros. reflexivity. Qed.

Lemma msub32_mod: ∀ a b, msub 32 a b mod 2^32 = msub 32 a b.
Proof. intros. unfold msub. apply N.Div0.mod_mod. Qed.

Lemma env_adv8: ∀ E j, (8 + (E + 8 * j) mod 2^64) mod 2^64 = (E + 8 * (j + 1)) mod 2^64.
Proof. intros. rewrite N.Div0.add_mod_idemp_r. f_equal. lia. Qed.

Lemma scan_nf: ∀ m p c L, strchrnul_proof.scan m p c L -> nilfree m p L.
Proof. intros m p c L SC i I. apply (SC i I). Qed.

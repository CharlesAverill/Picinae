(* Byte copies whose frame memory differs from the source memory: cpk m mb M
   d s k says the k bytes at d in M are the k bytes at s in m, and that M
   agrees with mb everywhere else.  Callers that push registers use mb = m
   with their pushes, so the saved registers can be read back through the
   frame while the source is still compared against the original memory
   (as strncat_proof.v's cpb).  Used by memccpy and strlcpy.

   Model:   Written by Claude Fable 5.1 (claude-fable-5-1), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_haszero CoqEtTu.lib.x64_compose.
Open Scope N.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *;
  change (2^63) with 9223372036854775808 in *; lia.

Definition cpk (m mb M:memory) (d s k:N) :=
  (forall i, i < k -> M Ⓑ[d ⊕ i] = m Ⓑ[s ⊕ i]) /\
  (forall b, ~ (msub 64 b d < k) -> M Ⓑ[b] = mb Ⓑ[b]).

(* the postcondition shape: j bytes copied, everything else unchanged except
   the F bytes below rsp *)
Definition copied_sf (m M:memory) (d s j rsp F:N) :=
  (forall i, i < j -> M Ⓑ[d ⊕ i] = m Ⓑ[s ⊕ i]) /\
  (forall b, ~ (msub 64 b d < j) -> F <= msub 64 b (rsp ⊖ F) -> M Ⓑ[b] = m Ⓑ[b]).

Lemma cpk_empty: forall m mb d s, cpk m mb mb d s 0.
Proof. intros. split. intros i I. lia. reflexivity. Qed.

Lemma cpk_copied_sf:
  forall m mb M d s j rsp F, cpk m mb M d s j ->
  (forall b, F <= msub 64 b (rsp ⊖ F) -> mb Ⓑ[b] = m Ⓑ[b]) -> copied_sf m M d s j rsp F.
Proof.
  intros m mb M d s j rsp F [C Fr] MB. split. exact C.
  intros b B1 B2. rewrite Fr by exact B1. apply MB, B2.
Qed.

(* an address of x's n bytes is outside the F bytes below rsp *)
Lemma outside_sf:
  forall x n rsp F i, ~ overlap 64 x n (rsp ⊖ F) F -> i < n -> F <= msub 64 (x ⊕ i) (rsp ⊖ F).
Proof.
  intros x n rsp F i NOV I. assert (BB: rsp ⊖ F < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ F) in *. clearbody b.
  destruct (N.le_gt_cases F (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D. mlia.
Qed.

(* a source byte is intact: it is outside the copied prefix (disjoint areas),
   and the frame memory agrees with the original there *)
Lemma cpk_src:
  forall m mb M d s n k j, cpk m mb M d s k -> k <= n -> ~ overlap 64 d n s n -> j < n ->
  mb Ⓑ[s ⊕ j] = m Ⓑ[s ⊕ j] -> M Ⓑ[s ⊕ j] = m Ⓑ[s ⊕ j].
Proof.
  intros m mb M d s n k j [_ F] KN NOV J MB. rewrite <- MB. apply F. intro H. apply NOV.
  exists (msub 64 (s ⊕ j) d), j. split. lia. split. exact J. mlia.
Qed.

Lemma cpk_src8:
  forall m mb M d s n k o, cpk m mb M d s k -> k <= n -> ~ overlap 64 d n s n -> o + 8 <= n ->
  (forall j, j < n -> mb Ⓑ[s ⊕ j] = m Ⓑ[s ⊕ j]) -> M Ⓠ[s + o] = m Ⓠ[s + o].
Proof.
  intros m mb M d s n k o CP KN NOV O MB. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE).
  rewrite <- (getmem_mod_l 64 LittleE 1 M a), <- (getmem_mod_l 64 LittleE 1 m a).
  replace (a mod 2^64) with (s ⊕ (o + msub 64 a (s + o))) by mlia.
  apply (cpk_src m mb M d s n k); try assumption. lia. apply MB. lia.
Qed.

Lemma cpk_store:
  forall m mb M d s n k a v, cpk m mb M d s k -> k < n -> n < 2^63 ->
  a mod 2^64 = (d + k) mod 2^64 -> v mod 2^8 = m Ⓑ[s ⊕ k] ->
  cpk m mb (setmem 64 LittleE 1 M a v) d s (k + 1).
Proof.
  intros m mb M d s n k a v [C F] K NB A V. split.
  - intros i I. destruct (N.lt_ge_cases i k) as [IK|IK].
    + rewrite getmem_noverlap. apply C, IK.
      intros [x [y [X [Y E]]]]. mlia.
    + replace i with k by lia.
      rewrite <- A, getmem_mod_l, getmem_setmem by discriminate. exact V.
  - intros b B. rewrite getmem_noverlap. apply F. lia.
    intros [x [y [X [Y E]]]]. apply B. mlia.
Qed.

Lemma cpk_store8:
  forall m mb M d s n k a v, cpk m mb M d s k -> k + 8 <= n -> n < 2^63 ->
  a mod 2^64 = (d + k) mod 2^64 -> v = m Ⓠ[s + k] ->
  cpk m mb (setmem 64 LittleE 8 M a v) d s (k + 8).
Proof.
  intros m mb M d s n k a v [C F] K NB A V. split.
  - intros i I. destruct (N.lt_ge_cases i k) as [IK|IK].
    + rewrite getmem_noverlap. apply C, IK.
      intros [x [y [X [Y E]]]]. mlia.
    + replace (d ⊕ i) with ((d ⊕ k) ⊕ (i - k))
        by (rewrite N.add_mod_idemp_l by discriminate; f_equal; lia).
      rewrite <- (byte_of_load (setmem 64 LittleE 8 M a v) (d ⊕ k) (i - k)) by lia.
      rewrite <- A, getmem_mod_l, getmem_setmem by discriminate.
      rewrite N.mod_small by (rewrite V; apply getmem_bound).
      rewrite V, byte_of_load by lia.
      rewrite <- getmem_mod_l. f_equal. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia.
  - intros b B. rewrite getmem_noverlap. apply F. lia.
    intros [x [y [X [Y E]]]]. apply B. mlia.
Qed.

(* a saved-register slot is read back through the frame (the copied area is
   outside the stack) *)
Lemma cpk_slot:
  forall m mb M d s n k rsp F j, cpk m mb M d s k -> k <= n -> ~ overlap 64 d n (rsp ⊖ F) F ->
  8 <= j <= F -> F < 2^63 -> M Ⓠ[rsp ⊖ j] = mb Ⓠ[rsp ⊖ j].
Proof.
  intros m mb M d s n k rsp F j [_ Fr] KN NOV J FB. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply Fr. intro H. apply NOV.
  exists (msub 64 a d), (F - j + msub 64 a (rsp ⊖ j)). split. lia. split. lia. mlia.
Qed.

(* ---- the first occurrence of a byte value ---- *)

Definition cabsent (m s c k:N) := forall i, i < k -> m Ⓑ[s ⊕ i] <> c.

Lemma cabsent_succ: forall m s c k, cabsent m s c k -> m Ⓑ[s ⊕ k] <> c -> cabsent m s c (k + 1).
Proof.
  intros m s c k CA B i I. destruct (N.lt_ge_cases i k). apply CA. assumption.
  replace i with k by lia. exact B.
Qed.

(* musl's memccpy word test: HASZERO(w ^ (c * ONES)) = 0 means none of the
   eight bytes is c *)
Lemma cabsent_add8:
  forall m s c k, c < 256 -> cabsent m s c k ->
  N.lnot (m Ⓠ[s + k] .^ c * 0x0101010101010101) 64
    .& (m Ⓠ[s + k] .^ c * 0x0101010101010101 ⊖ 0x0101010101010101) .& 0x8080808080808080 = 0 ->
  cabsent m s c (k + 8).
Proof.
  intros m s c k C CA H i I. destruct (N.lt_ge_cases i k) as [IK|IK]. apply CA, IK.
  assert (W: m Ⓠ[s + k] < 2^64) by apply getmem_bound.
  assert (X: m Ⓠ[s + k] .^ c * 0x0101010101010101 < 2^64).
  { assert (B: c * 0x0101010101010101 < 2^64) by lia.
    pose proof (lxor_bound 64 _ _ W B). lia. }
  pose proof (haszero_bytes_msub _ X H (i - k) ltac:(lia)) as B.
  rewrite byte_of_lxor, byte_of_bcast in B by (assumption || lia).
  apply lxor_neq0 in B. rewrite byte_of_load in B by lia.
  rewrite <- getmem_mod_l in B. rewrite N.add_mod_idemp_l in B by discriminate.
  replace (s + k + (i - k)) with (s + i) in B by lia. exact B.
Qed.

(* x & ~7 *)
Lemma land_align8: forall x, x < 2^64 -> x .& 18446744073709551608 = x - x mod 8.
Proof.
  intros x X.
  change 18446744073709551608 with (N.lxor (N.ones 64) 7).
  apply N.bits_inj. intro i. rewrite N.land_spec, N.lxor_spec.
  destruct (N.lt_ge_cases i 3) as [I|I].
  - rewrite N.ones_spec_low by lia.
    replace (N.testbit 7 i) with true by (destruct i as [|p]; [reflexivity|]; destruct p; try reflexivity; lia).
    rewrite <- (N.mul_comm 8), <- (N.shiftl_mul_pow2 (x / 8) 3) at 1.
    (* hmm, placeholder *)
Admitted.

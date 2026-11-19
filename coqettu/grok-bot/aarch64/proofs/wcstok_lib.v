(* wcstok: frame reads, memory agreement below the frames, and pre/post
   conversions between the caller's memory and the callees' memories.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokFrame GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs.
Import ARM8Notations.
Open Scope N.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Definition agreeD (m1 m2: memory) (B: N) := ∀ a, a + 4 <= B -> m1 Ⓓ[a] = m2 Ⓓ[a].

Lemma agreeD_sym: ∀ m1 m2 B, agreeD m1 m2 B -> agreeD m2 m1 B.
Proof. intros m1 m2 B H a A. symmetry. apply H, A. Qed.

(* every memory wcstok's code sees agrees with the caller's below sp - 96 *)
Lemma wt_agree: ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p W, 96 <= sp -> sp < 2^64 ->
  (W = wt_M1 sp mem raddr x19 x20 x21 x22 x29 \/ W = wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p \/
   wt_W2 sp mem raddr x19 x20 x21 x22 x29 s0 sep p W) ->
  agreeD W mem (sp - 96).
Proof.
  intros until W. intros SP0 SP1 WW a A.
  destruct WW as [->|[->|[->| ->]]];
  unfold wt_W1, wt_M1, wt_frame, wcsspn_proof.sspn_frame, wcscspn_proof.cspn_frame; memsimp; reflexivity.
Qed.

Lemma wt_M1_q: ∀ sp mem raddr x19 x20 x21 x22 x29 a, 96 <= sp -> sp < 2^64 -> a + 8 <= sp - 48 ->
  wt_M1 sp mem raddr x19 x20 x21 x22 x29 Ⓠ[a] = mem Ⓠ[a].
Proof. intros. unfold wt_M1, wt_frame. memsimp. reflexivity. Qed.

Definition wt_frd (W: memory) (sp raddr x19 x20 x21 x22 x29: N) :=
  W Ⓠ[sp - 48] = x29 /\ W Ⓠ[8 + (sp - 48)] = raddr /\ W Ⓠ[16 + (sp - 48)] = x19 /\
  W Ⓠ[24 + (sp - 48)] = x20 /\ W Ⓠ[32 + (sp - 48)] = x21 /\ W Ⓠ[40 + (sp - 48)] = x22.

Lemma wt_rd: ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p W, 96 <= sp -> sp < 2^64 ->
  raddr < 2^64 -> x19 < 2^64 -> x20 < 2^64 -> x21 < 2^64 -> x22 < 2^64 -> x29 < 2^64 ->
  (W = wt_M1 sp mem raddr x19 x20 x21 x22 x29 \/ W = wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p \/
   wt_W2 sp mem raddr x19 x20 x21 x22 x29 s0 sep p W) ->
  wt_frd W sp raddr x19 x20 x21 x22 x29.
Proof.
  intros until W. intros SP0 SP1 B30 B19 B20 B21 B22 B29 WW. unfold wt_frd.
  replace (8 + (sp - 48)) with (sp - 40) by lia. replace (16 + (sp - 48)) with (sp - 32) by lia.
  replace (24 + (sp - 48)) with (sp - 24) by lia. replace (32 + (sp - 48)) with (sp - 16) by lia.
  replace (40 + (sp - 48)) with (sp - 8) by lia.
  destruct WW as [->|[->|[->| ->]]];
  unfold wt_W1, wt_M1, wt_frame, wcsspn_proof.sspn_frame, wcscspn_proof.cspn_frame;
  repeat split; memsimp; apply N.mod_small; assumption.
Qed.

Lemma wt_frd_st: ∀ W sp raddr x19 x20 x21 x22 x29 a v, wt_frd W sp raddr x19 x20 x21 x22 x29 ->
  96 <= sp -> sp < 2^64 -> a + 8 <= sp - 48 -> wt_frd (W [Ⓠ a := v]) sp raddr x19 x20 x21 x22 x29.
Proof. unfold wt_frd. intros. repeat split; memsimp; tauto. Qed.

Lemma wt_frd_stD: ∀ W sp raddr x19 x20 x21 x22 x29 a v, wt_frd W sp raddr x19 x20 x21 x22 x29 ->
  96 <= sp -> sp < 2^64 -> a + 4 <= sp - 48 -> wt_frd (W [Ⓓ a := v]) sp raddr x19 x20 x21 x22 x29.
Proof. unfold wt_frd. intros. repeat split; memsimp; tauto. Qed.

(* string facts move between memories that agree below B *)
Lemma winset_agree: ∀ m1 m2 B c Lc w, agreeD m1 m2 B -> c + 4*Lc + 4 <= B ->
  wcsspn_proof.winset m1 c Lc w -> wcsspn_proof.winset m2 c Lc w.
Proof. intros m1 m2 B c Lc w AG CB (j & J & E). exists j. split; [exact J|]. rewrite <- AG by lia. exact E. Qed.

Lemma cwinset_agree: ∀ m1 m2 B c Lc w, agreeD m1 m2 B -> c + 4*Lc + 4 <= B ->
  wcscspn_proof.winset m1 c Lc w -> wcsspn_proof.winset m2 c Lc w.
Proof. intros m1 m2 B c Lc w AG CB (j & J & E). exists j. split; [exact J|]. rewrite <- AG by lia. exact E. Qed.

Lemma spn_agree: ∀ m1 m2 B s c Lc k, agreeD m1 m2 B -> c + 4*Lc + 4 <= B -> s + 4*k <= B ->
  wcsspn_proof.spn m1 s c Lc k -> wcsspn_proof.spn m2 s c Lc k.
Proof.
  intros m1 m2 B s c Lc k AG CB SB S i I. destruct (S i I) as [N0 W].
  rewrite <- AG by lia. split; [exact N0|]. eapply winset_agree; eassumption.
Qed.

Lemma cspn_agree: ∀ m1 m2 B s c Lc k, agreeD m1 m2 B -> c + 4*Lc + 4 <= B -> s + 4*k <= B ->
  wcscspn_proof.cspn m1 s c Lc k -> wcscspn_proof.cspn m2 s c Lc k.
Proof.
  intros m1 m2 B s c Lc k AG CB SB S i I. destruct (S i I) as [N0 W].
  rewrite <- AG by lia. split; [exact N0|]. intros (j & J & E). apply W. exists j. split; [exact J|].
  rewrite AG by lia. exact E.
Qed.

Lemma nilfree_agree: ∀ m1 m2 B s L, agreeD m1 m2 B -> s + 4*L <= B ->
  wcslen_proof.wcs_nilfree m1 s L -> wcslen_proof.wcs_nilfree m2 s L.
Proof. intros m1 m2 B s L AG SB N0 i I. rewrite <- AG by lia. apply N0, I. Qed.

Lemma wt_sf: ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k ph k' ph',
  same_invset_family (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k ph)
                     (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k' ph').
Proof. intros. reflexivity. Qed.

(* the callees' preconditions *)
Lemma wt_spn_pre: ∀ sp mem raddr x19 x20 x21 x22 x29 s sep Ls Lc,
  96 <= sp -> sp < 2^64 ->
  wcslen_proof.wcs_nilfree mem s Ls -> mem Ⓓ[s + 4*Ls] = 0 -> Ls < 2^61 ->
  wcslen_proof.wcs_nilfree mem sep Lc -> mem Ⓓ[sep + 4*Lc] = 0 -> 0 < sep ->
  s + 4*Ls + 4 <= sp - 96 -> sep + 4*Lc + 4 <= sp - 96 ->
  wcsspn_proof.wcsspn_pre (sp - 48) (wt_M1 sp mem raddr x19 x20 x21 x22 x29) s sep Ls Lc.
Proof.
  intros. assert (AG := wt_agree sp mem raddr x19 x20 x21 x22 x29 0 0 0 _ ltac:(lia) ltac:(assumption) (or_introl eq_refl)).
  apply agreeD_sym in AG.
  unfold wcsspn_proof.wcsspn_pre. splits; try lia.
  eapply nilfree_agree; [exact AG | lia | assumption].
  rewrite <- AG by lia. assumption.
  eapply nilfree_agree; [exact AG | lia | assumption].
  rewrite <- AG by lia. assumption.
Qed.

Lemma wt_cspn_pre: ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k,
  96 <= sp -> sp < 2^64 -> k <= Ls -> 0 < wt_s mem s0 p ->
  wcslen_proof.wcs_nilfree mem (wt_s mem s0 p) Ls -> mem Ⓓ[wt_s mem s0 p + 4*Ls] = 0 -> Ls < 2^61 ->
  wcslen_proof.wcs_nilfree mem sep Lc -> mem Ⓓ[sep + 4*Lc] = 0 -> 0 < sep ->
  wt_s mem s0 p + 4*Ls + 4 <= sp - 96 -> sep + 4*Lc + 4 <= sp - 96 ->
  wcscspn_proof.wcscspn_pre (sp - 48) (wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p)
    (wt_s mem s0 p + 4*k) sep (Ls - k) Lc.
Proof.
  intros until k. set (s := wt_s mem s0 p). intros.
  assert (AG := wt_agree sp mem raddr x19 x20 x21 x22 x29 s0 sep p _ ltac:(lia) ltac:(assumption) (or_intror (or_introl eq_refl))).
  apply agreeD_sym in AG.
  unfold wcscspn_proof.wcscspn_pre. splits; try lia.
  intros i I. rewrite <- AG by lia. replace (s + 4*k + 4*i) with (s + 4*(k+i)) by lia.
    match goal with H: wcslen_proof.wcs_nilfree mem s Ls |- _ => apply H; lia end.
  rewrite <- AG by lia. replace (s + 4*k + 4*(Ls-k)) with (s + 4*Ls) by lia. assumption.
  eapply nilfree_agree; [exact AG | lia | assumption].
  rewrite <- AG by lia. assumption.
Qed.

Lemma shl2: ∀ x, x << 2 = 4 * x.
Proof. intros. rewrite N.shiftl_mul_pow2. lia. Qed.

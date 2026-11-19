(* strlcpy verification-condition lemmas for invariant points 0x15eec4, 0x15eef0, 0x15ef88, 0x15ef90 -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Part of the strlcpy proof (0x15eec4 in Ghidra, 0x5eec4 ELF vaddr), which is
   split over several files so that no single coqc run exceeds the 8 GB cap
   (see ../../VCEffectsOnMemOverhead.md).  Full header (SEMANTICS, manual
   SPECIFICATION, PROVENANCE, I/O specification) is in strlcpy_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strlcpy_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame.
From Grok.proofs Require Import strlcpy_callees.
Import ARM8Notations.
Open Scope N.

Lemma slc_case_15eec4: ∀ sp mem raddr d q n x19 x29 L K (s1:store) (t:list (exit*store)),
  slc_pre sp mem d q n L K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 L K Prop (fun _ P => P) (fun _ P => P) True s1 0x15eec4 ->
  nextinv strlcpy_prog (invs1 sp mem raddr d q n x19 x29 L K) (exits1 sp mem raddr d q n x19 x29 L K) false ((Addr 0x15eec4, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 L K s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  (* entry *)
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X29).
  repeat arm8_step.
  all: destruct PRE0 as (NFq & ZL & NK & SP32 & SPlt & BD & BQ & QN & DISJ); change (2^64) with 18446744073709551616 in *.
  + apply N.eqb_eq in BC. exists 0. splits; try first [left; split; [exact BC|reflexivity] | reflexivity | lia].
    all: try (unfold slc_mem; replace (n =? 0) with true by (symmetry; apply N.eqb_eq; exact BC); reflexivity).
    all: try (rewrite X1; symmetry; apply N.add_0_r).
  + apply N.eqb_neq in BC. apply N.eqb_eq in BC0. apply xor_mod8 in BC0.
    exists 0. splits; try first [reflexivity | lia | al3 | (rewrite N.add_0_r; reflexivity)].
    all: try (rewrite msub_small by L64; lia).
  + apply N.eqb_neq in BC.
    exists 0, 0. splits; try first [left; reflexivity | reflexivity | lia | (rewrite N.add_0_r; reflexivity)].
    all: try (rewrite msub_small by L64; lia).
Qed.

Optimize Heap.

Lemma slc_case_15eef0: ∀ sp mem raddr d q n x19 x29 L K (s1:store) (t:list (exit*store)),
  slc_pre sp mem d q n L K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 L K Prop (fun _ P => P) (fun _ P => P) True s1 0x15eef0 ->
  nextinv strlcpy_prog (invs1 sp mem raddr d q n x19 x29 L K) (exits1 sp mem raddr d q n x19 x29 L K) false ((Addr 0x15eef0, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 L K s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  (* 0x15eef0 bounded byte loop *)
  destruct PRE as (k & j & NP & KK & JJ & X0 & X1 & X3 & X2 & X19 & MEM & SP & X29).
  facts raddr x19 x29.
  destruct NK as [N0|(KN & KL & KC)]; [lia|].
  assert (JK: j = k \/ (j = k + 1 /\ k = L)) by exact JJ.
  assert (BK: bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat j) = setmem 64 LittleE 1 (bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat k)) (d + k) 0 \/ j = k).
  { destruct JJ as [->|[-> ->]]. right; reflexivity. left. rewrite bcp_succ, RD, ZL by lia. reflexivity. }
  repeat arm8_step.
  + rewrite N.mod_small in BC by lia. apply N.eqb_eq in BC. assert (EK: k = K) by lia. rewrite EK in *.
    splits; try first [reflexivity | lia | assumption].
    unfold slc_fin. rewrite MEM. destruct BK as [-> | ->]. apply sm0_idem. reflexivity.
  + rewrite N.mod_small in BC by lia. apply N.eqb_neq in BC. apply N.eqb_eq in BC0.
    rewrite BC0. rewrite RD in BC0 by lia.
    assert (k = L) by (destruct (N.lt_ge_cases k L) as [H9|H9]; [destruct (NFq k H9 BC0) | lia]).
    assert (EK: k = K) by lia. rewrite EK in *.
    splits; try first [reflexivity | lia | assumption].
    unfold slc_fin. rewrite sm0_idem. destruct BK as [-> | ->]. apply sm0_idem. reflexivity.
  + rewrite N.mod_small in BC by lia. apply N.eqb_neq in BC. apply N.eqb_neq in BC0.
    rewrite RD in BC0 by lia.
    assert (k < L) by (destruct (N.lt_ge_cases k L) as [H9|H9]; [exact H9 | exfalso; apply BC0; replace k with L by lia; exact ZL]).
    assert (j = k) by (destruct JJ as [H9|[_ H9]]; [exact H9 | lia]). subst j.
    exists (k+1), (k+1). splits; try first [left; reflexivity | reflexivity | lia | assumption].
    all: try (rewrite bcp_succ; reflexivity).
    all: try (rewrite N.mod_small by L64; lia).
Qed.

Optimize Heap.

Lemma slc_case_15ef88: ∀ sp mem raddr d q n x19 x29 L K (s1:store) (t:list (exit*store)),
  slc_pre sp mem d q n L K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 L K Prop (fun _ P => P) (fun _ P => P) True s1 0x15ef88 ->
  nextinv strlcpy_prog (invs1 sp mem raddr d q n x19 x29 L K) (exits1 sp mem raddr d q n x19 x29 L K) false ((Addr 0x15ef88, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 L K s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  (* 0x15ef88 *)
  destruct PRE as (NP & X0 & X1 & X3 & FM & SP & X29).
  facts raddr x19 x29.
  destruct NK as [N0|(KN & KL & KC)]; [lia|].
  repeat arm8_step.
  exists K. splits; clo.
  all: try (right; split; [lia|reflexivity]).
  all: try (unfold slc_mem; replace (n =? 0) with false by (symmetry; apply N.eqb_neq; lia); exact FM).
Qed.

Optimize Heap.

Lemma slc_case_15ef90: ∀ sp mem raddr d q n x19 x29 L K (s1:store) (t:list (exit*store)),
  slc_pre sp mem d q n L K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 L K Prop (fun _ P => P) (fun _ P => P) True s1 0x15ef90 ->
  nextinv strlcpy_prog (invs1 sp mem raddr d q n x19 x29 L K) (exits1 sp mem raddr d q n x19 x29 L K) false ((Addr 0x15ef90, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 L K s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  (* 0x15ef90: call strlen(q + k), then return *)
  destruct PRE as (k & KC & X1 & X19 & MEM & SP & X29).
  facts raddr x19 x29.
  assert (KLe: k <= L /\ k <= n /\ (0 < n -> k < n)) by (destruct KC as [[-> ->]|[NP ->]]; destruct NK as [N0|(KN & KL & KC')]; lia).
  assert (SM: ∀ i, i <= L -> slc_mem sp mem raddr x19 x29 d q n K Ⓑ[q + i] = mem Ⓑ[q + i]).
  { intros i I. unfold slc_mem. destruct (n =? 0) eqn:N0.
    - apply CB. lia.
    - apply N.eqb_neq in N0. destruct NK as [N1|(KN & KL & KC')]; [lia|]. unfold slc_fin.
      destruct DISJ as [DJ|DJ].
      + rewrite getmem_setmem_above by L64. apply RD; lia.
      + rewrite getmem_setmem_below by L64. apply RD; lia. }
  assert (FQ: ∀ a, sp - 32 <= a -> a + 8 <= sp -> slc_mem sp mem raddr x19 x29 d q n K Ⓠ[a] = slc_frame sp mem raddr x19 x29 Ⓠ[a]).
  { intros a A1 A2. unfold slc_mem. destruct (n =? 0) eqn:N0. reflexivity.
    apply N.eqb_neq in N0. destruct NK as [N1|(KN & KL & KC')]; [lia|]. unfold slc_fin.
    rewrite getmem_setmem_below by L64. apply bcp_read_above; rewrite ?N2Nat.id; L64. }
  assert (Q32: slc_frame sp mem raddr x19 x29 Ⓠ[sp - 32] = x29) by (unfold slc_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  assert (Q24: slc_frame sp mem raddr x19 x29 Ⓠ[sp - 24] = raddr) by (unfold slc_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  assert (Q16: slc_frame sp mem raddr x19 x29 Ⓠ[sp - 16] = x19) by (unfold slc_frame; rewrite !(msub_small 64 sp) by L64; memsimp; apply N.mod_small; L64).
  do 2 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply strlcpy_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply strlen_correct_in_strlcpy with (d:=d) (n:=n) (L:=L) (K:=K); first [ exact (fun _ _ _ H => H) | eassumption ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strlcpy_prog_welltyped.
  clearbody s2.
  rename MDL' into MDL3. rename s' into s3.
  destruct_inv 64 PRE.
  destruct PRE as (L' & LLT & R0 & NF' & ZL' & MEM' & SP' & X30' & X29' & X19').
  rewrite MEM in NF', ZL', MEM'. rewrite SP in SP'. rewrite X29 in X29'. rewrite X19 in X19'.
  assert (LL: L' = L - k).
  { symmetry. apply (first_zero_unique (fun i => mem Ⓑ[q + k + i]) (fun i => slc_mem sp mem raddr x19 x29 d q n K Ⓑ[q + k + i])); cbv beta.
    - intros i I. replace (q + k + i) with (q + (k + i)) by lia. apply NFq. lia.
    - replace (q + k + (L - k)) with (q + L) by lia. exact ZL.
    - exact NF'.
    - exact ZL'.
    - intros i I. replace (q + k + i) with (q + (k + i)) by lia. apply SM. lia. }
  rewrite LL in R0.
  repeat arm8_step.
  all: rewrite ?(msub_small 64 sp) by L64.
  splits; try reflexivity.
  + rewrite N.sub_add by lia. apply N.mod_small. L64.
  + rewrite FQ by L64. exact Q16.
  + rewrite FQ by L64. exact Q32.
  + rewrite FQ by L64. exact Q24.
Qed.

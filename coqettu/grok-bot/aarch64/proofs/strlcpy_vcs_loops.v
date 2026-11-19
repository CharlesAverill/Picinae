(* strlcpy verification-condition lemmas for invariant points 0x15ef1c, 0x15ef34 -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
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

Lemma slc_case_15ef1c: ∀ sp mem raddr d q n x19 x29 L K (s1:store) (t:list (exit*store)),
  slc_pre sp mem d q n L K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 L K Prop (fun _ P => P) (fun _ P => P) True s1 0x15ef1c ->
  nextinv strlcpy_prog (invs1 sp mem raddr d q n x19 x29 L K) (exits1 sp mem raddr d q n x19 x29 L K) false ((Addr 0x15ef1c, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 L K s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  (* 0x15ef1c alignment byte loop *)
  destruct PRE as (k & NP & KK & AL & X0 & X1 & X3 & X2 & X19 & MEM & SP & X29).
  facts raddr x19 x29.
  destruct NK as [N0|(KN & KL & KC)]; [lia|].
  repeat arm8_step.
  all: nrm.
  + exists k, k. splits; clo.
  + exists k, k. splits; clo.
  + exists k, k. splits; clo.
  + match goal with H: _ Ⓑ[q + k] ≠ 0 |- _ => rewrite RD in H by lia end.
    assert (k < L) by (destruct (N.lt_ge_cases k L) as [H9|H9]; [exact H9 | exfalso; replace k with L in * by lia; contradiction]).
    exists (k+1). splits; clo.
    rewrite bcp_succ. reflexivity.
  + match goal with H: _ Ⓑ[q + k] = 0 |- _ => rewrite RD in H by lia end.
    assert (k = L) by (destruct (N.lt_ge_cases k L) as [H9|H9]; [destruct (NFq k H9 ltac:(assumption)) | lia]).
    exists k, (k+1). splits; clo.
    right; split; [reflexivity | assumption].
    rewrite bcp_succ. reflexivity.
Qed.

Optimize Heap.

Lemma slc_case_15ef34: ∀ sp mem raddr d q n x19 x29 L K (s1:store) (t:list (exit*store)),
  slc_pre sp mem d q n L K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 L K Prop (fun _ P => P) (fun _ P => P) True s1 0x15ef34 ->
  nextinv strlcpy_prog (invs1 sp mem raddr d q n x19 x29 L K) (exits1 sp mem raddr d q n x19 x29 L K) false ((Addr 0x15ef34, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 L K s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  (* 0x15ef34 *)
  destruct PRE as (k & j & NP & KN & KK & JJ & AL & X0 & X1 & X3 & X2 & X19 & MEM & SP & X29).
  facts raddr x19 x29.
  destruct NK as [N0|(KN' & KL & KC)]; [lia|].
  repeat arm8_step.
  all: nrm.
  + exists k, j. splits; clo.
  + match goal with H: _ Ⓑ[q + k] ≠ 0 |- _ => rewrite RD in H by (destruct JJ as [->|[-> _]]; lia) end.
    assert (k < L) by (destruct (N.lt_ge_cases k L) as [H9|H9]; [exact H9 | exfalso; replace k with L in * by lia; contradiction]).
    assert (j = k) by (destruct JJ as [H9|[_ H9]]; [exact H9 | lia]). subst j.
    exists k, (k + N.land (n - 1 - k) 0xfffffffffffffff8).
    pose proof (f8_le (n - 1 - k)). pose proof (f8_mod (n - 1 - k)).
    splits; clo.
Qed.

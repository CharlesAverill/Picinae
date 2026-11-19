(* strlcpy verification-condition lemmas for invariant points 0x15ef64 -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
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

Lemma slc_case_15ef64: ∀ sp mem raddr d q n x19 x29 L K (s1:store) (t:list (exit*store)),
  slc_pre sp mem d q n L K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 L K Prop (fun _ P => P) (fun _ P => P) True s1 0x15ef64 ->
  nextinv strlcpy_prog (invs1 sp mem raddr d q n x19 x29 L K) (exits1 sp mem raddr d q n x19 x29 L K) false ((Addr 0x15ef64, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 L K s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  (* 0x15ef64 word loop *)
  destruct PRE as (k & m & NP & KK & KM & MN & M8 & AL & X0 & X1 & X3 & X6 & X7 & X8 & X19 & MEM & SP & X29).
  facts raddr x19 x29.
  destruct NK as [N0|(KN & KL & KC)]; [lia|].
  repeat arm8_step.
  all: nrm.
  + exists k, k. splits; clo2.
  + assert (KM8: k + 8 <= m) by (assert (k <> m) by (intro; subst; contradiction); lia).
    set (W := bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat k) Ⓠ[q + k]) in *.
    assert (NZB: ∀ i, i < 8 -> byte_of W i ≠ 0).
    { apply haszero_test_zero. apply qword_lt64. apply N.eqb_eq. exact BC0. }
    assert (KL8: k + 8 <= L).
    { destruct (N.le_gt_cases (k + 8) L) as [H9|H9]; [exact H9|exfalso].
      apply (NZB (L - k)). clear - H9; lia. unfold W. rewrite byte_of_qword by lia.
      replace (q + k + (L - k)) with (q + L) by lia. rewrite RD by lia. exact ZL. }
    exists (k+8), m. splits; clo2.
    all: try (rewrite bcp_word8 by exact AL; reflexivity).
  + exists k, k. splits; clo2.
Qed.

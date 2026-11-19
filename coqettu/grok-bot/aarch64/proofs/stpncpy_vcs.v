(* stpncpy verification-condition lemmas (one per invariant point) and the memory lemma stp_mem_ok -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Part of the stpncpy proof (0x15e9c0 in Ghidra, 0x5e9c0 ELF vaddr), split
   into a definitions/callee file, a VC file and a main file (see
   ../../VCEffectsOnMemOverhead.md).  Full header (SEMANTICS, manual
   SPECIFICATION, PROVENANCE, I/O specification) is in stpncpy_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require stpncpy_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require Import memset_proof stpncpy_callees.
Import ARM8Notations.
Open Scope N.

(* tactics shared by the VC lemmas *)
Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Lemma f8_mod: ∀ x, N.land x 0xfffffffffffffff8 mod 8 = 0.
Proof.
  intro x. change 8 with (2^3). rewrite <- N.land_ones, <- N.land_assoc.
  change (N.land 0xfffffffffffffff8 (N.ones 3)) with 0. apply N.land_0_r.
Qed.

Lemma f8_le: ∀ x, N.land x 0xfffffffffffffff8 <= x.
Proof. intro x. apply N.land_le_l. Qed.

Ltac al3 := match goal with AL: msub 64 ?q ?d mod 8 = 0 |- msub 3 ?q ?d = 0 =>
  transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL] end.

Ltac facts raddr x19 x29 :=
  match goal with PRE0: stp_pre ?sp ?mem ?d ?q ?n ?K |- _ =>
    try change (mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19]) with (stp_frame sp mem raddr x19 x29) in *;
    let F := fresh in pose proof PRE0 as F;
    destruct F as (NFq & KN & KZ & SM96 & LOW & SP32 & SPlt & BD & BQ & DISJ);
    assert (CB: ∀ a, a + 1 <= sp - 32 -> stp_frame sp mem raddr x19 x29 Ⓑ[a] = mem Ⓑ[a])
      by (let a := fresh "a" in let A := fresh "A" in intros a A; unfold stp_frame; rewrite !(msub_small 64 sp) by L64; memsimp; reflexivity);
    assert (RD: ∀ i j, i < n -> j <= n -> bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat j) Ⓑ[q+i] = mem Ⓑ[q+i])
      by (let ii := fresh "ii" in let jj := fresh "jj" in let I := fresh "I" in let J := fresh "J" in intros ii jj I J; rewrite <- CB by L64; destruct DISJ as [DJ|DJ];
          [apply bcp_read_below | apply bcp_read_above]; rewrite ?N2Nat.id; L64);
    change (2^64) with 18446744073709551616 in *
  end.

Ltac nrm := repeat match goal with
  | H: negb ((?b >> 0) mod 2^32 =? 0) = true |- _ => apply cbnz32_true in H; [|apply byte_lt32]
  | H: negb ((?b >> 0) mod 2^32 =? 0) = false |- _ => apply cbnz32_false in H; [|apply byte_lt32]
  | H: negb (_ =? _) = true |- _ => apply Bool.negb_true_iff, N.eqb_neq in H
  | H: negb (_ =? _) = false |- _ => apply Bool.negb_false_iff, N.eqb_eq in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end.

Ltac clean := repeat match goal with
  | H: context [getmem _ _ _ _ _] |- _ => clear H
  | H: context [bcp _ _ _ _] |- _ => clear H
  | H: context [setmem _ _ _ _ _ _] |- _ => clear H
  | H: ∀ _, _ |- _ => clear H
  | H: nilfree _ _ _ |- _ => clear H
  | H: models _ _ |- _ => clear H
  | H: exec_prog _ _ |- _ => clear H
  | H: stp_pre _ _ _ _ _ _ |- _ => clear H
  | H: ?f ?v = _ |- _ => match type of f with store => clear H | var -> N => clear H end
  end.
Ltac llia := clean; lia.
Ltac mods := change (2^64) with 18446744073709551616; repeat match goal with |- context [(?x) mod 18446744073709551616] => rewrite (N.mod_small x) by llia end.
Ltac clo := try first [ sassumption | sreflexivity | (left; reflexivity) | al3 |
  (rewrite ?N.add_0_r, ?N.sub_0_r; first [sassumption | sreflexivity]) |
  match goal with |- _ = bcp _ _ _ (N.to_nat 0) => reflexivity end |
  match goal with
  | |- bcp _ _ _ _ = _ => fail 1 | |- setmem _ _ _ _ _ _ = _ => fail 1 | |- _ [Ⓠ _ := _] = _ => fail 1
  | |- _ => first [ llia | (mods; llia) | (rewrite msub_small by L64; llia) | (rewrite msub_small by L64; mods; llia) ] end ].

Lemma stp_mem_ok: ∀ sp mem raddr d q n x19 x29 K j M,
  stp_pre sp mem d q n K ->
  x19 < 2^64 -> x29 < 2^64 -> raddr < 2^64 ->
  (j = K \/ (j = K + 1 /\ K < n)) ->
  (∀ i, i < n - K -> M Ⓑ[d + K + i] = 0) ->
  (∀ a, a < 2^64 -> (a < d + K \/ d + K + (n - K) <= a) -> M Ⓑ[a] = bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat j) Ⓑ[a]) ->
  (∀ i, i < K -> M Ⓑ[d + i] = mem Ⓑ[q + i]) /\
  (∀ i, K <= i -> i < n -> M Ⓑ[d + i] = 0) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> M Ⓑ[a] = stp_frame sp mem raddr x19 x29 Ⓑ[a]) /\
  M Ⓠ[sp - 16] = x19 /\ M Ⓠ[sp - 32] = x29 /\ M Ⓠ[sp - 24] = raddr.
Proof.
  intros sp mem raddr d q n x19 x29 K j M PRE0 W19 W29 W30 JJ BY OT.
  facts raddr x19 x29.
  assert (JN: j <= n) by (destruct JJ as [->|[-> ?]]; lia).
  assert (OUT: ∀ a, a < 18446744073709551616 -> (a < d \/ d + n <= a) -> M Ⓑ[a] = stp_frame sp mem raddr x19 x29 Ⓑ[a]).
  { intros a A O. rewrite OT by (change (2^64) with 18446744073709551616; lia).
    destruct O as [O|O]; [apply bcp_read_below | apply bcp_read_above]; rewrite ?N2Nat.id; L64. }
  assert (FQ: ∀ a v, sp - 32 <= a -> a + 8 <= sp -> stp_frame sp mem raddr x19 x29 Ⓠ[a] = v -> M Ⓠ[a] = v).
  { intros a v A1 A2 E. rewrite <- E. apply getmem_ext. intros i I. apply OUT; lia. }
  splits.
  - intros i I. rewrite OT by (change (2^64) with 18446744073709551616; lia).
    rewrite bcp_read_in by (rewrite ?N2Nat.id; change (2^64) with 18446744073709551616; lia).
    apply RD; lia.
  - intros i I1 I2. replace (d + i) with (d + K + (i - K)) by lia. apply BY. lia.
  - exact OUT.
  - apply FQ; try lia. unfold stp_frame. rewrite !(msub_small 64 sp) by L64. memsimp. apply N.mod_small. exact W19.
  - apply FQ; try lia. unfold stp_frame. rewrite !(msub_small 64 sp) by L64. memsimp. apply N.mod_small. exact W29.
  - apply FQ; try lia. unfold stp_frame. rewrite !(msub_small 64 sp) by L64. memsimp. apply N.mod_small. exact W30.
Qed.

Optimize Heap.

Lemma stp_case_15e9c0: ∀ sp mem raddr d q n x19 x29 K mm md cc mn (s1:store) (t:list (exit*store)),
  stp_pre sp mem d q n K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 K mm md cc mn Prop (fun _ P => P) (fun _ P => P) True s1 0x15e9c0 ->
  nextinv stp_prog (invs1 sp mem raddr d q n x19 x29 K mm md cc mn) (exits1 sp mem raddr d q n x19 x29 K mm md cc mn) false ((Addr 0x15e9c0, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 K mm md cc mn s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X29).
  repeat arm8_step.
  all: nrm.
  all: facts raddr x19 x29.
  1: (pose proof (xor_mod8 q d BC) as AL; exists 0; splits; clo).
  1: (exists 0; splits; clo).
Qed.

Optimize Heap.

Lemma stp_case_15e9ec: ∀ sp mem raddr d q n x19 x29 K mm md cc mn (s1:store) (t:list (exit*store)),
  stp_pre sp mem d q n K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 K mm md cc mn Prop (fun _ P => P) (fun _ P => P) True s1 0x15e9ec ->
  nextinv stp_prog (invs1 sp mem raddr d q n x19 x29 K mm md cc mn) (exits1 sp mem raddr d q n x19 x29 K mm md cc mn) false ((Addr 0x15e9ec, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 K mm md cc mn s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  destruct PRE as (k & KK & AL & X0 & X1 & X2 & MEM & SP & X29).
  facts raddr x19 x29.
  repeat arm8_step.
  all: nrm.
  1: (assert (EK: k = K) by llia; subst k; exists K; splits; clo).
  1: (exists k, k; splits; clo).
  1: (assert (EK: k = K) by llia; subst k; exists K; splits; clo).
  1: (match goal with H: _ Ⓑ[q + k] ≠ 0 |- _ => rewrite RD in H by llia; rename H into BZ end;
      assert (KK': k < K) by (destruct (N.lt_ge_cases k K) as [H9|H9]; [exact H9|exfalso; apply BZ; replace k with K by llia; apply KZ; llia]);
      exists (k+1); splits; clo; try (rewrite bcp_succ; reflexivity)).
  1: (match goal with H: _ Ⓑ[q + k] = 0 |- _ => rewrite RD in H by llia; rename H into BZ end;
      assert (EK: k = K) by (destruct (N.lt_ge_cases k K) as [H9|H9]; [destruct (NFq k H9 BZ) | llia]);
      subst k; exists K, (K+1); splits; clo; try (right; split; llia); try (rewrite bcp_succ; reflexivity)).
Qed.

Optimize Heap.

Lemma stp_case_15ea0c: ∀ sp mem raddr d q n x19 x29 K mm md cc mn (s1:store) (t:list (exit*store)),
  stp_pre sp mem d q n K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 K mm md cc mn Prop (fun _ P => P) (fun _ P => P) True s1 0x15ea0c ->
  nextinv stp_prog (invs1 sp mem raddr d q n x19 x29 K mm md cc mn) (exits1 sp mem raddr d q n x19 x29 K mm md cc mn) false ((Addr 0x15ea0c, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 K mm md cc mn s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  destruct PRE as (k & j & KK & KLN & JJ & AL & X0 & X1 & X2 & MEM & SP & X29).
  facts raddr x19 x29.
  repeat arm8_step.
  all: nrm.
  1: (rewrite RD in BC by (destruct JJ as [->|[-> _]]; llia);
      assert (EK: k = K) by (destruct (N.lt_ge_cases k K) as [H9|H9]; [destruct (NFq k H9 BC) | llia]);
      subst k; exists j; splits; clo; try (destruct JJ as [->|[-> _]]; [left; reflexivity | right; split; llia])).
  1: (rewrite RD in BC by (destruct JJ as [->|[-> _]]; llia);
      assert (KK': k < K) by (destruct (N.lt_ge_cases k K) as [H9|H9]; [exact H9|exfalso; apply BC; replace k with K by llia; apply KZ; llia]);
      assert (j = k) by (destruct JJ as [H9|[_ H9]]; [exact H9 | llia]); subst j;
      exists k, (k + N.land (n - k) 0xfffffffffffffff8);
      pose proof (f8_le (n - k)); pose proof (f8_mod (n - k));
      splits; clo).
Qed.

Optimize Heap.

Lemma stp_case_15ea38: ∀ sp mem raddr d q n x19 x29 K mm md cc mn (s1:store) (t:list (exit*store)),
  stp_pre sp mem d q n K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 K mm md cc mn Prop (fun _ P => P) (fun _ P => P) True s1 0x15ea38 ->
  nextinv stp_prog (invs1 sp mem raddr d q n x19 x29 K mm md cc mn) (exits1 sp mem raddr d q n x19 x29 K mm md cc mn) false ((Addr 0x15ea38, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 K mm md cc mn s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  destruct PRE as (k & m & KK & KM & MN & M8 & AL & X0 & X1 & X5 & X6 & X7 & MEM & SP & X29).
  facts raddr x19 x29.
  repeat arm8_step.
  all: nrm.
  1: (exists k; splits; clo).
  2: (exists k; splits; clo).
  1: (assert (KM': k <> m) by (intro E; apply BC; rewrite E; reflexivity);
      assert (KM8: k + 8 <= m) by (clear - KM M8 KM'; lia);
      set (W := bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat k) Ⓠ[q + k]) in *;
      assert (NZB: ∀ i, i < 8 -> byte_of W i ≠ 0) by (apply haszero_test_zero; [apply qword_lt64 | apply N.eqb_eq; exact BC0]);
      assert (KL8: k + 8 <= K) by (destruct (N.le_gt_cases (k+8) K) as [H9|H9]; [exact H9|exfalso];
        apply (NZB (K - k)); [clear - H9 KK; lia|];
        unfold W; rewrite byte_of_qword by (clear - H9 KK; lia);
        replace (q + k + (K - k)) with (q + K) by (clear - H9 KK; lia);
        rewrite RD by (clear - H9 KK KM8 MN; lia); apply KZ; clear - H9 KK KM8 MN; lia);
      exists (k+8), m; splits; clo; try (rewrite bcp_word8 by exact AL; reflexivity)).
Qed.

Optimize Heap.

Lemma stp_case_15ea64: ∀ sp mem raddr d q n x19 x29 K mm md cc mn (s1:store) (t:list (exit*store)),
  stp_pre sp mem d q n K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 K mm md cc mn Prop (fun _ P => P) (fun _ P => P) True s1 0x15ea64 ->
  nextinv stp_prog (invs1 sp mem raddr d q n x19 x29 K mm md cc mn) (exits1 sp mem raddr d q n x19 x29 K mm md cc mn) false ((Addr 0x15ea64, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 K mm md cc mn s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  destruct PRE as (k & KK & X19 & X1 & X2 & MEM & SP & X29).
  facts raddr x19 x29.
  repeat arm8_step.
  all: nrm.
  1: (assert (EK: k = K) by llia; subst k; exists K; splits; clo).
  1: (match goal with H: _ Ⓑ[q + k] ≠ 0 |- _ => rewrite RD in H by llia; rename H into BZ end;
      assert (KK': k < K) by (destruct (N.lt_ge_cases k K) as [H9|H9]; [exact H9|exfalso; apply BZ; replace k with K by llia; apply KZ; llia]);
      exists (k+1); splits; clo; try (rewrite bcp_succ; reflexivity)).
  1: (match goal with H: _ Ⓑ[q + k] = 0 |- _ => rewrite RD in H by llia; rename H into BZ end;
      assert (EK: k = K) by (destruct (N.lt_ge_cases k K) as [H9|H9]; [destruct (NFq k H9 BZ) | llia]);
      subst k; exists (K+1); splits; clo; try (right; split; llia); try (rewrite bcp_succ; reflexivity)).
Qed.

Optimize Heap.

Lemma stp_case_15ea78: ∀ sp mem raddr d q n x19 x29 K mm md cc mn (s1:store) (t:list (exit*store)),
  stp_pre sp mem d q n K ->
  x19 < 18446744073709551616 -> x29 < 18446744073709551616 -> raddr < 18446744073709551616 ->
  d < 18446744073709551616 -> q < 18446744073709551616 -> n < 18446744073709551616 ->
  models arm8typctx s1 ->
  invs sp mem raddr d q n x19 x29 K mm md cc mn Prop (fun _ P => P) (fun _ P => P) True s1 0x15ea78 ->
  nextinv stp_prog (invs1 sp mem raddr d q n x19 x29 K mm md cc mn) (exits1 sp mem raddr d q n x19 x29 K mm md cc mn) false ((Addr 0x15ea78, s1) :: t).
Proof.
  intros sp mem raddr d q n x19 x29 K mm md cc mn s1 t PRE0 W19 W29 W30 W0 W1 W2 MDL1 PRE. hnf in PRE.
  destruct PRE as (j & JJ & X19 & X2 & MEM & SP & X29).
  facts raddr x19 x29.
  assert (JN: j <= n) by (destruct JJ as [->|[-> ?]]; llia).
  do 3 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply stp_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply memset_correct_in_stpncpy with (sp:=sp) (mem:=mem) (raddr:=raddr) (d:=d) (q:=q) (n:=n) (x19:=x19) (x29:=x29) (K:=K);
    first [ exact (fun _ _ _ H => H) | eassumption |
      (unfold s2; simpl_stores; change (2^64) with 18446744073709551616;
       first [ sassumption | sreflexivity | reflexivity | llia | (rewrite X19; llia) | (rewrite X2; llia) | (rewrite X19, X2; llia) |
                (unfold memset_full_defs.mf_side; right; right; rewrite ?X2; llia) ]) ].
  reflexivity.
  intros.
  assert (MDL3: models arm8typctx s') by (eapply preservation_exec_prog; try eassumption; apply stp_prog_welltyped).
  assert (S2M: s2 V_MEM64 = bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat j)) by (unfold s2; simpl_stores; rewrite ?MEM; reflexivity).
  assert (S2X0: s2 R_X0 = d + K) by (unfold s2; simpl_stores; rewrite ?X19; reflexivity).
  assert (S2X1: s2 R_X1 = 0) by (unfold s2; simpl_stores; reflexivity).
  assert (S2X2: s2 R_X2 = n - K) by (unfold s2; simpl_stores; rewrite ?X2; reflexivity).
  clearbody s2. rename s' into s3.
  destruct_inv 64 PRE.
  all: destruct PRE as ((R0 & RSP & R30 & BY & OT) & R19).
  all: rewrite ?S2M, ?S2X0, ?S2X1, ?S2X2 in *.
  all: pose proof (stp_mem_ok sp mem raddr d q n x19 x29 K j (s3 V_MEM64) PRE0 W19 W29 W30 JJ BY OT) as MO.
  all: destruct MO as (M1 & M2 & M3 & Q16 & Q32 & Q24).
  all: repeat arm8_step.
  all: unfold stp_post; splits.
  all: rewrite ?(msub_small 64 sp) by L64.
  all: try first [ sassumption | exact M1 | exact M2 | exact M3 | exact Q16 | exact Q32 | exact Q24 | (mods; llia) ].
Qed.

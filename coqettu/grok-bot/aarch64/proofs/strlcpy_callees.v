(* strlcpy callee lemmas and shared definitions: strlcpy_prog = strlcpy + strlen lifts, frame/precondition/memory definitions, the shared invariant family (strlcpy id 1, strlen id 0), strlen_correct_in_strlcpy, and the tactics used by the VC files -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
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
Import ARM8Notations.
Open Scope N.

Definition strlcpy_prog : program := updateall2 strlcpy_armv8.strlcpy_armv8 strlen_armv8.strlen_armv8.

Theorem strlcpy_prog_welltyped: welltyped_prog arm8typctx strlcpy_prog.
Proof.
  intros s a. unfold strlcpy_prog, updateall2, updateall.
  destruct (strlen_armv8.strlen_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (strlen_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strlcpy_armv8.welltyped.
Qed.

Lemma strlcpy_prog_mono: ∀ prog, strlcpy_armv8.strlcpy_armv8 ⊆2 prog -> strlen_armv8.strlen_armv8 ⊆2 prog -> strlcpy_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold strlcpy_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* the caller's memory after the prologue (stp x29,x30,[sp,#-32]!; str x19,[sp,#16]) *)
Definition slc_frame (sp mem raddr x19 x29 : N) :=
  mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19].

Definition slc_fin (sp mem raddr x19 x29 d q K : N) :=
  setmem 64 LittleE 1 (bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat K)) (d + K) 0.

Definition slc_mem (sp mem raddr x19 x29 d q n K : N) :=
  if n =? 0 then slc_frame sp mem raddr x19 x29 else slc_fin sp mem raddr x19 x29 d q K.

Definition slc_pre (sp mem d q n L K : N) :=
  nilfree mem q L /\ mem Ⓑ[q + L] = 0 /\ (n = 0 \/ (K < n /\ K <= L /\ (K = L \/ K + 1 = n))) /\
  32 <= sp /\ sp < 2^64 /\ d + n + 32 <= sp /\ q + L + 33 <= sp /\ q + n < 2^64 /\
  (q + L < d \/ d + n <= q).

Section Invariants.
  Variables (sp mem raddr d q n x19 x29 L K : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15eec4 => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x15ef1c => Inv 1 (∃ k, 0 < n /\ k <= K /\ msub 64 q d mod 8 = 0 /\ s R_X0 = d /\ s R_X1 = q + k /\ s R_X3 = d + k /\
                         s R_X2 = n - 1 - k /\ s R_X19 = n /\
                         s V_MEM64 = bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat k) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ef34 => Inv 1 (∃ k j, 0 < n /\ k < n - 1 /\ k <= K /\ (j = k \/ (j = k + 1 /\ k = L)) /\ msub 64 q d mod 8 = 0 /\
                         s R_X0 = d /\ s R_X1 = q + k /\ s R_X3 = d + k /\ s R_X2 = n - 1 - k /\ s R_X19 = n /\
                         s V_MEM64 = bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat j) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ef64 => Inv 1 (∃ k m, 0 < n /\ k <= K /\ k <= m /\ m <= n - 1 /\ (m - k) mod 8 = 0 /\ msub 64 q d mod 8 = 0 /\
                         s R_X0 = d /\ s R_X1 = q + k /\ s R_X3 = d + k /\ s R_X6 = q + m /\ s R_X7 = q + (n - 1) /\
                         s R_X8 = 0xfefefefefefefeff /\ s R_X19 = n /\
                         s V_MEM64 = bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat k) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15eef0 => Inv 1 (∃ k j, 0 < n /\ k <= K /\ (j = k \/ (j = k + 1 /\ k = L)) /\
                         s R_X0 = d /\ s R_X1 = q + k /\ s R_X3 = d + k /\ s R_X2 = d + (n - 1) /\ s R_X19 = n /\
                         s V_MEM64 = bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat j) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ef88 => Inv 1 (0 < n /\ s R_X0 = d /\ s R_X1 = q + K /\ s R_X3 = d + K /\
                         setmem 64 LittleE 1 (s V_MEM64) (d + K) 0 = slc_fin sp mem raddr x19 x29 d q K /\
                         s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ef90 => Inv 1 (∃ k, ((n = 0 /\ k = 0) \/ (0 < n /\ k = K)) /\ s R_X1 = q + k /\ s R_X19 = k /\
                         s V_MEM64 = slc_mem sp mem raddr x19 x29 d q n K /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15efa4 => Post 1 (s R_X0 = L /\ s V_MEM64 = slc_mem sp mem raddr x19 x29 d q n K /\
                          s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr)
    (* strlen (string at q) *)
    | 0x15efa8 => Inv 0 (s R_X0 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15efb4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = q /\ s R_X1 = q ⊕ k /\ nilfree mem q k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15efd8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = q /\ s R_X1 = q ⊕ k /\ nilfree mem q k /\
                         s R_X4 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15eff4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = q /\ s R_X1 = q ⊕ k /\ nilfree mem q k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15f000 => Post 0 (∃ k, k < 2^64 /\ s R_X0 = k /\ nilfree mem q k /\ mem Ⓑ[q + k] = 0 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strlcpy_prog invs.
  Definition invs0 := make_invs 0 strlcpy_prog invs.
  Definition exits1 := make_exits 1 strlcpy_prog invs.
  Definition invs1 := make_invs 1 strlcpy_prog invs.
End Invariants.

Theorem strlen_correct_in_strlcpy:
  ∀ prog s t xs'
    (P: strlcpy_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15efa8, s))
    (MDL: models arm8typctx s),
  ∀ d n L K,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) d (s R_X0) n (s R_X19) (s R_X29) L K)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) d (s R_X0) n (s R_X19) (s R_X29) L K)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  set (x29 := s R_X29). set (x19 := s R_X19).
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr p x29 x19.
  eapply satisfies_all_pmono with (p1:=strlcpy_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strlcpy_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & MEM & SP & X30 & X29 & X19).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    repeat arm8_step.
    exists 0. repeat split; try assumption.
    all: first [ apply nilfree_0 | rewrite N.add_0_r; symmetry; apply N.mod_small; exact P64 ].
  - destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists k. repeat split; assumption.
    + apply cbnz32_true in BC0; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC0; [|apply byte_lt32].
      exists k. repeat split; assumption.
  - destruct PRE as (k & KLT & X0 & X1 & NF & X4 & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists ((k+8) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le.
      intros i Hi. destruct (N.lt_ge_cases i k). apply NF; assumption.
      pose proof (haszero_test_zero _ (qword_lt64 mem (p+k)) BC (i-k) ltac:(lia)) as H8.
      rewrite byte_of_qword in H8 by lia. replace (p + k + (i - k)) with (p + i) in H8 by lia.
      exact H8.
    + exists k. repeat split; assumption.
  - destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + apply cbnz32_true in BC; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC; [|apply byte_lt32].
      exists k. repeat split; assumption.
Qed.


Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.
Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Lemma first_zero_unique: ∀ (f g: N -> N) L1 L2,
  (∀ i, i < L1 -> f i ≠ 0) -> f L1 = 0 -> (∀ i, i < L2 -> g i ≠ 0) -> g L2 = 0 ->
  (∀ i, i <= L1 -> g i = f i) -> L1 = L2.
Proof.
  intros f g L1 L2 F1 F0 G1 G0 E.
  destruct (N.lt_trichotomy L1 L2) as [H|[H|H]]; [|exact H|].
  - exfalso. apply (G1 L1 H). rewrite E by lia. exact F0.
  - exfalso. apply (F1 L2 H). rewrite <- E by lia. exact G0.
Qed.

Lemma sm0_idem: ∀ m a, setmem 64 LittleE 1 (setmem 64 LittleE 1 m a 0) a 0 = setmem 64 LittleE 1 m a 0.
Proof.
  intros. set (m1 := setmem 64 LittleE 1 m a 0).
  assert (G: getmem 64 LittleE 1 m1 a = 0) by (unfold m1; rewrite getmem_setmem by (vm_compute; discriminate); reflexivity).
  rewrite <- G at 1. apply setmem_getmem.
Qed.

Lemma f8_mod: ∀ x, N.land x 0xfffffffffffffff8 mod 8 = 0.
Proof.
  intro x. change 8 with (2^3). rewrite <- N.land_ones, <- N.land_assoc.
  change (N.land 0xfffffffffffffff8 (N.ones 3)) with 0. apply N.land_0_r.
Qed.

Lemma f8_le: ∀ x, N.land x 0xfffffffffffffff8 <= x.
Proof. intro x. apply N.land_le_l. Qed.

Ltac al3 := match goal with AL: msub 64 ?q ?d mod 8 = 0 |- msub 3 ?q ?d = 0 =>
  transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL] end.

Ltac prep :=
  match goal with PRE0: slc_pre _ _ _ _ _ _ _ |- _ =>
    destruct PRE0 as (NFq & ZL & NK & SP32 & SPlt & BD & BQ & QN & DISJ) end;
  change (2^64) with 18446744073709551616 in *;
  let C := fresh "C" in
  match goal with |- context [slc_frame ?sp ?mem ?raddr ?x19 ?x29] =>
    set (C := slc_frame sp mem raddr x19 x29) in * end.

Ltac facts raddr x19 x29 :=
  match goal with PRE0: slc_pre ?sp ?mem ?d ?q ?n ?L ?K |- _ =>
    try change (mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19]) with (slc_frame sp mem raddr x19 x29) in *;
    let F := fresh in pose proof PRE0 as F;
    destruct F as (NFq & ZL & NK & SP32 & SPlt & BD & BQ & QN & DISJ);
    assert (CB: ∀ a, a + 1 <= sp - 32 -> slc_frame sp mem raddr x19 x29 Ⓑ[a] = mem Ⓑ[a])
      by (let a := fresh "a" in let A := fresh "A" in intros a A; unfold slc_frame; rewrite !(msub_small 64 sp) by L64; memsimp; reflexivity);
    assert (RD: ∀ i j, i <= L -> j <= n -> bcp (slc_frame sp mem raddr x19 x29) d q (N.to_nat j) Ⓑ[q+i] = mem Ⓑ[q+i])
      by (let ii := fresh "ii" in let jj := fresh "jj" in let I := fresh "I" in let J := fresh "J" in intros ii jj I J; rewrite <- CB by lia; destruct DISJ as [DJ|DJ];
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

Ltac mods := repeat match goal with |- context [(?x) mod 18446744073709551616] => rewrite (N.mod_small x) by L64 end.

Ltac clo := try first [ assumption | reflexivity | (left; reflexivity) | al3 |
  match goal with
  | |- _ <= _ => lia | |- _ < _ => lia
  | |- bcp _ _ _ _ = _ => fail 1 | |- setmem _ _ _ _ _ _ = _ => fail 1
  | |- _ = _ => first [ lia | (rewrite msub_small by L64; lia) | (mods; lia) ] end ].

Ltac clean := repeat match goal with
  | H: context [getmem _ _ _ _ _] |- _ => clear H
  | H: context [bcp _ _ _ _] |- _ => clear H
  | H: context [setmem _ _ _ _ _ _] |- _ => clear H
  | H: ∀ _, _ |- _ => clear H
  | H: nilfree _ _ _ |- _ => clear H
  | H: models _ _ |- _ => clear H
  | H: exec_prog _ _ |- _ => clear H
  | H: ?f ?v = _ |- _ => match type of f with store => clear H | var -> N => clear H end
  end.
Ltac llia := clean; lia.
Ltac clo2 := try first [ sassumption | sreflexivity | al3 |
  match goal with
  | |- bcp _ _ _ _ = _ => fail 1 | |- setmem _ _ _ _ _ _ = _ => fail 1 | |- _ [Ⓠ _ := _] = _ => fail 1
  | |- _ => first [ llia | (rewrite N.mod_small by llia; llia) | (rewrite msub_small by L64; llia) ] end ].

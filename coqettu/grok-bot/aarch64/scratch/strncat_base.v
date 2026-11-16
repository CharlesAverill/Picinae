From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strncat_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame.
Import ARM8Notations.
Open Scope N.

Definition strncat_prog : program := updateall2 strncat_armv8.strncat_armv8 strlen_armv8.strlen_armv8.

Theorem strncat_prog_welltyped: welltyped_prog arm8typctx strncat_prog.
Proof.
  intros s a. unfold strncat_prog, updateall2, updateall.
  destruct (strlen_armv8.strlen_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (strlen_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strncat_armv8.welltyped.
Qed.

Lemma strncat_prog_mono: ∀ prog, strncat_armv8.strncat_armv8 ⊆2 prog -> strlen_armv8.strlen_armv8 ⊆2 prog -> strncat_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold strncat_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* the caller's memory after strncat's prologue (stp x29,x30,[sp,#-48]!; str x21,[sp,#32]; stp x19,x20,[sp,#16]) *)
Definition ncat_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 16 := x21] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20].

(* precondition: d is a string of length Ld; q has K nonzero bytes, and either K = n or q[K] = 0
   (so K = min(n, strnlen(q))); all bytes touched lie below the frame at sp-48; the written range
   [d+Ld, d+Ld+K] does not overlap the read range [q, q+K] (overlap is undefined behaviour in C). *)
Definition strncat_pre (sp mem d q n Ld K : N) :=
  nilfree mem d Ld /\ mem Ⓑ[d + Ld] = 0 /\ K <= n /\ n < 2^64 /\ nilfree mem q K /\ (K = n \/ mem Ⓑ[q + K] = 0) /\
  48 <= sp /\ sp < 2^64 /\ d + Ld + K + 1 <= sp - 48 /\ q + K + 1 <= sp - 48 /\
  (q + K < d + Ld \/ d + Ld + K < q).

Definition strncat_post (sp mem raddr d q x19 x20 x21 x29 Ld K : N) (s:store) :=
  s V_MEM64 = setmem 64 LittleE 1 (bcp (ncat_frame sp mem raddr x19 x20 x21 x29) (d + Ld) q (N.to_nat K)) (d + Ld + K) 0 /\
  s R_X0 = d /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29 /\ s R_X30 = raddr.

Section Invariants.
  Variables (sp mem raddr d q n x19 x20 x21 x29 Ld K : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strncat *)
    | 0x15f0b4 => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29)
    | 0x15f0e4 => Inv 1 (∃ k, k <= K /\ s R_X0 = d + Ld + k /\ s R_X2 = (d + Ld + n) mod 2^64 /\ s R_X19 = q + k /\
                         s R_X20 = n /\ s R_X21 = d /\
                         s V_MEM64 = bcp (ncat_frame sp mem raddr x19 x20 x21 x29) (d + Ld) q (N.to_nat k) /\
                         s R_SP = sp - 48 /\ s R_X29 = sp - 48)
    | 0x15f10c => Post 1 (strncat_post sp mem raddr d q x19 x20 x21 x29 Ld K s)
    (* strlen (string at d) *)
    | 0x15efa8 => Inv 0 (s R_X0 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | 0x15efb4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | 0x15efd8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s R_X4 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | 0x15eff4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | 0x15f000 => Post 0 (∃ k, k < 2^64 /\ s R_X0 = k /\ nilfree mem d k /\ mem Ⓑ[d + k] = 0 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strncat_prog invs.
  Definition invs0 := make_invs 0 strncat_prog invs.
  Definition exits1 := make_exits 1 strncat_prog invs.
  Definition invs1 := make_invs 1 strncat_prog invs.
End Invariants.

Theorem strlen_correct_in_strncat:
  ∀ prog s t xs'
    (P: strncat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15efa8, s))
    (MDL: models arm8typctx s),
  ∀ q n Ld K,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q n (s R_X19) (s R_X20) (s R_X21) (s R_X29) Ld K)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q n (s R_X19) (s R_X20) (s R_X21) (s R_X29) Ld K)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  set (x29 := s R_X29). set (x19 := s R_X19). set (x20 := s R_X20). set (x21 := s R_X21).
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  assert (X20: s R_X20 = x20) by reflexivity. assert (X21: s R_X21 = x21) by reflexivity.
  clearbody sp mem raddr p x29 x19 x20 x21.
  eapply satisfies_all_pmono with (p1:=strncat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 X19 X20 X21 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & MEM & SP & X30 & X29 & X19 & X20 & X21).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    repeat arm8_step.
    exists 0. repeat split; try assumption.
    all: first [ apply nilfree_0 | rewrite N.add_0_r; symmetry; apply N.mod_small; exact P64 ].
  - (* byte loop until X1 is 8-aligned *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19 & X20 & X21).
    repeat arm8_step.
    + exists k. repeat split; assumption.
    + apply cbnz32_true in BC0; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC0; [|apply byte_lt32].
      exists k. repeat split; assumption.
  - (* aligned word loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & X4 & MEM & SP & X30 & X29 & X19 & X20 & X21).
    repeat arm8_step.
    + exists ((k+8) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le.
      intros i Hi. destruct (N.lt_ge_cases i k). apply NF; assumption.
      pose proof (haszero_test_zero _ (qword_lt64 mem (p+k)) BC (i-k) ltac:(lia)) as H8.
      rewrite byte_of_qword in H8 by lia. replace (p + k + (i - k)) with (p + i) in H8 by lia.
      exact H8.
    + exists k. repeat split; assumption.
  - (* final byte loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19 & X20 & X21).
    repeat arm8_step.
    + apply cbnz32_true in BC; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC; [|apply byte_lt32].
      exists k. repeat split; assumption.
Qed.

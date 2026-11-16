From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strchr_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep.
Import ARM8Notations.
Open Scope N.

Definition strchr_prog : program :=
  updateall2 (updateall2 strchr_armv8.strchr_armv8 strchrnul_armv8.strchrnul_armv8) strlen_armv8.strlen_armv8.

Ltac contains_tac SC :=
  repeat first
  [ exact SC | discriminate SC | (rewrite SC; reflexivity)
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].

Lemma strchr_prog_contains2: strchr_armv8.strchr_armv8 ⊆2 strchr_prog.
Proof.
  intros s a insn SC. unfold strchr_prog, updateall2, updateall, strlen_armv8.strlen_armv8, strchrnul_armv8.strchrnul_armv8.
  contains_tac SC.
Qed.

Lemma strchr_prog_contains1: strchrnul_armv8.strchrnul_armv8 ⊆2 strchr_prog.
Proof.
  intros s a insn SC. unfold strchr_prog, updateall2, updateall, strlen_armv8.strlen_armv8.
  contains_tac SC.
Qed.

Lemma strchr_prog_contains0: strlen_armv8.strlen_armv8 ⊆2 strchr_prog.
Proof. apply subset_updateall2. Qed.

Theorem strchr_prog_welltyped: welltyped_prog arm8typctx strchr_prog.
Proof.
  intros s a. unfold strchr_prog, updateall2, updateall.
  destruct (strlen_armv8.strlen_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (strlen_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
  destruct (strchrnul_armv8.strchrnul_armv8 s a) as [[sz q]|] eqn:TN.
    pose proof (strchrnul_armv8.welltyped s a) as WT. rewrite TN in WT. exact WT.
    apply strchr_armv8.welltyped.
Qed.

Lemma strchr_prog_mono: ∀ prog, strchr_armv8.strchr_armv8 ⊆2 prog -> strchrnul_armv8.strchrnul_armv8 ⊆2 prog ->
  strlen_armv8.strlen_armv8 ⊆2 prog -> strchr_prog ⊆2 prog.
Proof.
  intros prog P2 P1 P0. unfold strchr_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono.
  rewrite <- (updateall2_subset _ _ P1). apply updateall2_mono. exact P2.
Qed.

(* The first k bytes at p are neither 0 nor c. *)
Definition scan (m:memory) (p:addr) (c:N) (k:N) :=
  ∀ i, i < k -> m Ⓑ[p + i] ≠ 0 /\ m Ⓑ[p + i] ≠ c.

Lemma scan_0: ∀ m p c, scan m p c 0.
Proof. intros m p c i H. destruct i; discriminate. Qed.

Lemma scan_succ: ∀ m p c k, scan m p c k -> m Ⓑ[p + k] ≠ 0 -> m Ⓑ[p + k] ≠ c ->
  scan m p c (k+1).
Proof.
  intros m p c k W N0 NC i I. destruct (N.lt_ge_cases i k). apply W; assumption.
  replace i with k by lia. split; assumption.
Qed.

Lemma scan_mono: ∀ m p c k k', k' <= k -> scan m p c k -> scan m p c k'.
Proof. intros m p c k k' LE W i I. apply W. lia. Qed.

Lemma scan_nilfree: ∀ m p k, nilfree m p k -> scan m p 0 k.
Proof. intros m p k NF i I. split; apply NF; exact I. Qed.

(* strchrnul result for byte c (< 256). *)
Definition strchrnul_spec (m:memory) (p c r:N) :=
  ∃ k, k < 2^64 /\ scan m p c k /\ (m Ⓑ[p + k] = 0 \/ m Ⓑ[p + k] = c) /\ r = p ⊕ k.


(* Word test of strchrnul: haszero(x) | haszero(x ^ splat c), masked; if it is
   zero, no byte of the quadword is 0 or c. *)
Lemma chrnul_test: ∀ m a c, c < 2^8 ->
  ((m Ⓠ[ a ] ⊖ 72340172838076673
    .& (m Ⓠ[ a ] .^ 18446744073709551615)
    .| (m Ⓠ[ a ] .^ (c * 72340172838076673 .^ 18446744073709551615))
       .& (m Ⓠ[ a ] .^ c * 72340172838076673) ⊖ 72340172838076673)
   .& 9259542123273814144 =? 0) = true ->
  ∀ i, i < 8 -> m Ⓑ[a + i] ≠ 0 /\ m Ⓑ[a + i] ≠ c.
Proof.
  intros m a c C T i I. apply N.eqb_eq in T.
  rewrite N.land_lor_distr_l in T. apply N.lor_eq_0_iff in T. destruct T as [T1 T2].
  split.
  - pose proof (haszero_test_zero _ (qword_lt64 m a) (proj2 (N.eqb_eq _ _) T1) i I) as H.
    rewrite byte_of_qword in H by lia. exact H.
  - rewrite <- N.lxor_assoc, (N.lxor_comm (m Ⓠ[a])) in T2.
    rewrite (N.land_comm ((c * 72340172838076673 .^ m Ⓠ[a]) .^ 18446744073709551615)) in T2.
    exact (hasbyte_test_zero m a c C (proj2 (N.eqb_eq _ _) T2) i I).
Qed.

Ltac post_k k :=
  splits; try assumption; left; splits; [reflexivity | assumption |];
  exists k; splits; [assumption | assumption | | reflexivity];
  first [ left; apply N.eqb_eq; assumption | right; apply N.eqb_eq; assumption ].

Ltac adv1 k :=
  exists ((k+1) mod 2^64);
  splits; first [ assumption | reflexivity | apply mp2_mod_lt | apply ptr_adv
                | (eapply scan_mono; [apply mod64_le | apply scan_succ; [assumption | apply N.eqb_neq; assumption ..]]) ].

Definition nul_frame (sp mem raddr p x29:N) := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 8 := p].

Section Invariants.
  Variables (sp mem raddr p c x29 : N).
  Definition c8 := c mod 2^8.
  (* strchrnul's 32-byte frame (c8 = 0 path only): saved X29, X30 and s. *)
  Definition frame_mem := nul_frame sp mem raddr p x29.
  (* strchr's 32-byte frame: saved X29, X30 and c (32-bit, at sp-4). *)
  Definition chr_frame := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓓ sp ⊖ 4 := c].
  Definition strchr_post (s:store) :=
    s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\
    ∃ m' r, s V_MEM64 = m' /\
      (m' = chr_frame \/ m' = nul_frame (sp ⊖ 32) chr_frame 0x15ebdc p (sp ⊖ 32)) /\
      strchrnul_spec m' p c8 r /\ s R_X0 = (if m' Ⓑ[r] =? c8 then r else 0).
  Definition strchrnul_post (s:store) :=
    s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\
    ((s V_MEM64 = mem /\ c8 ≠ 0 /\ strchrnul_spec mem p c8 (s R_X0)) \/
     (s V_MEM64 = frame_mem /\ c8 = 0 /\ strchrnul_spec frame_mem p 0 (s R_X0))).
  Definition FR (s:store) := s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strchr (s = p, c = c) *)
    | 0x15ebcc => Inv 2 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\
                         s R_X30 = raddr /\ s R_X29 = x29)
    | 0x15ebf0 => Post 2 (strchr_post s)
    (* strchrnul (s = p, c = c) *)
    | 0x15ebf4 => Inv 1 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\
                         s R_X30 = raddr /\ s R_X29 = x29)
    (* byte loop until 8-aligned: tst x2,#7 *)
    | 0x15ec00 => Inv 1 (∃ k, k < 2^64 /\ s R_X2 = p ⊕ k /\ s R_X1 = c8 /\ c8 ≠ 0 /\ scan mem p c8 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    (* word loop: ldr x3,[x2] *)
    | 0x15ec58 => Inv 1 (∃ k, k < 2^64 /\ s R_X2 = p ⊕ k /\ s R_X1 = c8 /\ c8 ≠ 0 /\ scan mem p c8 k /\
                         s R_X6 = c8 * 0x0101010101010101 /\ s R_X7 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    (* final byte loop: ldrb w0,[x2] *)
    | 0x15ec8c => Inv 1 (∃ k, k < 2^64 /\ s R_X2 = p ⊕ k /\ s R_X1 = c8 /\ c8 ≠ 0 /\ scan mem p c8 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x15ec40 => Post 1 (strchrnul_post s)
    | 0x15eca0 => Post 1 (strchrnul_post s)
    (* strlen (s = p) *)
    | 0x15efa8 => Inv 0 (s R_X0 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15efb4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15efd8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s R_X4 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15eff4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f000 => Post 0 (∃ k, k < 2^64 /\ s R_X0 = k /\ nilfree mem p k /\ mem Ⓑ[p + k] = 0 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strchr_prog invs.
  Definition invs0 := make_invs 0 strchr_prog invs.
  Definition exits1 := make_exits 1 strchr_prog invs.
  Definition invs1 := make_invs 1 strchr_prog invs.
  Definition exits2 := make_exits 2 strchr_prog invs.
  Definition invs2 := make_invs 2 strchr_prog invs.
End Invariants.

Theorem strlen_correct_in_strchr:
  ∀ prog s t xs'
    (P2: strchr_armv8.strchr_armv8 ⊆2 prog) (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15efa8, s))
    (MDL: models arm8typctx s),
  ∀ c x29,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) c x29)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) c x29)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  clearbody sp mem raddr p.
  eapply satisfies_all_pmono with (p1:=strchr_prog).
    apply strchr_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    repeat arm8_step.
    exists 0. repeat split; try assumption.
    all: first [ apply nilfree_0 | rewrite N.add_0_r; symmetry; apply N.mod_small; exact P64 ].
  - (* byte loop until X1 is 8-aligned *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30).
    repeat arm8_step.
    + exists k. repeat split; assumption.
    + apply cbnz32_true in BC0; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC0; [|apply byte_lt32].
      exists k. repeat split; assumption.
  - (* aligned word loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & X4 & MEM & SP & X30).
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
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30).
    repeat arm8_step.
    + apply cbnz32_true in BC; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC; [|apply byte_lt32].
      exists k. repeat split; assumption.
Qed.

Theorem strchrnul_correct_in_strchr:
  ∀ prog s sp mem raddr p c x29 t xs'
    (P2: strchr_armv8.strchr_armv8 ⊆2 prog) (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15ebf4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr p c x29) (exits1 sp mem raddr p c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strchr_prog).
    apply strchr_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  assert (C8: c8 c < 2^8) by (apply N.mod_lt; discriminate).
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & X1 & MEM & SP & X30 & X29).
    pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64. simpl in P64.
    pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
    pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
    grok_step. grok_step. grok_step.
    + (* c8 = 0: call strlen *)
      apply N.eqb_eq in BC.
      do 4 arm8_step.
      set (s2 := update _ _ _).
      eapply models_after_steps. eassumption. apply strchr_prog_welltyped. intro MDL2.
      eapply (perform_call 0). reflexivity.
      intros. eapply strlen_correct_in_strchr with (c:=c) (x29:=x29);
        first [ exact strchr_prog_contains2 | exact strchr_prog_contains1 | exact strchr_prog_contains0 | eassumption | reflexivity ].
      reflexivity.
      intros.
      unfold s2 in PRE. psimpl in PRE.
      assert (MDL': models arm8typctx s').
        eapply preservation_exec_prog; try eassumption. apply strchr_prog_welltyped.
      set (t' := t2++t0++_::t) in *. clearbody s2 t'.
      clear - PRE MDL' SP64 P64 R64 X2964 BC.
      rename MDL' into MDL. rename s' into s.
      destruct_inv 64 PRE.
      destruct PRE as (k & KLT & R0 & NF & Z & MEM & SP & X30).
      repeat arm8_step.
      splits; try (apply N.mod_small; assumption).
      right. splits. reflexivity. exact BC.
      exists k. splits. exact KLT. apply scan_nilfree; exact NF. left; exact Z. reflexivity.
    + (* c8 <> 0: byte loop with k = 0 *)
      apply N.eqb_neq in BC.
      exists 0. rewrite N.add_0_r, N.mod_small by exact P64.
      splits; first [ reflexivity | assumption | apply scan_0 | lia ].
  - (* byte loop until aligned *)
    destruct PRE as (k & KLT & X2 & X1 & CNZ & SC & MEM & SP & X30 & X29).
    repeat grok_step.
    all: first [ post_k k | adv1 k |
                 (exists k; splits; try assumption; try reflexivity;
                  rewrite N.shiftr_0_r, (N.mod_small (c8 c)), scast_small32 by lia;
                  apply N.mod_small; lia) ].
  - (* word loop *)
    destruct PRE as (k & KLT & X2 & X1 & CNZ & SC & X6 & X7 & MEM & SP & X30 & X29).
    repeat grok_step.
    + exists ((k+8) mod 2^64). splits; try assumption; try reflexivity.
      apply mp2_mod_lt. apply ptr_adv.
      eapply scan_mono. apply mod64_le.
      intros i Hi. destruct (N.lt_ge_cases i k). apply SC; assumption.
      pose proof (chrnul_test _ _ _ C8 BC (i-k) ltac:(lia)) as H8.
      replace (p + k + (i - k)) with (p + i) in H8 by lia. exact H8.
    + exists k. splits; try assumption; try reflexivity.
  - (* final byte loop *)
    destruct PRE as (k & KLT & X2 & X1 & CNZ & SC & MEM & SP & X30 & X29).
    repeat grok_step.
    all: first [ post_k k | adv1 k ].
Qed.

Theorem strchr_partial_correctness:
  ∀ prog s sp mem raddr p c x29 t xs'
    (P2: strchr_armv8.strchr_armv8 ⊆2 prog) (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15ebcc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs2 sp mem raddr p c x29) (exits2 sp mem raddr p c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strchr_prog).
    apply strchr_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64. simpl in P64.
  pose proof (MDL1 R_X1 64 eq_refl) as C64. rewrite X1 in C64. simpl in C64.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  do 4 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strchr_prog_welltyped. intro MDL2.
  eapply (perform_call 1). reflexivity.
  intros. eapply strchrnul_correct_in_strchr;
    first [ exact strchr_prog_contains2 | exact strchr_prog_contains1 | exact strchr_prog_contains0 | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strchr_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 P64 C64 R64 X2964.
  rename MDL' into MDL. rename s' into s.
  destruct_inv 64 PRE.
  destruct PRE as (SP & X30 & X29 & [(MEM & CNZ & SPEC) | (MEM & CZ & SPEC)]).
  - repeat arm8_step.
    all: splits; try (apply N.mod_small; assumption).
    all: eexists _, (s R_X0); splits; [ reflexivity | left; reflexivity | exact SPEC | ].
    all: dump_ctx. all: admit.
  - unfold frame_mem, nul_frame in MEM. repeat arm8_step.
    all: splits; try (apply N.mod_small; assumption).
    all: eexists _, (s R_X0); splits; [ reflexivity | right; reflexivity | unfold c8 in *; rewrite CZ; exact SPEC | ].
    all: dump_ctx. all: admit.
Admitted.

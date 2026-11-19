From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strcat_armv8 strcpy_armv8 stpcpy_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr.
Import ARM8Notations.
Open Scope N.

Definition strcat_prog : program :=
  updateall2 (updateall2 (updateall2 strcat_armv8.strcat_armv8 strcpy_armv8.strcpy_armv8)
    stpcpy_armv8.stpcpy_armv8) strlen_armv8.strlen_armv8.

Ltac contains_tac SC :=
  repeat first
  [ exact SC | discriminate SC | (rewrite SC; reflexivity)
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].

Lemma strcat_prog_contains2: strcpy_armv8.strcpy_armv8 ⊆2 strcat_prog.
Proof.
  intros s a insn SC. unfold strcat_prog, updateall2, updateall, strlen_armv8.strlen_armv8, stpcpy_armv8.stpcpy_armv8.
  contains_tac SC.
Qed.

Theorem strcat_prog_welltyped: welltyped_prog arm8typctx strcat_prog.
Proof.
  intros s a. unfold strcat_prog, updateall2, updateall.
  destruct (strlen_armv8.strlen_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (strlen_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
  destruct (stpcpy_armv8.stpcpy_armv8 s a) as [[sz q]|] eqn:T1.
    pose proof (stpcpy_armv8.welltyped s a) as WT. rewrite T1 in WT. exact WT.
  destruct (strcpy_armv8.strcpy_armv8 s a) as [[sz q]|] eqn:T2.
    pose proof (strcpy_armv8.welltyped s a) as WT. rewrite T2 in WT. exact WT.
    apply strcat_armv8.welltyped.
Qed.

Lemma strcat_prog_mono: ∀ prog, strcat_armv8.strcat_armv8 ⊆2 prog -> strcpy_armv8.strcpy_armv8 ⊆2 prog ->
  stpcpy_armv8.stpcpy_armv8 ⊆2 prog -> strlen_armv8.strlen_armv8 ⊆2 prog -> strcat_prog ⊆2 prog.
Proof.
  intros prog P3 P2 P1 P0. unfold strcat_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono.
  rewrite <- (updateall2_subset _ _ P1). apply updateall2_mono.
  rewrite <- (updateall2_subset _ _ P2). apply updateall2_mono. exact P3.
Qed.

Definition frame_mem (sp mem raddr x29 x19 : N) := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19].
Definition cat_frame (sp mem raddr q x29 x19 : N) := mem [Ⓠ sp ⊖ 48 := x29] [Ⓠ sp ⊖ 40 := raddr] [Ⓠ sp ⊖ 32 := x19] [Ⓠ sp ⊖ 8 := q].
Definition strcpy_post (sp mem raddr d q x29 x19 : N) (s:store) :=
  ∃ k, bnz (frame_mem sp mem raddr x29 x19) d q k /\
       getmem 64 LittleE 1 (bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat k)) (q + k) = 0 /\
       s V_MEM64 = bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat (k+1)) /\ s R_X0 = d /\ s R_SP = sp /\
       s R_X29 = bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 32] /\
       s R_X30 = bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 24] /\
       s R_X19 = bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 16].
(* strcat: L = strlen(d) on its frame memory C, then strcpy(d+L, q) runs with
   SP = sp-48 and saves X29 = sp-48, X30 = 0x15ebbc, X19 = d in its own frame. *)
Definition strcat_post (sp mem raddr d q x29 x19 : N) (s:store) :=
  let C := cat_frame sp mem raddr q x29 x19 in
  let F := frame_mem (sp ⊖ 48) C 0x15ebbc (sp ⊖ 48) d in
  ∃ L k, L < 2^64 /\ nilfree C d L /\ C Ⓑ[d + L] = 0 /\
    bnz F (d ⊕ L) q k /\ getmem 64 LittleE 1 (bcp F (d ⊕ L) q (N.to_nat k)) (q + k) = 0 /\
    s V_MEM64 = bcp F (d ⊕ L) q (N.to_nat (k+1)) /\
    s R_X0 = bcp F (d ⊕ L) q (N.to_nat (k+1)) Ⓠ[sp ⊖ 64] /\ s R_SP = sp /\
    s R_X29 = bcp F (d ⊕ L) q (N.to_nat (k+1)) Ⓠ[sp ⊖ 48] /\
    s R_X30 = bcp F (d ⊕ L) q (N.to_nat (k+1)) Ⓠ[sp ⊖ 40] /\
    s R_X19 = bcp F (d ⊕ L) q (N.to_nat (k+1)) Ⓠ[sp ⊖ 32].

Section Invariants.
  Variables (sp mem raddr d q x29 x19 : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strcat *)
    | 0x15eb98 => Inv 3 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15ebc8 => Post 3 (strcat_post sp mem raddr d q x29 x19 s)
    (* strcpy *)
    | 0x15eccc => Inv 2 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15ecec => Post 2 (strcpy_post sp mem raddr d q x29 x19 s)
    (* stpcpy *)
    | 0x15e950 => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e95c => Inv 1 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e990 => Inv 1 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X4 = K8 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e9ac => Inv 1 (∃ k, s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e9bc => Post 1 (∃ k, bnz mem d q k /\ getmem 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k) = 0 /\
                          s V_MEM64 = bcp mem d q (N.to_nat (k+1)) /\
                          s R_X0 = (d + k) mod 2^64 /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    (* strlen (string at d) *)
    | 0x15efa8 => Inv 0 (s R_X0 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15efb4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15efd8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s R_X4 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15eff4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15f000 => Post 0 (∃ k, k < 2^64 /\ s R_X0 = k /\ nilfree mem d k /\ mem Ⓑ[d + k] = 0 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strcat_prog invs.
  Definition invs0 := make_invs 0 strcat_prog invs.
  Definition exits1 := make_exits 1 strcat_prog invs.
  Definition invs1 := make_invs 1 strcat_prog invs.
  Definition exits2 := make_exits 2 strcat_prog invs.
  Definition invs2 := make_invs 2 strcat_prog invs.
  Definition exits3 := make_exits 3 strcat_prog invs.
  Definition invs3 := make_invs 3 strcat_prog invs.
End Invariants.

Ltac al3 := match goal with AL: msub 64 ?q ?d mod 8 = 0 |- msub 3 ?q ?d = 0 =>
  transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL] end.
Ltac modeq := rewrite ?N.Div0.add_mod_idemp_r, ?N.Div0.add_mod_idemp_l; f_equal; lia.

Theorem strlen_correct_in_strcat:
  ∀ prog s t xs'
    (P: strcat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15efa8, s))
    (MDL: models arm8typctx s),
  ∀ q,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q (s R_X29) (s R_X19))
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q (s R_X29) (s R_X19))
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  set (x29 := s R_X29). set (x19 := s R_X19).
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr p x29 x19.
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & MEM & SP & X30 & X29 & X19).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    repeat arm8_step.
    exists 0. repeat split; try assumption.
    all: first [ apply nilfree_0 | rewrite N.add_0_r; symmetry; apply N.mod_small; exact P64 ].
  - (* byte loop until X1 is 8-aligned *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists k. repeat split; assumption.
    + apply cbnz32_true in BC0; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC0; [|apply byte_lt32].
      exists k. repeat split; assumption.
  - (* aligned word loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & X4 & MEM & SP & X30 & X29 & X19).
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
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + apply cbnz32_true in BC; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC; [|apply byte_lt32].
      exists k. repeat split; assumption.
Qed.

Theorem stpcpy_correct_in_strcat:
  ∀ prog s t xs'
    (P: strcat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e950, s))
    (MDL: models arm8typctx s),
  satisfies_all prog
    (invs1 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X29) (s R_X19))
    (exits1 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X29) (s R_X19))
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (d := s R_X0).
  set (q := s R_X1). set (x29 := s R_X29). set (x19 := s R_X19).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = d) by reflexivity.
  assert (X1: s R_X1 = q) by reflexivity. assert (X29: s R_X29 = x29) by reflexivity.
  assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr d q x29 x19.
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
    pose proof (MDL1 R_X0 64 eq_refl) as BD. pose proof (MDL1 R_X1 64 eq_refl) as BQ.
    rewrite X0 in BD. rewrite X1 in BQ.
    repeat arm8_step.
    + exists 0. apply N.eqb_eq in BC. split.
      * transitivity (msub 64 q d mod 2^3).
        rewrite msub_mod_pow2. reflexivity. apply xor_mod8. exact BC.
      * repeat split; rewrite ?N.add_0_r, ?N.mod_small by assumption; try assumption; try reflexivity.
        intros i I. lia.
    + exists 0.
      repeat split; rewrite ?N.add_0_r, ?N.mod_small by assumption; try assumption; try reflexivity.
      intros i I. lia.
  - destruct PRE as (k & AL & X0 & X1 & NZ & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists k. split. al3. split. reflexivity. repeat split; assumption.
    + exists k. apply N.eqb_eq in BC0. repeat split; try assumption. rewrite bcp_succ. reflexivity.
    + exists (k+1). apply N.eqb_neq in BC0. split. al3. repeat split; try assumption.
      * modeq.
      * modeq.
      * apply bnz_succ; assumption.
      * rewrite bcp_succ. reflexivity.
  - destruct PRE as (k & AL & X4 & X0 & X1 & NZ & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists (k+8). apply N.eqb_eq in BC. split. al3. split. reflexivity. repeat split; try assumption.
      * modeq.
      * modeq.
      * apply (bnz_word mem d q k _ AL eq_refl); [|exact NZ].
        apply haszero_none'; [apply getmem_bound | exact BC].
      * rewrite bcp_word8 by exact AL. reflexivity.
    + exists k. repeat split; assumption.
  - destruct PRE as (k & X0 & X1 & NZ & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    all: pose proof (getmem_bound 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k)) as B;
         change (2^(1*8)) with (2^8) in B;
         destruct (byte_test _ _ B BC) as [[T NZK] | [T ZK]]; try discriminate T.
    + exists (k+1). repeat split; try assumption.
      * modeq.
      * modeq.
      * apply bnz_succ; assumption.
      * rewrite bcp_succ. reflexivity.
    + exists k. repeat split; try assumption. rewrite bcp_succ. reflexivity.
Qed.

Theorem strcpy_correct_in_strcat:
  ∀ prog s sp mem raddr d q x29 x19 t xs'
    (P: strcat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eccc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X29: s R_X29 = x29) (X19: s R_X19 = x19),
  satisfies_all prog (invs2 sp mem raddr d q x29 x19) (exits2 sp mem raddr d q x29 x19) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as D64. rewrite X0 in D64. simpl in D64.
  do 5 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcat_prog_welltyped. intro MDL2.
  eapply (perform_call 1). reflexivity.
  intros. eapply stpcpy_correct_in_strcat; first [ exact (fun _ _ _ H => H) | eassumption ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcat_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 D64 X1.
  rename MDL' into MDL. rename s' into s.
  destruct_inv 64 PRE.
  destruct PRE as (k & NZ & Z & MEM & R0 & SP & X30 & X29 & X19).
  repeat arm8_step.
  rewrite X1 in *. exists k. unfold frame_mem, strcpy_post.
  repeat split; try assumption; try reflexivity. apply N.mod_small; exact SP64.
Qed.

Theorem strcat_partial_correctness:
  ∀ prog s sp mem raddr d q x29 x19 t xs'
    (P3: strcat_armv8.strcat_armv8 ⊆2 prog) (P2: strcpy_armv8.strcpy_armv8 ⊆2 prog)
    (P1: stpcpy_armv8.stpcpy_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eb98, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X29: s R_X29 = x29) (X19: s R_X19 = x19),
  satisfies_all prog (invs3 sp mem raddr d q x29 x19) (exits3 sp mem raddr d q x29 x19) (xs'::t).
Proof.
  intros.
  assert (PP: strcat_prog ⊆2 prog) by (apply strcat_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs3, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as D64. rewrite X0 in D64. simpl in D64.
  pose proof (MDL1 R_X1 64 eq_refl) as Q64. rewrite X1 in Q64. simpl in Q64.
  do 6 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcat_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply strlen_correct_in_strcat with (q := q); first [ exact (fun _ _ _ H => H) | eassumption ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcat_prog_welltyped.
  clearbody s2.
  clear - PRE MDL' SP64 D64 Q64 X0.
  rename MDL' into MDL. rename s' into s0.
  destruct_inv 64 PRE.
  destruct PRE as (L & LLT & R0 & NF & ZL & MEM & SP & X30 & X29 & X19).
  rename SP into SP1. rename MEM into MEM1.
  do 4 arm8_step.
  rewrite (N.mod_small q) by exact Q64.
  set (s3 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcat_prog_welltyped. intro MDL3.
  eapply (perform_call 2). reflexivity.
  intros. eapply strcpy_correct_in_strcat; first [ exact (fun _ _ _ H => H) | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s3 in PRE. unfold strcpy_post, frame_mem in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcat_prog_welltyped.
  clearbody s3.
  clear - PRE MDL' SP64 D64 Q64 NF ZL LLT SP1 MEM1.
  rename MDL' into MDL0. rename s' into s4.
  destruct_inv 64 PRE.
  destruct PRE as (k & NZ & Z & MEM & R0 & SP & X29 & X30 & X19).
  repeat arm8_step.
  all: dump_ctx.
Admitted.
(*
  splits; try assumption; try reflexivity.
  all: dump_ctx.
Admitted.
*)

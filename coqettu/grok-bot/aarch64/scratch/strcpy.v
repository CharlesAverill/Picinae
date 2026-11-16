From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strcpy_armv8 stpcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr.
Import ARM8Notations.
Open Scope N.

Definition strcpy_prog : program := updateall2 strcpy_armv8.strcpy_armv8 stpcpy_armv8.stpcpy_armv8.

Lemma strcpy_prog_contains: strcpy_armv8.strcpy_armv8 ⊆2 strcpy_prog.
Proof.
  intros s a insn SC. unfold strcpy_prog, updateall2, updateall, stpcpy_armv8.stpcpy_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem strcpy_prog_welltyped: welltyped_prog arm8typctx strcpy_prog.
Proof.
  intros s a. unfold strcpy_prog, updateall2, updateall.
  destruct (stpcpy_armv8.stpcpy_armv8 s a) as [[sz q']|] eqn:TL.
    pose proof (stpcpy_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply strcpy_armv8.welltyped.
Qed.

Section Invariants.
  Variables (sp mem raddr d q x29 x19 : N).
  Definition frame_mem := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19].
  Definition strcpy_post (s:store) :=
    ∃ k, bnz frame_mem d q k /\ getmem 64 LittleE 1 (bcp frame_mem d q (N.to_nat k)) (q + k) = 0 /\
         s V_MEM64 = bcp frame_mem d q (N.to_nat (k+1)) /\ s R_X0 = d /\ s R_SP = sp /\
         s R_X29 = bcp frame_mem d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 32] /\
         s R_X30 = bcp frame_mem d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 24] /\
         s R_X19 = bcp frame_mem d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 16].
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strcpy *)
    | 0x15eccc => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15ecec => Post 1 (strcpy_post s)
    (* stpcpy callee; x29/x19 are the values it must leave alone *)
    | 0x15e950 => Inv 0 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e95c => Inv 0 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e990 => Inv 0 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X4 = K8 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e9ac => Inv 0 (∃ k, s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e9bc => Post 0 (∃ k, bnz mem d q k /\ getmem 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k) = 0 /\
                          s V_MEM64 = bcp mem d q (N.to_nat (k+1)) /\
                          s R_X0 = (d + k) mod 2^64 /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strcpy_prog invs.
  Definition invs0 := make_invs 0 strcpy_prog invs.
  Definition exits1 := make_exits 1 strcpy_prog invs.
  Definition invs1 := make_invs 1 strcpy_prog invs.
End Invariants.

Ltac al3 := match goal with AL: msub 64 ?q ?d mod 8 = 0 |- msub 3 ?q ?d = 0 =>
  transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL] end.
Ltac modeq := rewrite ?N.Div0.add_mod_idemp_r, ?N.Div0.add_mod_idemp_l; f_equal; lia.

Theorem stpcpy_correct_in_strcpy:
  ∀ prog s t xs'
    (P1: strcpy_armv8.strcpy_armv8 ⊆2 prog) (P0: stpcpy_armv8.stpcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e950, s))
    (MDL: models arm8typctx s),
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X29) (s R_X19))
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X29) (s R_X19))
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
  eapply satisfies_all_pmono with (p1:=strcpy_prog).
    unfold strcpy_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcpy_prog_welltyped. intro MDL1.
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

Theorem strcpy_partial_correctness:
  ∀ prog s sp mem raddr d q x29 x19 t xs'
    (P1: strcpy_armv8.strcpy_armv8 ⊆2 prog) (P0: stpcpy_armv8.stpcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eccc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X29: s R_X29 = x29) (X19: s R_X19 = x19),
  satisfies_all prog (invs1 sp mem raddr d q x29 x19) (exits1 sp mem raddr d q x29 x19) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strcpy_prog).
    unfold strcpy_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcpy_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as D64. rewrite X0 in D64. simpl in D64.
  do 5 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcpy_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply stpcpy_correct_in_strcpy;
    first [ exact strcpy_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcpy_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 D64 X1.
  rename MDL' into MDL. rename s' into s.
  destruct_inv 64 PRE.
  destruct PRE as (k & NZ & Z & MEM & R0 & SP & X30 & X29 & X19).
  repeat arm8_step.
  rewrite X1 in *. exists k. unfold frame_mem.
  repeat split; try assumption; try reflexivity. apply N.mod_small; exact SP64.
Qed.

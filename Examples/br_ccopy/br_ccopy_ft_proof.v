Require Import br_ccopy_ft.
Require Import Picinae_riscv.
Import RISCVNotations.
Require Import NArith.
Require Import List.
Require Import Lia ZifyN ZifyBool.

Import ListNotations.
Open Scope N_scope.

Section Invariants.
    Variable ctl : N.
    Variable dst src : addr.
    Variable len : N.
    Variable mem base_mem : memory.

    Definition k_equal (mem : memory) (p1 p2 : addr) (k : N) : Prop :=
        forall (i : N),
            i < k ->
            mem Ⓑ[p1 + i] = mem Ⓑ[p2 + i].

    Definition mem_equal (mem1 mem2 : memory) : Prop :=
        forall (i : N),
            mem1 Ⓑ[i] = mem2 Ⓑ[i].

    Definition postcondition (s : store) : Prop :=
        (ctl = 0 -> mem_equal base_mem (s V_MEM32)) /\
        (ctl = 1 ->
            k_equal (s V_MEM32) dst src len).

    Definition neg (n : N) : N := 0 ⊖ n.

    Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0 (
                s R_A0 = ctl /\ s R_A1 = dst /\ s R_A2 = src /\ s R_A3 = len /\
                s V_MEM32 = mem /\
                s V_MEM32 = base_mem /\
                ~ overlap 32 src len dst len
            )
        | 0x20 => Inv 0 (exists k mem',
                s V_MEM32 = mem' /\
                s R_A0 = neg ctl /\
                s R_A1 = dst ⊕ k /\
                s R_A2 = src ⊕ k /\
                s R_A6 = dst ⊕ len /\
                k < len < 2^32 /\
                ~ overlap 32 src len dst len /\
                (ctl = 0 -> mem_equal base_mem (s V_MEM32)) /\
                (ctl = 1 -> k_equal mem' src dst k)
            )
        | 0x90 | 0x94 => Post 0 (postcondition s)
        | _ => NoInv
        end.

    Definition br_ccopy : program := lift_riscv br_ccopy_ft.

    Definition exits0 := make_exits 0 br_ccopy invs.
    Definition invs0 := make_invs 0 br_ccopy invs.
End Invariants.

Lemma k_equal_inv : forall mem a b k,
    k_equal mem a b (1 + k) ->
    k_equal mem a b k.
Proof.
    intros. unfold k_equal in *.
    intros. apply H. lia.
Qed.

Lemma k_equal_step : forall mem a b k,
    k_equal mem a b k ->
    mem Ⓑ[a + k] = mem Ⓑ[b + k] ->
    k_equal mem a b (1 + k).
Proof.
    intros. unfold k_equal in *.
    intros. assert (i = k \/ i < k) by lia. destruct H2.
        subst. assumption.
    now apply H.
Qed.

Lemma noverlap_single : forall a b w,
    a <> b ->
    a < 2^w ->
    b < 2^w ->
    ~ overlap w a 1 b 1.
Proof.
    intros a b w Neq ALt BLt (i & j & I1 & J1 & Contra).
    replace i with 0 in * by lia.
    replace j with 0 in * by lia. psimpl in Contra.
    rewrite N.shiftl_1_l, N.mod_small, N.mod_small in Contra by lia.
    contradiction.
Qed.

Lemma noverlap_single_lt : forall p a b,
    a < b < 2^32 ->
    ~ overlap 32 (p + a) 1 (p + b) 1.
Proof.
    intros.
    apply noverlap_sum. psimpl.
    repeat rewrite msub_nowrap; psimpl;
    repeat rewrite N.mod_small by lia.
    all: lia.
Qed.

Theorem setmem_getmem:
  forall m a w en len,
  setmem w en len m a (getmem w en len m a) = m.
Proof.
  symmetry.
  rewrite <- (recompose_bytes (2^w*8) m) at 1.
  rewrite <- (recompose_bytes (2^w*8) (setmem _ _ _ _ _ _)).
  apply f_equal2; [|rewrite setmem_highbits; reflexivity].
  change (2^(2^w*8)) with (memsize w).
  apply byte_equivalent. symmetry.
  destruct (N.le_gt_cases len (msub w a0 a)) as [H|H].
    apply setmem_frame, H.

  assert (IN1: msub w (N.pred len) (msub w a0 a) < len).
    destruct (N.le_gt_cases (2^w) len).
      eapply N.lt_le_trans. apply msub_lt. assumption.
      rewrite msub_nowrap.
        eapply N.le_lt_trans. apply N.le_sub_l. eapply N.le_lt_trans. apply mp2_mod_le.
          apply N.lt_pred_l. intro H'. subst len. eapply N.nlt_0_r, H.
        rewrite msub_mod_pow2, N.min_id, N.mod_small.
          apply N.lt_le_pred, H.
          eapply N.le_lt_trans. apply N.le_pred_l. assumption.

  rewrite <- getbyte_mod_l, <- (add_msub w a a0), getbyte_mod_l.
  rewrite setmem_byte_anylen by assumption.
  set (i := match en with BigE => _ | _ => _ end).
  rewrite shiftr_getmem, (getmem_mod w en 1), <- (getmem_1 w en).
  rewrite <- (getmem_mod_l w en 1 m a0), <- getmem_mod_l.
  apply f_equal5; try reflexivity.

    apply N.min_r, N.neq_0_le_1, N.sub_gt. subst i. destruct en. apply IN1.
    rewrite <- N.shiftr_div_pow2, <- N.shiftl_mul_pow2, <- N.ldiff_ones_r.
    eapply N.le_lt_trans. apply N.add_le_mono_l, N.ldiff_le_l.
    rewrite <- N.sub_pred_l, N.add_sub_assoc.
      rewrite N.add_comm, N.add_sub. apply N.lt_pred_l. intro H'. subst len. eapply N.nlt_0_r, H.
      apply N.lt_le_pred, H.

    subst i. destruct en.

      rewrite <- N.sub_add_distr, <- mp2_add_r, <- msub_sub by
        (rewrite N.add_1_r; apply N.le_succ_l, IN1).
      rewrite <- (msub_mod_r w w len) by reflexivity.
      rewrite <- add_msub_swap, N.add_1_r, N.succ_pred_pos by
        (eapply N.le_lt_trans; [ apply N.le_0_l | apply H ]).
      rewrite msub_msub_distr, msub_diag, N.add_0_l, msub_mod_pow2, N.min_id, add_msub.
      reflexivity.

      rewrite N.add_assoc, <- mp2_add_r, mp2_mod_mul, N.add_0_r.
      apply add_msub.
Qed.

(* Proof in fault-free context *)
Theorem br_ccopy_correctness:
  forall s mem t xs' ctl src dst len
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = ctl)
         (A1: s R_A1 = dst)
         (A2: s R_A2 = src)
         (LEN: s R_A3 = len)
         (NOV: ~ overlap 32 src len dst len),
  satisfies_all br_ccopy (invs0 ctl dst src len mem mem)
                         (exits0 ctl dst src len mem mem) (xs'::t).
Proof using.
    Local Ltac step := time r5_step.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. repeat split; assumption.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s. rename a1 into a.

    destruct_inv 32 PRE.

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & A3 & Mem & BMem & Nov). {
    repeat step.
    (* len = 0, exit *)
    split.
        intros. now rewrite Mem.
        intros. unfold k_equal. lia.
    discriminate.
    (* len <> 0, loop *)
    exists 0; eexists; psimpl; repeat split; unfold k_equal; try lia.
    apply (models_var R_A3) in MDL. rewrite <- A3. apply MDL.
    assumption.
    intro. subst. unfold mem_equal. reflexivity.
    }

    (* Loop *)
    destruct PRE as (k & mem' & Mem & A0 & A1 & A2 & A6 & Bound & Nov & Same & Eq). {
    repeat step.
    - (* dst + k + 1 <> dst + len, loop *)
        exists (k + 1). eexists. psimpl. repeat split; try lia.
        assumption.
        intro. subst ctl.
            unfold mem_equal. intros. cbv [neg]. psimpl. subst.
            rewrite setmem_getmem. now apply Same.
        intro. subst ctl.
        cbv [neg]. psimpl.
        rewrite N.lxor_comm, <- N.lxor_assoc, N.lxor_nilpotent.
        psimpl.
        apply k_equal_step.
            unfold k_equal. intros.
            rewrite getmem_noverlap, getmem_noverlap. now apply Eq.
            apply noverlap_single_lt. lia.
            apply noverlap_shrink with (a1 := src) (len1 := len).
                psimpl. rewrite N.mod_small by lia. lia.
            apply noverlap_symmetry, noverlap_shrink with (a1 := dst) (len1 := len).
                psimpl. rewrite N.mod_small by lia. lia.
            now apply noverlap_symmetry.
            psimpl. rewrite getmem_noverlap. reflexivity.
            apply noverlap_shrink with (a1 := src) (len1 := len).
                psimpl. rewrite N.mod_small by lia. lia.
            apply noverlap_symmetry, noverlap_shrink with (a1 := dst) (len1 := len).
                psimpl. rewrite N.mod_small by lia. lia.
            now apply noverlap_symmetry.
    - discriminate.
    - (* dst + k + 1 = dst + len, return *)
        replace len with (k + 1) in * by lia. split.
        intro. subst ctl.
            unfold mem_equal. intros. cbv [neg]. psimpl. subst.
            rewrite setmem_getmem. now apply Same.
        intro. subst ctl.
        cbv [neg]. psimpl.
        rewrite N.lxor_comm, <- N.lxor_assoc, N.lxor_nilpotent.
        psimpl.
        apply k_equal_step.
            unfold k_equal. intros.
            rewrite getmem_noverlap, getmem_noverlap.
                symmetry. now apply Eq.
            apply noverlap_shrink with (a1 := src) (len1 := k + 1).
                psimpl. rewrite N.mod_small by lia. lia.
            apply noverlap_symmetry, noverlap_shrink with (a1 := dst) (len1 := k + 1).
                psimpl. rewrite N.mod_small by lia. lia.
            now apply noverlap_symmetry.
            apply noverlap_single_lt. lia.
            psimpl. rewrite getmem_noverlap. reflexivity.
            apply noverlap_shrink with (a1 := src) (len1 := k + 1).
                psimpl. rewrite N.mod_small by lia. lia.
            apply noverlap_symmetry, noverlap_shrink with (a1 := dst) (len1 := k + 1).
                psimpl. rewrite N.mod_small by lia. lia.
            now apply noverlap_symmetry.
    }
Qed.

Module FaultModel <: FaultModel RISCVArch IL_RISCV FTC.
    Import FTC.
    Definition fault_spacing := 0.
    Theorem fault_spacing_small : fault_spacing < 2^w.
    Proof. apply mp2_gt_0. Qed.

    Definition max_faults := 1.
End FaultModel.
Module FT := RVFaultTolerance FaultModel.
Import FT.

Section FaultTolerantInvariants.
    Variable ctl : N.
    Variable dst src : addr.
    Variable len : N.
    Variable base_mem mem : memory.

    Definition ft_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0 (
                s R_A0 = ctl /\ s R_A1 = dst /\ s R_A2 = src /\ s R_A3 = len /\
                s V_MEM32 = mem /\
                s V_MEM32 = base_mem /\
                ~ overlap 32 src len dst len /\
                fault_assumptions s
            )
        | 0x20 => Inv 0 (exists k mem',
                s V_MEM32 = mem' /\
                s R_A0 = neg ctl /\
                s R_A1 = dst ⊕ k /\
                s R_A2 = src ⊕ k /\
                s R_A6 = dst ⊕ len /\
                k < len < 2^32 /\
                ~ overlap 32 src len dst len /\
                (ctl = 0 -> mem_equal base_mem (s V_MEM32)) /\
                (ctl = 1 -> k_equal mem' src dst k) /\
                fault_invs s
            )
        | 0x90 | 0x94 => Post 0 (postcondition ctl dst src len base_mem s)
        | _ => NoInv
        end.

    Definition br_ccopy_fault : program := inject_skip br_ccopy.

    Definition ft_exits0 := make_exits 0 br_ccopy_fault ft_invs.
    Definition ft_invs0 := make_invs 0 br_ccopy_fault ft_invs.
End FaultTolerantInvariants.

Lemma le_impl_eq_or_le :
    forall x y,
        x <= y ->
        x = y \/ x <= y - 1.
Proof. lia. Qed.

(* Proof in single-fault context *)
Theorem br_ccopy_ft_correctness:
  forall s mem t xs' ctl src dst len
         (ENTRY: startof t xs' = (Addr 0, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = ctl)
         (A1: s R_A1 = dst)
         (A2: s R_A2 = src)
         (LEN: s R_A3 = len)
         (NOV: ~ overlap 32 src len dst len)
         (FAULT: fault_assumptions s),
  satisfies_all br_ccopy_fault (ft_invs0 ctl dst src len mem mem)
                               (ft_exits0 ctl dst src len mem mem) (xs'::t).
Proof using.

    Ltac process_faults :=
        lazymatch goal with
        | [s : store, FAULT: fault_assumptions ?s |-
                nextinv _ _ _ _ ((Addr 0, ?s) :: _)] =>
            destruct FAULT as (FC & FT);
            unfold FTC.fault_counter, FaultModel.max_faults in FC;
            unfold FTC.fault_timer in FT;
            match type of FC with
            | s ?v = ?n =>
                replace s with (update s v n) by
                    now erewrite store_upd_eq
            end;
            match type of FT with
            | s ?v = ?n =>
                replace s with (update s v n) by
                    now erewrite store_upd_eq
            end
        | [s : store, FAULT: fault_invs ?s |-
                    nextinv _ _ _ _ _] =>
                unfold fault_invs in FAULT;
                unfold FTC.fault_counter, FaultModel.max_faults in FAULT;
                repeat (lazymatch goal with
                        | [H: ?x <= 0 |- _] => apply N.le_0_r in H
                        | [H: ?x <= ?y |- _] =>
                            let EQ := fresh "EQ" in
                            let LE := fresh "LE" in
                            destruct (le_impl_eq_or_le _ _ H) as [EQ|LE];
                                clear H;
                                [|psimpl in LE]
                        end)
        end.

    Ltac clean_fault_goals :=
        repeat match goal with
        | [n : N, BC : ?n mod 2 = 0 |- _] => clear BC n
        | [n : N, BC : ?n mod 2 = N.pos ?p |- _] => clear BC n p
        | [s' : store, n : N, 
            BC : (if 0 <? ?s' V_FC then ?n mod 2 else 0) = _ |- _] => clear BC n
        | [H: ?x = ?x |- _] => clear H
        end;
        try discriminate.

    Ltac fault_step arch_step := 
        (try process_faults);
        time arch_step;
        clean_fault_goals.

    Ltac step ::= fault_step r5_step.

    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. now repeat (split; [assumption|]).

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply inject_skip_lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s. rename a1 into a.

    destruct_inv 32 PRE.

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & A3 & Mem & BMem & Nov & FC). {
    repeat step.
    par: match goal with
        | [|- exists _ _, _] =>
            exists 0; eexists; psimpl;
            repeat (split; [easy|]);
            split;
                [apply (models_var R_A3) in MDL;
                rewrite <- A3; simpl in MDL; lia|];
            split; [assumption|];
            split; [intro; subst; now unfold mem_equal|split];
            [intro; subst; unfold k_equal; lia
            |unfold fault_invs, FaultModel.max_faults; now psimpl]
        | [|- (_ -> _) /\ (_ -> _)] => 
            split; 
                [intro; subst; now unfold mem_equal
                |intro; unfold k_equal; lia]
        end.
    }

    (* Loop *)
    destruct PRE as (k & mem' & Mem & A0 & A1 & A2 & A6 & Bound & Nov & Same & Eq & FAULT). {
    Local Ltac solve_inv ctl dst src len k Eq Same :=
        exists (k + 1); eexists; psimpl; repeat split; try lia;
        try (unfold fault_invs, FaultModel.max_faults; now psimpl);
        [intro; subst ctl; unfold mem_equal; intros;
            cbv [neg]; psimpl; subst;
            rewrite setmem_getmem; now apply Same
        |intro; subst ctl; cbv [neg]; psimpl;
        rewrite N.lxor_comm, <- N.lxor_assoc, N.lxor_nilpotent;
        apply k_equal_step; unfold k_equal; intros; psimpl;
        repeat rewrite getmem_noverlap;
        match goal with
        | [|- _ = _] => auto; now apply Eq
        | [|- ~ overlap _ _ _ _ _] =>
            (apply noverlap_single_lt; lia) ||
            (apply (noverlap_shrink _ src len);
            [psimpl; rewrite N.mod_small by lia; lia
            |apply noverlap_symmetry, (noverlap_shrink _ dst len);
                [psimpl; lia|now apply noverlap_symmetry]])
        | _ => idtac
        end].
    Local Ltac solve_post ctl dst src len k Eq Same :=
        solve [let i := fresh "i" in
        let ILen := fresh "ILen" in
        replace len with (k + 1) in * by lia; split;
        [intros; subst ctl; unfold mem_equal; intros; cbv [neg];
         psimpl; subst; rewrite setmem_getmem; now apply Same
        |intros; subst ctl; cbv [neg]; psimpl;
        rewrite N.lxor_comm, <- N.lxor_assoc, N.lxor_nilpotent;
        psimpl; apply k_equal_step;
        [unfold k_equal; intros;
        repeat rewrite getmem_noverlap; 
        [symmetry;now apply Eq|
        apply (noverlap_shrink _ src (k + 1));
        [psimpl; lia|
        apply noverlap_symmetry, (noverlap_shrink _ dst (k + 1));
        [psimpl; lia|now apply noverlap_symmetry]]|
        apply noverlap_single_lt; lia]
        |psimpl;rewrite getmem_noverlap; auto;
        apply (noverlap_shrink _ src (k + 1));
        [psimpl; lia|
        apply noverlap_symmetry, (noverlap_shrink _ dst (k + 1));
        [psimpl; lia|now apply noverlap_symmetry]]]]].
    repeat (step;
            (* Get to end of already-faulted branches *) 
            lazymatch goal with
            | [|- context[update _ V_FC 0]] => repeat step;
                lazymatch goal with
                | [|- exists _, _] => solve_inv ctl dst src len k Eq Same
                | [|- (_ -> _) /\ (_ -> _)] => solve_post ctl dst src len k Eq Same
                end
            | [|- nextinv _ _ _ _ _] => idtac
            end).
    step. solve_inv ctl dst src len k Eq Same.
    step; solve_post ctl dst src len k Eq Same.
    step. solve_inv ctl dst src len k Eq Same.
    solve_post ctl dst src len k Eq Same.
    }
Qed.

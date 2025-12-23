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
    Variable mem : memory.

    Definition k_equal (mem : memory) (p1 p2 : addr) (k : N) : Prop :=
        forall (i : N),
            i < k ->
            mem Ⓑ[p1 + i] = mem Ⓑ[p2 + i].

    Definition postcondition (s : store) : Prop :=
        ctl = 1 ->
        k_equal (s V_MEM32) dst src len.

    Definition neg (n : N) : N := 0 ⊖ n.

    Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0 (
                s R_A0 = ctl /\ s R_A1 = dst /\ s R_A2 = src /\ s R_A3 = len /\
                s V_MEM32 = mem /\
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

Lemma noverlap_single_lt : forall p a b,
    a < b < 2^32 ->
    ~ overlap 32 (p + a) 1 (p + b) 1.
Proof.
    intros. apply noverlap_sum. psimpl.
    repeat rewrite msub_nowrap; psimpl;
    repeat rewrite N.mod_small by lia.
    all: lia.
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
  satisfies_all br_ccopy (invs0 ctl dst src len mem)
                         (exits0 ctl dst src len mem) (xs'::t).
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
    destruct PRE as (A0 & A1 & A2 & A3 & Mem & Nov). {
    repeat step.
    (* len = 0, exit *)
    1-2: intro; unfold k_equal; lia.
    (* len <> 0, loop *)
    exists 0; eexists; psimpl; repeat split; unfold k_equal; try lia.
    apply (models_var R_A3) in MDL. rewrite <- A3. apply MDL.
    assumption.
    }

    (* Loop *)
    destruct PRE as (k & mem' & Mem & A0 & A1 & A2 & A6 & Bound & Nov & Eq). {
    repeat step.
    - (* dst + k + 1 <> dst + len, loop *)
        exists (k + 1). eexists. psimpl. repeat split; try lia.
        assumption.
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
        replace len with (k + 1) in * by lia.
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

Section FaultTolerantInvariants.
    Variable ctl : N.
    Variable dst src : addr.
    Variable len : N.
    Variable mem : memory.

    Definition ft_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        | 0x0 => Inv 0 (
                s R_A0 = ctl /\ s R_A1 = dst /\ s R_A2 = src /\ s R_A3 = len /\
                s V_MEM32 = mem /\
                ~ overlap 32 src len dst len /\
                s V_FC = 1
            )
        | 0x20 => Inv 0 (exists k mem',
                s V_MEM32 = mem' /\
                s R_A0 = neg ctl /\
                s R_A1 = dst ⊕ k /\
                s R_A2 = src ⊕ k /\
                s R_A6 = dst ⊕ len /\
                k < len < 2^32 /\
                ~ overlap 32 src len dst len /\
                (ctl = 1 -> k_equal mem' src dst k) /\
                s V_FC <= 1
            )
        | 0x90 | 0x94 => Post 0 (postcondition ctl dst src len s)
        | _ => NoInv
        end.

    Definition br_ccopy_fault : program := inject_fault br_ccopy.

    Definition ft_exits0 := make_exits 0 br_ccopy_fault ft_invs.
    Definition ft_invs0 := make_invs 0 br_ccopy_fault ft_invs.
End FaultTolerantInvariants.

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
         (FC: s V_FC = 1),
  satisfies_all br_ccopy_fault (ft_invs0 ctl dst src len mem)
                               (ft_exits0 ctl dst src len mem) (xs'::t).
Proof using.
    Local Ltac step ::= 
        match goal with
        | [s' : store, FC : ?s' V_FC <= 1 |- _] =>
            let H := fresh "H" in
            assert (s' V_FC = 0 \/ s' V_FC = 1) as H by lia;
            clear FC; destruct H
        | _ => idtac
        end;
        time r5_step;
        repeat match goal with
        | [n : N, BC : ?n mod 2 = _ |- _] => clear BC n
        | [s' : store, n : N, 
            BC : (if 0 <? ?s' V_FC then ?n mod 2 else 0) = _ |- _] => clear BC n
        | [H: ?x = ?x |- _] => clear H
        end;
        try discriminate.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. repeat split; assumption.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply inject_fault_lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s. rename a1 into a.

    destruct_inv 32 PRE.

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & A3 & Mem & Nov & FC). {
    repeat step.
    all: match goal with
        | [|- _ -> _] => intro; unfold k_equal; lia
        | _ => exists 0; eexists; psimpl; repeat split; unfold k_equal; try lia;
            [apply (models_var R_A3) in MDL; rewrite <- A3; apply MDL
            |assumption]
        end.
    }

    (* Loop *)
    destruct PRE as (k & mem' & Mem & A0 & A1 & A2 & A6 & Bound & Nov & Eq & FC). {
    Local Ltac solve_inv ctl dst src len k Eq :=
        solve [exists (k + 1); eexists; psimpl; repeat split; try lia;
        [assumption|];
        intro; subst ctl; cbv [neg]; psimpl;
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
    Local Ltac solve_post ctl dst src len k Eq :=
        solve [let i := fresh "i" in
        let ILen := fresh "ILen" in
        replace len with (k + 1) in * by lia;
        intros; subst ctl; cbv [neg]; psimpl;
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
        [psimpl; lia|now apply noverlap_symmetry]]]].
    repeat (step;
            (* Get to end of already-faulted branches *) 
            lazymatch goal with
            | [|- context[update _ V_FC 0]] => repeat step;
                lazymatch goal with
                | [|- exists _, _] => solve_inv ctl dst src len k Eq
                | [|- _ -> _] => solve_post ctl dst src len k Eq
                end
            | [|- nextinv _ _ _ _ _] => idtac
            end).
    step. solve_inv ctl dst src len k Eq.
    step; solve_post ctl dst src len k Eq.
    step. solve_inv ctl dst src len k Eq.
    solve_post ctl dst src len k Eq.
    }
Qed.

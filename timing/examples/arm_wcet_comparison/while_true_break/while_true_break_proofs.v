From Picinae.timing.examples.arm_wcet_comparison.while_true_break Require Import while_true_break_lifted.
Require Import ARMv6MTiming.
Import ARMv6MNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : ARMv6MCPUTimingBehavior).
Import cpu.

Module Program_while_true_break <: ProgramInformation.
    Definition entry_addr : N := 0x8000000.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x8000016 => true
        | _ => false
    end | _ => false end.

    Definition binary := while_true_break_while_true_break_armv6m.
End Program_while_true_break.

Module ARMv6MTiming := ARMv6MTiming cpu Program_while_true_break.
Module while_true_breakAuto := ARMv6MTimingAutomation ARMv6MTiming.
Import Program_while_true_break while_true_breakAuto.

Definition time_of_while_true_break (n : N) (t : trace) :=
  cycle_count_of_trace t =
    tmovs_reg + tmuls + tlsls_imm + tcmp_reg +
    if (n * n <=? n + n) then tb_taken + tbx else (
        tb_not_taken +
        (* loop iters that branch back *)
        (n - 3) * (
            tsubs_imm8 + tmovs_reg + tmuls + tlsls_imm + tcmp_reg + tb_taken
        ) +
        (* final loop iter, which falls through to the return *)
        tsubs_imm8 + tmovs_reg + tmuls + tlsls_imm + tcmp_reg + tb_not_taken +
        tbx
    ).

Definition while_true_break_timing_invs (n : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000000 => Some (
    s R_R0 = n /\ 0 <= n < 1000 /\
    cycle_count_of_trace t' = 0
  )
| 0x800000a => Some (
    3 <= n < 1000 /\
    3 <= s R_R0 <= n /\
    n * n <=? n + n = false /\
    cycle_count_of_trace t' =
        tmovs_reg + tmuls + tlsls_imm + tcmp_reg + tb_not_taken +
        (* loop iters *)
        (n - s R_R0) * (
            tsubs_imm8 + tmovs_reg + tmuls + tlsls_imm + tcmp_reg + tb_taken
        )
  )
| 0x8000016 => Some (time_of_while_true_break n t)
| _ => None end | _ => None end.

Lemma Contra : forall n,
    n * n <= n + n -> n <= 2.
Proof.
    induction n using N.peano_ind; intros.
        lia.
    lia.
Qed.

(* Turn a branch condition over the APSR flags into (in)equalities. *)
Ltac flag_cases H :=
    repeat match type of H with context [ if ?b then _ else _ ] =>
        let E := fresh "E" in destruct b eqn:E
    end;
    cbn in H; try discriminate H;
    repeat match goal with
    | [ E: (_ <=? _) = true |- _ ] => apply N.leb_le in E
    | [ E: (_ <=? _) = false |- _ ] => apply N.leb_gt in E
    | [ E: (_ =? _) = true |- _ ] => apply N.eqb_eq in E
    | [ E: (_ =? _) = false |- _ ] => apply N.eqb_neq in E
    end.

(* Derive (in)equalities from a copy of branch condition BC, leaving BC itself
   for hammer to time the branch with. *)
Ltac branch_fact BC :=
    let F := fresh "F" in pose proof BC as F;
    rewrite N.shiftl_mul_pow2, N.mod_small, N.mod_small in F by lia;
    change (2^1) with 2 in F; flag_cases F; lia.

Ltac loop_fact BC M1 M2 :=
    let F := fresh "F" in pose proof BC as F;
    rewrite M1, M2, N.shiftl_mul_pow2, N.mod_small in F by lia;
    change (2^1) with 2 in F; flag_cases F; nia.

Theorem while_true_break_timing:
  forall s t s' x' n
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models armv6mtypctx s)
         (* bindings *)
         (R0: s R_R0 = n)
         (R0B: 0 <= n < 1000),
  satisfies_all
    lifted_prog
    (while_true_break_timing_invs n)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep armv6m_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto; lia.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped_lift_armv6m].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    - destruct PRE as (R0 & Bounds & Cycles).
        assert (SQ: n * n < 2^32). {
            change (2^32) with (2^16 * 2^16).
            rewrite <- N.square_lt_mono. lia.
        }
        repeat step.
        -- (* loop entry: n * n > n + n *)
            assert (n + n < n * n) by branch_fact BC.
            assert (3 <= n) by nia.
            split. lia.
            split. lia.
            split. apply N.leb_gt. lia.
            hammer.
        -- (* immediate exit: n * n <= n + n *)
            assert (n * n <= n + n) by branch_fact BC.
            replace (n * n <=? n + n) with true by (symmetry; apply N.leb_le; lia).
            hammer.
    - destruct PRE as (NBounds & Bounds & Path & Cycles).
        assert (M1: s' R_R0 ⊖ 1 = s' R_R0 - 1).
            rewrite msub_nowrap by (psimpl; lia). psimpl. lia.
        assert (M2: msub 31 (s' R_R0) 1 = s' R_R0 - 1).
            rewrite msub_nowrap by (psimpl; lia). psimpl. lia.
        assert (SQ: (s' R_R0 - 1) * (s' R_R0 - 1) < 2^32). {
            change (2^32) with (2^16 * 2^16).
            rewrite <- N.square_lt_mono. lia.
        }
        repeat step.
        -- (* loop exit: (s' R_R0 - 1)^2 <= 2 (s' R_R0 - 1), so s' R_R0 = 3 *)
            assert (s' R_R0 = 3) by loop_fact BC M1 M2.
            rewrite Path.
            hammer.
        -- (* loop continues *)
            assert (3 <= s' R_R0 - 1) by loop_fact BC M1 M2.
            split. assumption.
            split. rewrite M1. lia.
            split. assumption.
            hammer.
            rewrite ?M1.
            replace (n - (s' R_R0 - 1)) with (1 + (n - s' R_R0)) by lia. lia.
Qed.

End TimingProof.

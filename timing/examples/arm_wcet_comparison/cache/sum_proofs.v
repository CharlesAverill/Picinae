From Picinae.timing.examples.arm_wcet_comparison.cache Require Import sum_lifted.
Require Import ARMv6MTiming.
Import ARMv6MNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : ARMv6MCPUTimingBehavior).
Import cpu.

Module Program_sum <: ProgramInformation.
    Definition entry_addr : N := 0x8000000.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x8000014 => true
        | _ => false
    end | _ => false end.

    Definition binary := cache_sum_armv6m.
End Program_sum.

Module ARMv6MTiming := ARMv6MTiming cpu Program_sum.
Module sumAuto := ARMv6MTimingAutomation ARMv6MTiming.
Import Program_sum sumAuto.

Definition time_of_sum (size : N) (t : trace) :=
  cycle_count_of_trace t =
    tcmp_imm +
    if size =? 0 then (
        tb_taken + tmovs_imm + tb + tbx
    ) else (
        tb_not_taken + tlsls_imm + tmovs_reg + tadds_3reg + tmovs_imm +
        (* loop iters that branch back *)
        (size - 1) * (
            (tldm_base + 1) + tadds_3reg + tcmp_reg + tb_taken
        ) +
        (* final loop iter, which falls through to the return *)
        (tldm_base + 1) + tadds_3reg + tcmp_reg + tb_not_taken +
        tbx
    ).

Definition sum_timing_invs (arr : addr) (size : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000000 => Some (
    s R_R0 = arr /\ s R_R1 = size /\ 0 <= size < 1000 /\
    cycle_count_of_trace t' = 0
  )
| 0x800000c => Some (exists i,
    s R_R3 = arr ⊕ 4 * i /\ s R_R1 = arr ⊕ 4 * size /\
    size =? 0 = false /\
    i < size < 1000 /\
    cycle_count_of_trace t' =
        tcmp_imm + tb_not_taken + tlsls_imm + tmovs_reg + tadds_3reg + tmovs_imm +
        i * (
            (tldm_base + 1) + tadds_3reg + tcmp_reg + tb_taken
        )
  )
| 0x8000014 => Some (time_of_sum size t)
| _ => None end | _ => None end.

Theorem sum_timing:
  forall s t s' x' arr size
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models armv6mtypctx s)
         (* bindings *)
         (R0: s R_R0 = arr)
         (R1: s R_R1 = size)
         (SIZE: 0 <= size < 1000),
  satisfies_all
    lifted_prog
    (sum_timing_invs arr size)
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
    - destruct PRE as (R0 & R1 & Bounds & Cycles).
        repeat step.
        -- (* size = 0: straight to the return *)
            hammer.
        -- (* loop entry *)
            exists 0. repeat split; psimpl; try lia.
            hammer.
    - destruct PRE as (i & R3 & R1 & Path & ISize & Cycles).
        repeat step.
        -- (* last iteration: i + 1 = size *)
            apply N.eqb_eq in BC. rewrite !N.mod_small in BC by lia.
            hammer.
            replace size with (i + 1) in * by lia.
            lia.
        -- (* loop continues *)
            apply N.eqb_neq in BC. rewrite !N.mod_small in BC by lia.
            exists (1 + i). split.
                rewrite N.mul_add_distr_l. psimpl. reflexivity.
            split. reflexivity. split. assumption. split. lia.
            hammer.
Qed.

End TimingProof.

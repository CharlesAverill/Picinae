Require Import ct_swap.
(* Require Import mod_add_same_r. *)
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_ct_swap <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x1f4 => true
        | _ => false
        end | _ => false end.

    Definition binary := ct_swap.
End Program_ct_swap.

Module RISCVTiming := RISCVTiming cpu Program_ct_swap.
Module ct_swapAuto := RISCVTimingAutomation RISCVTiming.
Import Program_ct_swap ct_swapAuto.

Definition postcondition (t : trace) (len : N) :=
    cycle_count_of_trace t =
        tslli 0x2 + tsub + tadd +
        len * (
            ttbne + 2 * tlw + 2 * taddi +
            txor + tand + txor +
            tsw + tlw + txor +
            tsw + tjal
        ) + tfbne + tjalr.

Definition ct_swap_timing_invs (b : addr) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (
        s R_A2 = b /\ s R_A3 = len /\
        (* array fits in memory *)
        4 * len < 2^32 /\
        cycle_count_of_trace t' = 0)
| 0x1f0 => Some (
        exists i, s R_A2 = b ⊕ (4 * i) /\ s R_A3 = b ⊕ (len << 2) /\
        i <= len /\
        4 * len < 2^32 /\
        cycle_count_of_trace t' =
            tslli 0x2 + tsub + tadd +
            i * (
                ttbne + 2 * tlw + 2 * taddi +
                txor + tand + txor +
                tsw + tlw + txor +
                tsw + tjal
            ) 
    )
| 0x1f4 => Some (postcondition t len)
| _ => None
end | _ => None end.

Theorem ct_swap_timing:
  forall s (t : trace) s' x' len b
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (ALIGNED: exists k', b = 4 * k')
         (LEN: 4 * len < 2^32)
         (A2: s R_A2 = b)
         (A3: s R_A3 = len),
  satisfies_all 
    lifted_prog
    (ct_swap_timing_invs b len)
 exits
  ((x',s')::t).
Proof.
    intros. apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. now step.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (A2 & A3 & LEN & Cycles).
        repeat step. exists 0. psimpl; repeat split; auto. lia.
        hammer.

    destruct PRE as (i & A2 & A3 & ILEN & LEN & Cycles).
        repeat step. {
            exists (1 + i).
            psimpl; repeat split; auto.
                rewrite N.mul_add_distr_l. now psimpl.
                assert (forall n m, n <= m -> n=m \/ n < m) by lia.
                apply H in ILEN. destruct ILEN. subst.
                    change (len << 2) with (4 * len) in BC.
                    rewrite N.eqb_refl in BC. inversion BC.
                    lia.
            hammer.
        }

        (* simplify BC to solve ccot goal *)
        rewrite <- A2, <- A3 in BC.
        apply Bool.negb_false_iff, N.eqb_eq in BC.
        rewrite BC in A2. rewrite A3 in A2.
        change (len << 2) with (4 * len) in *.
        replace len with i in *. hammer.
            rewrite N.eqb_refl. hammer. lia.
Qed.

Require Import ct_swap.
Require Import mod_add_same_r.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

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

(* Postcondition *)
Definition time_of_ct_swap (len : N) (t : trace) :=
    cycle_count_of_trace t = 
        (* Function entry *)
        tslli 2 + tsub + tadd + 
        (* Loop *)
        len *
        ((ttbne + tlw + tlw + taddi + taddi + txor + tand + txor + tsw + tlw + txor + tsw + tjal)) +
        (* Loop exit and function return *)
        tfbne + tjalr.

Definition ct_swap_timing_invs (len : N) (base_addr_b : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (
        (4 * len < 2^32) /\
        (* The pointer to uint32_t array b is a multiple of 4. *)
        (exists k', base_addr_b = 4 * k') /\
        (s R_A3 = len) /\
        (s R_A2 = base_addr_b) /\
        (cycle_count_of_trace t' = 0)
    )
| 0x1f0 => Some (
        (4 * len < 2^32) /\
        (* The pointer to uint32_t array b is a multiple of 4.  *)
        (exists k', base_addr_b = 4 * k') /\
        (* Pointer b is incremented by 4 until it reaches the value in R_A3 *)
        (s R_A3 = (base_addr_b ⊕ (4 * len))) /\
        (* The pointer in R_A2 is the base pointer of b modulo plus the offset index * 4. *)
        (exists index, 
            (index <= len) /\
            (s R_A2 = base_addr_b ⊕ (4 * index)) /\  
            (cycle_count_of_trace t' =
                tslli 2 + tsub + tadd + 
                (* array loop iteration *)
                (index *
                    (ttbne + tlw + tlw + taddi + taddi + txor + tand + txor + tsw + tlw + txor + tsw + tjal)
                )
            )
        )
    )
| 0x1f4 => Some (
        time_of_ct_swap len t
    )
| _ => None end | _ => None end.


Theorem ct_swap_timing:
  forall s (t : trace) s' x' len base_addr_b
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (PTR_ALIGN: exists k', base_addr_b = 4 * k')
         (LEN_VALID: 4 * len < 2^32)
         (A3: s R_A3 = len)
         (A2: s R_A2 = base_addr_b),
  satisfies_all 
    lifted_prog
    (ct_swap_timing_invs len base_addr_b)
 exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. 
    now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (LEN_VALID & PTR_ALIGN & A3 & A2 & init).
    repeat step.
        split.
            assumption.
        split.
            assumption.
        split.
            rewrite N.shiftl_mul_pow2.
            psimpl.
            rewrite N.mul_comm.
            reflexivity.
        (* 0 loop iterations *)
        exists 0.
            split.
                lia.
        split.
        (* Pointer to b has not changed *)
            change (4 * 0) with 0.
            rewrite N.mod_small.
            rewrite N.add_0_r.
            reflexivity.
            pose proof (models_var R_A2 MDL).
            simpl in H.
            lia.
        hammer.

    destruct PRE as (LEN_VALID & PTR_ALIGN & FINAL_PTR & INDEX & INDEX_VALID & MOVING_PTR & CCOT).
    repeat step.
        split.
            assumption.
        split.
            assumption.
        split.
            reflexivity.
        (* 1 + INDEX loop iterations *)
        exists (1 + INDEX).
            split.
                assert (forall n m, n <= m -> n=m \/ n < m).
                lia.
                apply H in INDEX_VALID.
                destruct INDEX_VALID as [eq | lt].
                    (* INDEX != len because of branch condition *)
                    rewrite eq in BC.
                    rewrite N.eqb_refl in BC.
                    discriminate.
                    lia.
            split.
                lia.
        hammer.

    (* Postcondition *)
    hammer.
    (* INDEX = len *)
    replace INDEX with len.
        lia.
        lia.
Qed.

End TimingProof.

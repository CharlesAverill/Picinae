(* This routine has nested loops with a comparison in the inner one, 
   this makes it tough to reason about the runtime exactly unless we also
   reason about sortedness. 
   
   Instead of reasoning about exact runtime, this proof will give
   - an exact lower bound, and
   - an extremely tight upper bound
   on the runtime of the function, by considering the max runtime out of
   the taken and untaken branches of the inner comparison.
*)

Require Import bubble_sort.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_bubble_sort_theta_n2 <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x220 => true
        | _ => false
    end | _ => false end.

    Definition binary := bubble_sort.
End Program_bubble_sort_theta_n2.

Module RISCVTiming := RISCVTiming cpu Program_bubble_sort_theta_n2.
Module bubble_sort_theta_n2Auto := RISCVTimingAutomation RISCVTiming.
Import Program_bubble_sort_theta_n2 bubble_sort_theta_n2Auto.

Definition time_of_bubble_sort_theta_n2
        (len : N) (t : trace) :=
    (* ----------------------------------------- *)
    (* lower bound *)
    tslli 2 + tadd + taddi +
    (* outer loop full iterations *)
    len * (
        tfbeq + taddi + tjal +
        (* inner loop full iterations *)
        (len - 1) * (
            ttbne +
            tlw + tlw +
            N.min ttbgeu (tfbgeu + tsw + tsw) +
            taddi
        ) +
        (* inner loop partial iteration *)
        tfbne +
        taddi + tjal
    ) +
    (* outer loop partial iteration *)
    ttbeq +
    (* return *)
    tjalr <=
    (* ----------------------------------------- *)
    cycle_count_of_trace t <=
    (* ----------------------------------------- *)
    (* upper bound *)
    tslli 2 + tadd + taddi +
    (* outer loop full iterations *)
    len * (
        tfbeq + taddi + tjal +
        (* inner loop full iterations *)
        (len - 1) * (
            ttbne +
            tlw + tlw +
            N.max ttbgeu (tfbgeu + tsw + tsw) +
            taddi
        ) +
        (* inner loop partial iteration *)
        tfbne +
        taddi + tjal
    ) +
    (* outer loop partial iteration *)
    ttbeq +
    (* return *)
    tjalr.

Definition bubble_sort_theta_n2_timing_invs (s : store) (base_mem : memory)
    (arr : addr) (len : N) (_a5 : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (s V_MEM32 = base_mem /\ 
                    s R_A0 = arr /\ s R_A1 = len /\
                    s R_A5 = _a5 /\
                    arr + 4 * len < 2^32 /\
                    cycle_count_of_trace t' = 0)
| 0x1f0 => Some (exists mem a4, s V_MEM32 = mem /\
                   s R_A0 = arr /\ s R_A1 = len /\
                   s R_A3 = (arr + 4 * len) /\
                   (* a4 is outer loop counter *)
                   s R_A4 = a4 /\
                   a4 <= len /\
                   arr + 4 * len < 2^32 /\
                   tslli 2 + tadd + taddi +
                   a4 * (
                       tfbeq + taddi + tjal +
                       (len - 1) * (
                           ttbne +
                            tlw + tlw +
                            N.min ttbgeu (tfbgeu + tsw + tsw) +
                            taddi
                       ) +
                       (* inner loop partial iteration *)
                       tfbne +
                       taddi + tjal
                   ) <=
                   (* ----------------------------------------- *)
                   cycle_count_of_trace t' <=
                   (* ----------------------------------------- *)
                   tslli 2 + tadd + taddi +
                   a4 * (
                       tfbeq + taddi + tjal +
                       (len - 1) * (
                           ttbne +
                            tlw + tlw +
                            N.max ttbgeu (tfbgeu + tsw + tsw) +
                            taddi
                       ) +
                       (* inner loop partial iteration *)
                       tfbne +
                       taddi + tjal
                   )
            )
| 0x214 => Some (exists mem a4 inner_loop_count, s V_MEM32 = mem /\
                   s R_A0 = arr /\ s R_A1 = len /\
                   s R_A3 = (arr + 4 * len) /\
                   (* a4 is outer loop counter *)
                   s R_A4 = a4 /\
                   s R_A5 = (arr + 4 * (1 + inner_loop_count)) /\
                   1 + inner_loop_count <= len /\
                   (* this is here to handle the inductive case where 
                      inner_loop_count is incremented *)
                   ~ 1 + inner_loop_count > len /\
                   0 < len /\
                   a4 < len /\
                   arr + 4 * len < 2^32 /\
                   tslli 2 + tadd + taddi +
                   a4 * (
                       tfbeq + taddi + tjal +
                       (len - 1) * (
                           ttbne +
                            tlw + tlw +
                            N.min ttbgeu (tfbgeu + tsw + tsw) +
                            taddi
                       ) +
                       (* inner loop partial iteration *)
                       tfbne +
                       taddi + tjal
                   ) +
                   tfbeq + taddi + tjal +
                   (* number of inner loops so far *)
                   inner_loop_count * (
                        ttbne + tlw + tlw +
                        N.min ttbgeu (tfbgeu + tsw + tsw) +
                        taddi
                    ) <=
                   (* ----------------------------------------- *)
                   cycle_count_of_trace t' <=
                   (* ----------------------------------------- *)
                   tslli 2 + tadd + taddi +
                   a4 * (
                       tfbeq + taddi + tjal +
                       (len - 1) * (
                           ttbne +
                            tlw + tlw +
                            N.max ttbgeu (tfbgeu + tsw + tsw) +
                            taddi
                       ) +
                       (* inner loop partial iteration *)
                       tfbne +
                       taddi + tjal
                   ) +
                   tfbeq + taddi + tjal +
                   (* number of inner loops so far *)
                   inner_loop_count * (
                        ttbne + tlw + tlw +
                        N.max ttbgeu (tfbgeu + tsw + tsw) +
                        taddi
                    )
            )
| 0x220 => Some (time_of_bubble_sort_theta_n2 len t)
| _ => None end | _ => None end.

Theorem bubble_sort_theta_n2_timing:
  forall s t s' x' base_mem arr len a5
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = arr)
         (A2: s R_A1 = len)
         (A5: s R_A5 = a5)
         (* array must fit inside the address space without wrapping *)
         (* this shouldn't be necessary but makes the proof easy *)
         (ARR_VALID: arr + 4 * len < 2^32),
  satisfies_all 
    lifted_prog
    (bubble_sort_theta_n2_timing_invs s base_mem arr len a5)
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
    rename a5 into _a5.

    destruct_inv 32 PRE.

    (* 0x1e4 -> 0x1f0 *)
    destruct PRE as (MEM & A0 & A1 & A5 & ARR_VALID & Cycles). {
        repeat step. do 2 eexists. repeat split; eauto.
        now rewrite N.mod_small by assumption. lia.
        (* lower bound *)
        hammer.
        (* upper bound *)
        hammer.
    }

    (* 0x1f0 -> *)
    destruct PRE as (mem & a4 & MEM & A0 & A1 & A3 & A4 & A4_VALID & ARR_VALID &
        Cycles_low & Cycles_high).
    repeat step.
        (* a4 = len *)
        hammer.
        (* a4 <> len *)
        do 2 eexists; exists 0; repeat split; eauto.
        rewrite N.mod_small by (apply N.eqb_neq in BC; lia);
            now psimpl.
        1-4: apply N.eqb_neq in BC; lia.
        (* lower bound *)
        hammer.
        (* upper bound *)
        hammer.

    (* 0x101bc -> *)
    destruct PRE as (mem & a4 & inner_loop_count & MEM & A0 & A1 & A3 & A4
                     & A5 & ILC_LEN & ILC_LEN' & LEN_POS & A4_LEN & ARR_VALID 
                     & Cycles_low & Cycles_high).
    step.
        (* not at end of array, continue inner loop *)
        repeat step.
        (* arr[j-1] < arr[j] *)
        do 2 eexists; exists (1 + inner_loop_count); repeat split; eauto.
            repeat rewrite N.mul_add_distr_l. psimpl.
            rewrite N.mod_small. reflexivity.
            1-4: lia.
        hammer. hammer.
        (* arr[j-1 >= arr[j] *)
        do 2 eexists; exists (1 + inner_loop_count); repeat split; eauto.
            repeat rewrite N.mul_add_distr_l. psimpl.
            rewrite N.mod_small. reflexivity.
            1-4: apply Bool.negb_true_iff, N.eqb_neq in BC; lia.
        hammer. hammer.
        (* at end of array, exit inner loop -> outer loop invariant *)
        apply Bool.negb_false_iff, N.eqb_eq in BC; subst.
        repeat step.
        do 2 eexists. repeat split; eauto.
            rewrite N.mod_small; lia.
        rewrite N.mod_small by lia.
        hammer.
        replace (s' R_A1) with (1 + inner_loop_count) by lia.
        rewrite N.mod_small by lia. hammer.
Qed.

End TimingProof.


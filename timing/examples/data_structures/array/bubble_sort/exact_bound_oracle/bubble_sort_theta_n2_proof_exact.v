(* This proof accomplish reasoning about exact runtimes by assuming the existence
   of an oracle function that determines whether loop iteration (i, j) has a swap
   in it.
*)

Require Import bubble_sort.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

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

Definition sum (low high : N) (f : N -> N) : N :=
    let range := List.map N.of_nat (List.seq (N.to_nat low) (N.to_nat (high - low))) in
    List.fold_left (fun acc i => acc + f i) range 0.

Lemma sum_0_0 : forall f, sum 0 0 f = 0.
Proof. reflexivity. Qed.

Lemma sum_Sn : forall low high f,
    low <= high ->
    sum low (1 + high) f = sum low high f + f high.
Proof.
    intros. unfold sum at 1.
    rewrite <- N.add_sub_assoc, N.add_1_l, N2Nat.inj_succ.
    rewrite seq_S, map_app, fold_left_app. simpl.
    rewrite N2Nat.inj_sub at 2.
    rewrite Arith_base.le_plus_minus_r_stt by lia.
    rewrite N2Nat.id. reflexivity. assumption.
Qed.

Definition time_of_bubble_sort_theta_n2 (len : N) (swap : N -> N -> bool) (t : trace) :=
  cycle_count_of_trace t =
    tslli 2 + tadd + taddi +
    (* outer loop full iterations *)
    sum 0 len (fun i =>
        tfbeq + taddi + tjal +
        (* inner loop full iterations *)
        sum 0 (len - 1) (fun j =>
            ttbne +
            tlw + tlw +
            (if swap i j then (
                tfbgeu + tsw + tsw
            ) else (
                ttbgeu
            )) + taddi
        ) +
        (* inner loop partial iteration *)
        tfbne +
        taddi + tjal
    ) +
    (* outer loop partial iteration *)
    ttbeq +
    (* return *)
    tjalr.

Definition swap_correctness (swap : N -> N -> bool) (arr : addr) : Prop :=
    forall mem i j, swap i j = (mem Ⓓ[arr + 4 * (j + 1)] <? mem Ⓓ[arr + 4 * j]).

Definition bubble_sort_theta_n2_timing_invs (s : store) (base_mem : memory)
    (arr : addr) (len : N) (_a5 : N) (swap : N -> N -> bool) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (s V_MEM32 = base_mem /\ 
                    s R_A0 = arr /\ s R_A1 = len /\
                    s R_A5 = _a5 /\
                    arr + 4 * len < 2^32 /\
                    swap_correctness swap arr /\
                    cycle_count_of_trace t' = 0)
| 0x1f0 => Some (exists mem a4, s V_MEM32 = mem /\
                   s R_A0 = arr /\ s R_A1 = len /\
                   s R_A3 = (arr + 4 * len) /\
                   (* a4 is outer loop counter *)
                   s R_A4 = a4 /\
                   a4 <= len /\
                   arr + 4 * len < 2^32 /\
                   swap_correctness swap arr /\
                 cycle_count_of_trace t' =
                   tslli 2 + tadd + taddi +
                   sum 0 a4 (fun i =>
                       tfbeq + taddi + tjal +
                       sum 0 (len - 1) (fun j =>
                           ttbne +
                            tlw + tlw +
                            (if swap i j then (
                                tfbgeu + tsw + tsw
                            ) else (
                                ttbgeu
                            )) +
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
                   a4 < len /\
                   s R_A5 = (arr + 4 * (1 + inner_loop_count)) /\
                   1 + inner_loop_count <= len /\
                   (* this is here to handle the inductive case where 
                      inner_loop_count is incremented *)
                   ~ 1 + inner_loop_count > len /\
                   0 < len /\
                   arr + 4 * len < 2^32 /\
                   swap_correctness swap arr /\
                 cycle_count_of_trace t' =
                   tslli 2 + tadd + taddi +
                   sum 0 a4 (fun i =>
                       tfbeq + taddi + tjal +
                       sum 0 (len - 1) (fun j =>
                           ttbne +
                            tlw + tlw +
                            (if swap i j then (
                                tfbgeu + tsw + tsw
                            ) else (
                                ttbgeu
                            )) +
                            taddi
                       ) +
                       (* inner loop partial iteration *)
                       tfbne +
                       taddi + tjal
                   ) +
                   tfbeq + taddi + tjal +
                   (* number of inner loops so far *)
                   sum 0 inner_loop_count (fun j =>
                        ttbne + tlw + tlw +
                        (if swap a4 j then (
                            tfbgeu + tsw + tsw
                        ) else (
                            ttbgeu
                        )) +
                        taddi
                    )
            )
| 0x220 => Some (time_of_bubble_sort_theta_n2 len swap t)
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
         (ARR_VALID: arr + 4 * len < 2^32)
         (* Oracle function *)
         (swap: N -> N -> bool)
         (SWAP: swap_correctness swap arr),
  satisfies_all 
    lifted_prog
    (bubble_sort_theta_n2_timing_invs s base_mem arr len a5 swap)
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
    destruct PRE as (MEM & A0 & A1 & A5 & ARR_VALID & Swap & Cycles). {
        repeat step. eexists. eexists. repeat split; eauto.
        now rewrite N.mod_small by assumption. lia.
        rewrite sum_0_0.
        hammer.
    }

    (* 0x1f0 -> *)
    destruct PRE as (mem & a4 & MEM & A0 & A1 & A3 & A4 & ARR_VALID &
        A4_VALID & Swap & Cycles).
    repeat step.
        (* a4 = len *)
            apply N.eqb_eq in BC. rewrite BC in *. clear BC.
            hammer; rewrite N.eqb_refl; hammer.
        (* a4 <> len *)
        do 2 eexists; exists 0; repeat split; eauto.
            apply N.eqb_neq in BC. lia.
            rewrite N.mod_small by (apply N.eqb_neq in BC; lia);
                now psimpl.
            1-3: apply N.eqb_neq in BC; lia.
            rewrite sum_0_0. hammer.

    (* 0x101bc -> *)
    destruct PRE as (mem & a4 & inner_loop_count & MEM & A0 & A1 & A3 & A4
                     & A4_LEN & A5 & ILC_LEN & ILC_LEN' & LEN_POS & ARR_VALID 
                     & Swap & Cycles).
    step.
        (* not at end of array, continue inner loop *)
        repeat step.
        (* arr[j-1] < arr[j] *)
        do 2 eexists; exists (1 + inner_loop_count); repeat split; eauto.
            now rewrite A4.
            repeat rewrite N.mul_add_distr_l. psimpl.
                rewrite N.mod_small. reflexivity.
            1-3: apply Bool.negb_true_iff, N.eqb_neq in BC; lia.

        rewrite sum_Sn by lia.
        unfold swap_correctness in Swap.
        rewrite N.mul_add_distr_l in BC0 at 2. psimpl in BC0.
        rewrite (N.add_comm 1) in BC0.
        rewrite <- Swap with (i := a4) in BC0.
        hammer.

        (* arr[j-1 >= arr[j] *)
        do 2 eexists; exists (1 + inner_loop_count); repeat split; eauto.
            now rewrite A4.
            repeat rewrite N.mul_add_distr_l. psimpl.
            rewrite N.mod_small. reflexivity.
            1-3: apply Bool.negb_true_iff, N.eqb_neq in BC; lia.

        rewrite sum_Sn by lia.
        unfold swap_correctness in Swap.
        rewrite N.mul_add_distr_l in BC0 at 2. psimpl in BC0.
        rewrite (N.add_comm 1) in BC0.
        rewrite <- Swap with (i := a4) in BC0.
        hammer.

        (* at end of array, exit inner loop -> outer loop invariant *)
        apply Bool.negb_false_iff, N.eqb_eq in BC; subst.
        repeat step.
        eexists. eexists. repeat split; eauto.
            rewrite N.mod_small; lia.
        hammer.
            rewrite N.mod_small by lia.
            replace (s' R_A1) with (1 + inner_loop_count) in * by lia.
        assert (forall x, 1 + x - 1 = x) by lia. rewrite H in *.
        rewrite sum_Sn by lia. hammer.
Qed.

End TimingProof.

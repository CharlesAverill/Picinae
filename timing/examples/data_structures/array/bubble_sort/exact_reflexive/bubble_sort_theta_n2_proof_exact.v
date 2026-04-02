(* This proof accomplish reasoning about exact runtimes by assuming the existence
   of an oracle function that determines whether loop iteration (i, j) has a swap
   in it.
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

(* Fixpoint update {A : Type} (l : list A) (i : nat) (a : A) : option (list A) :=
    match l with
    | [] => None
    | h :: t =>
        match i with
        | O => Some (a :: t)
        | S i' => match update t i' a with 
                  | None => None
                  | Some t' => Some (h :: t')
                  end
        end
    end.

Definition swap {A : Type} (l : list A) (i j : nat) : option (list A) :=
    match nth_error l i, nth_error l j with
    | Some ival, Some jval =>
        match update l i jval with
        | None => None
        | Some l' => update l j ival
        end
    | _, _ => None
    end.

Require Import Nat.
Fixpoint list_bubblesort_body (l : list N) (i j fuel : nat) : option (list N) :=
    match fuel with
    | O => None
    | S fuel' =>
        (if i <? length l then (
            if j <? length l - 1 then (
                match nth_error l j, nth_error l (j + 1) with
                | Some val_j, Some val_Sj =>
                    match swap l j (j + 1) with
                    | Some l' =>
                        list_bubblesort_body (
                            if N.ltb val_Sj val_j then (
                                l'
                            ) else l
                        ) i (j + 1) fuel'
                    | None => None
                    end
                | _, _ => None 
                end
            ) else list_bubblesort_body l (i + 1) 0 fuel'
        ) else Some l)%nat
    end.

Fixpoint list_of_arr (mem : memory) (arr : addr) (len : nat) : list N :=
    match len with
    | O => []
    | S len' => mem Ⓓ[arr] :: list_of_arr mem (arr + 4) len'
    end. *)

Fixpoint arr_bubblesort (mem : memory) (arr : addr) (len i j : N) (fuel : nat) : option memory :=
    match fuel with
    | O => Some mem
    | S fuel' =>
        if i <? len then (
            if j <? len - 1 then (
                if mem Ⓓ[arr + 4 * j + 4] <? mem Ⓓ[arr + 4 * j] then (
                    arr_bubblesort
                        (mem[Ⓓ arr + 4 * j := mem Ⓓ[arr + 4 * j + 1]]
                            [Ⓓ arr + 4 * j + 1 := mem Ⓓ[arr + 4 * j]])
                    arr len i (j + 1) fuel'
                ) else arr_bubblesort mem arr len i (j + 1) fuel'
            ) else arr_bubblesort mem arr len (i + 1) 0 fuel'
        ) else Some mem
    end.

Definition time_of_bubble_sort_theta_n2 (len : N) (N_swaps : N) (t : trace) :=
  cycle_count_of_trace t = 5.

Definition bubble_sort_theta_n2_timing_invs (s : store) (base_mem : memory)
    (arr : addr) (len : N) (_a5 : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (s V_MEM32 = base_mem /\ 
                 s R_A0 = arr /\ s R_A1 = len /\
                 s R_A5 = _a5 /\
                 arr + 4 * len < 2^32 /\
                 Some (s V_MEM32) = arr_bubblesort base_mem arr len 0 0 0
           )
| 0x1f0 => Some (exists mem a4, s V_MEM32 = mem /\
                   s R_A0 = arr /\ s R_A1 = len /\
                   s R_A3 = (arr + 4 * len) /\
                   (* a4 is outer loop counter *)
                   s R_A4 = a4 /\
                   a4 <= len /\
                   arr + 4 * len < 2^32 /\
                 Some mem = arr_bubblesort base_mem arr len 0 0 (N.to_nat (a4 * len))
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
                 Some mem = arr_bubblesort base_mem arr len 0 0 (N.to_nat (a4 * len + inner_loop_count))
            )
| 0x220 => Some (Some (s V_MEM32) = arr_bubblesort base_mem arr len 0 0 (N.to_nat (len * len)))
| _ => None end | _ => None end.

Lemma add_cancel_l : forall x y z,
    x = y -> x + z = y + z.
Proof. lia. Qed.

Lemma step_sort_swap : forall steps mem arr len i j,
    Some mem = arr_bubblesort mem arr len i j steps ->
    i <? len = true -> j <? len - 1 = true ->
    (mem Ⓓ[ 4 + arr + 4 * j ] <?
     mem Ⓓ[ arr + 4 * j ]) = true ->
    Some
    (mem [Ⓓarr + 4 * j
        := mem Ⓓ[ 4 + arr + 4 * j ] ]
    [Ⓓ 4 + arr + 4 * j := mem Ⓓ[ arr + 4 * j ] ]) =
        arr_bubblesort mem arr len i j (1 + steps).
Proof.
    induction steps; intros; simpl.
    - rewrite H0, H1. rewrite <- N.add_assoc, N.add_comm in H2.
      rewrite H2. rewrite <- (N.add_assoc 4) at 1.
      rewrite (N.add_comm 4).
    rewrite H0, H1.
    rewrite <- N.add_assoc, N.add_comm in H2. rewrite H2.

Abort.

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
    repeat split; auto. now rewrite MEM.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.
    rename a5 into _a5.

    destruct_inv 32 PRE.

    (* 0x1e4 -> 0x1f0 *)
    destruct PRE as (MEM & A0 & A1 & A5 & ARR_VALID & Cycles). {
        repeat step. eexists. exists 0. repeat split; eauto.
        now rewrite N.mod_small by assumption. lia.
    }

    (* 0x1f0 -> *)
    destruct PRE as (mem & a4 & MEM & A0 & A1 & A3 & A4 & A4_VALID & 
        ARR_VALID & Correctness).
    repeat step.
        replace a4 with len in * by lia. now find_rewrites.
        (* a4 <> len *)
        eexists. exists a4, 0. repeat split; eauto.
            rewrite N.mod_small by (apply N.eqb_neq in BC; lia);
                now psimpl.
        1-4: lia.
        rewrite N.add_0_r. now find_rewrites.

    (* 0x101bc -> *)
    destruct PRE as (mem & a4 & inner_loop_count & 
                     MEM & A0 & A1 & A3 & A4 & A5 & ILC_LEN & ILC_LEN' & LEN_POS 
                     & A4_LEN & ARR_VALID & Correctness).
    step.
        (* not at end of array, continue inner loop *)
        repeat step.
        (* arr[j-1] < arr[j] *)
        eexists. exists (s' R_A4). exists (1 + inner_loop_count).
            repeat split; eauto.
        repeat rewrite N.mul_add_distr_l. psimpl.
            rewrite N.mod_small. reflexivity.
        1-4: lia.
        psimpl.
        rewrite <- N.add_assoc, N2Nat.inj_add. simpl.
        replace (0 <? len) with true by (now apply N.ltb_lt in LEN_POS).
        destruct (0 <? len - 1) eqn:E. psimpl.
            repeat rewrite N.mul_add_distr_l in *. psimpl. psimpl in BC0.
            rewrite BC0.

        (* TODO : replace with hammer when fixed *)
        hammer. repeat rewrite (N.mul_add_distr_r 1). psimpl.
        replace (a4 * (len - 1) - N_swaps) with
            (1 + (a4 * (len - 1) - 1 - N_swaps)).
        rewrite N.mul_add_distr_r. psimpl. compare_sums.
        hammer.
        rewrite <- getmem_mod_l with 
            (a := 4294967292 + arr + 4 * (1 + inner_loop_count)) in BC0.
        replace (4294967292 + arr ⊕ 4 * (1 + inner_loop_count)) with
            (arr ⊕ 4 * inner_loop_count) in BC0.
        rewrite (N.add_comm 1 inner_loop_count), getmem_mod_l in BC0.
        rewrite N.mul_add_distr_l.
        replace (a4 * (len - 1) - 1 - N_swaps) with
            ((a4 * (len - 1) - N_swaps) - 1) by lia.
        repeat rewrite N.mul_add_distr_r. psimpl.
        remember (a4 * (tfbeq + taddi + tjal + tfbne + taddi)).
        remember (N_swaps *
            (ttbne + tlw + tlw + tfbgeu + tsw + tsw + taddi)).
        remember ((1 + N_swaps_this_iter) *
            (ttbne + tlw + tlw + tfbgeu + tsw + tsw + taddi)).
        rewrite N.mul_comm with (n := (a4 * (len - 1) - N_swaps)).
        rewrite <- mul_sub1 with (y := (a4 * (len - 1) - N_swaps)).
        remember ((a4 * (len - 1) - N_swaps - 1) *
            (ttbne + tlw + tlw + ttbgeu + taddi)).
        remember (N_swaps_this_iter *
            (ttbne + tlw + tlw + tfbgeu + tsw + tsw + taddi)).
        clear. 
        
        rewrite mul_sub1 with (y := (a4 * (len - 1) - N_swaps - 1)).

        (* arr[j-1 >= arr[j] *)
        do 2 eexists; exists (1 + inner_loop_count); repeat split; eauto.
            repeat rewrite N.mul_add_distr_l. psimpl.
            rewrite N.mod_small. reflexivity.
            1-3: apply Bool.negb_true_iff, N.eqb_neq in BC; lia.
        (* TODO : replace with hammer when fixed *)
        unfold_cycle_count_list.
        do 1 (match goal with
        | [|- context[time_of_addr ?X ?Y]] =>
            let H := fresh "H" in
            eassert(time_of_addr X Y = _) as H by
            (now (cbv - [getmem setmem N.eqb]; find_rewrites;
                    simpl; find_rewrites));
            rewrite H; clear H
        end).
        match goal with
        | [|- context[time_of_addr ?X ?Y]] =>
            let H := fresh "H" in
            eassert(time_of_addr X Y = _) as H
        end. cbv [time_of_addr].
        eassert (rv_decode (binary 516) = _) by (now compute); 
            rewrite H; clear H.
        cbv [N.eqb]. psimpl. rewrite BC0. compute. reflexivity.
        rewrite H. clear H.
        rewrite sum_Sn by lia.
        hammer.
        rewrite <- getmem_mod_l with 
            (a := 4294967292 + arr + 4 * (1 + inner_loop_count)) in BC0.
        replace (4294967292 + arr ⊕ 4 * (1 + inner_loop_count)) with
            (arr ⊕ 4 * inner_loop_count) in BC0.
        rewrite (N.add_comm 1 inner_loop_count), getmem_mod_l in BC0.
        unfold swap_correctness in Swap.
        rewrite <- Swap with (i := a4) in BC0.
        rewrite BC0.
        hammer.
        clear. rewrite N.mul_add_distr_l. now psimpl.

        (* at end of array, exit inner loop -> outer loop invariant *)
        apply Bool.negb_false_iff, N.eqb_eq in BC; subst.
        repeat step.
        eexists. eexists. repeat split; eauto.
            rewrite N.mod_small.
        lia. lia.
        hammer. rewrite N.mod_small, BC, N.eqb_refl by lia.
            hammer.
        replace len with (1 + inner_loop_count) in * by lia.
        assert (forall x, 1 + x - 1 = x) by lia. rewrite H in *. clear H.
        rewrite sum_Sn by lia. hammer.
Qed.

End TimingProof.

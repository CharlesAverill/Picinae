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
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Module bubble_sort_theta_n2Time <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound s (bubble_sort a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x1018c.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x101c8 => true
    | _ => false
  end | _ => false end.
End bubble_sort_theta_n2Time.

Module bubble_sort_theta_n2Auto := TimingAutomation bubble_sort_theta_n2Time.
Import bubble_sort_theta_n2Time bubble_sort_theta_n2Auto.

Definition time_of_bubble_sort_theta_n2 (mem : addr -> N) 
        (arr : addr) (len : N) (t : trace) :=
    (* ----------------------------------------- *)
    (* lower bound, return if len = 0 *)
    (3 + 2) + 2 + 2 + time_branch + time_branch <=
    (* ----------------------------------------- *)
    cycle_count_of_trace t <=
    (* ----------------------------------------- *)
    (* upper bound *)
    (3 + 2) + 2 + 2 +
    (* outer loop full iterations *)
    len * (
        3 + 2 + time_branch +
        (* inner loop full iterations *)
        (len - 1) * (
            time_mem + time_mem +
            (* branch timing depends on instruction latency, 
               which is dependent on memory speed, so we can't know
               whether the time of a successful branch to skip the
               if-then body will be faster or slower than 
               falling through + the if-then body
            *)
            N.max time_branch (3 + time_mem + time_mem) +
            2 + time_branch
        ) +
        (* inner loop partial iteration *)
        3 +
        2 + time_branch
    ) +
    (* outer loop partial iteration *)
    time_branch +
    (* return *)
    time_branch.

Definition bubble_sort_theta_n2_timing_invs (s : store) (base_mem : addr -> N)
    (arr : addr) (len : N) (_a5 : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1018c => Some (s V_MEM32 = Ⓜbase_mem /\ 
                    s R_A0 = Ⓓarr /\ s R_A1 = Ⓓlen /\
                    s R_A5 = Ⓓ_a5 /\
                    arr + 4 * len < 2^32 /\
                    cycle_count_of_trace t' = 0)
| 0x10198 => Some (exists mem a4, s V_MEM32 = Ⓜmem /\
                   s R_A0 = Ⓓarr /\ s R_A1 = Ⓓlen /\
                   s R_A3 = Ⓓ(arr + 4 * len) /\
                   (* a4 is outer loop counter *)
                   s R_A4 = Ⓓa4 /\
                   a4 <= len /\
                   arr + 4 * len < 2^32 /\
                   (3 + 2) + 2 + 2 <=
                   (* ----------------------------------------- *)
                   cycle_count_of_trace t' <=
                   (* ----------------------------------------- *)
                   (3 + 2) + 2 + 2 +
                   a4 * (
                       3 + 2 + time_branch +
                       (len - 1) * (
                           time_branch + time_mem + time_mem +
                           N.max time_branch (3 + time_mem + time_mem) +
                           2
                       ) +
                       (* inner loop partial iteration *)
                       3 +
                       2 + time_branch
                   )
            )
| 0x101bc => Some (exists mem a4 inner_loop_count, s V_MEM32 = Ⓜmem /\
                   s R_A0 = Ⓓarr /\ s R_A1 = Ⓓlen /\
                   s R_A3 = Ⓓ(arr + 4 * len) /\
                   (* a4 is outer loop counter *)
                   s R_A4 = Ⓓa4 /\
                   s R_A5 = Ⓓ(arr + 4 * (1 + inner_loop_count)) /\
                   1 + inner_loop_count <= len /\
                   (* this is here to handle the inductive case where 
                      inner_loop_count is incremented *)
                   ~ 1 + inner_loop_count > len /\
                   0 < len /\
                   a4 < len /\
                   arr + 4 * len < 2^32 /\
                   (3 + 2) + 2 + 2 <=
                   (* ----------------------------------------- *)
                   cycle_count_of_trace t' <=
                   (* ----------------------------------------- *)
                   (3 + 2) + 2 + 2 +
                   a4 * (
                       3 + 2 + time_branch +
                       (len - 1) * (
                           time_mem + time_mem +
                           N.max time_branch (3 + time_mem + time_mem) +
                           2 + time_branch
                       ) +
                       3 +
                       2 + time_branch
                   ) +
                   3 + 2 + time_branch +
                   (* number of inner loops so far *)
                   inner_loop_count * (time_branch + time_mem + time_mem +
                    N.max time_branch (3 + time_mem + time_mem) + 2)
            )
| 0x101c8 => Some (time_of_bubble_sort_theta_n2 base_mem arr len t)
| _ => None end | _ => None end.

Definition lifted_bubble_sort_theta_n2 : program :=
    lift_riscv bubble_sort.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Lemma div_add_distr : forall x y z,
    z <> 0 ->
    (x * z + y * z) / z = x + y.
Proof.
    intros. rewrite N.div_add_l by assumption.
    now rewrite N.div_mul by assumption.
Qed.

Lemma div_sub_distr : forall x y z,
    z <> 0 ->
    (x * z - y * z) / z = x - y.
Proof.
    intros.
    rewrite <- N.mul_sub_distr_r. now apply N.div_mul.
Qed.

Theorem bubble_sort_theta_n2_timing:
  forall s t s' x' base_mem arr len a5
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (A0: s R_A0 = Ⓓarr)
         (A2: s R_A1 = Ⓓlen)
         (A5: s R_A5 = Ⓓa5)
         (* array must fit inside the address space without wrapping *)
         (* this shouldn't be necessary but makes the proof easy *)
         (ARR_VALID: arr + 4 * len < 2^32),
  satisfies_all 
    lifted_bubble_sort_theta_n2
    (bubble_sort_theta_n2_timing_invs s base_mem arr len a5)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.
    rename a5 into _a5.

    destruct_inv 32 PRE.

    (* 0x1018c -> 0x10198 *)
    destruct PRE as (MEM & A0 & A1 & A5 & ARR_VALID & Cycles). {
        repeat step. eexists. eexists. repeat split; eauto.
        now rewrite N.mod_small by assumption. lia.
        (* lower bound *)
        hammer.
        (* upper bound *)
        hammer.
    }

    (* 0x10198 -> *)
    destruct PRE as (mem & a4 & MEM & A0 & A1 & A3 & A4 & A4_VALID & ARR_VALID &
        Cycles_low & Cycles_high).
    repeat step.
        (* a4 = len *)
        unfold time_of_bubble_sort_theta_n2.
            apply N.eqb_eq in BC; subst. split;
            hammer; rewrite N.eqb_refl; hammer.
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
            1-3: apply Bool.negb_true_iff, N.eqb_neq in BC; lia.
        hammer. hammer.
        (* arr[j-1 >= arr[j] *)
        do 2 eexists; exists (1 + inner_loop_count); repeat split; eauto.
            repeat rewrite N.mul_add_distr_l. psimpl.
            rewrite N.mod_small. reflexivity.
            1-3: apply Bool.negb_true_iff, N.eqb_neq in BC; lia.
        hammer. hammer.
        (* at end of array, exit inner loop -> outer loop invariant *)
        apply Bool.negb_false_iff, N.eqb_eq in BC; subst.
        repeat step.
        eexists. eexists. repeat split; eauto.
            rewrite N.mod_small.
        lia. lia.
        hammer.
        replace len with (1 + inner_loop_count) by lia.
        hammer. rewrite BC, N.eqb_refl.
        rewrite N.mod_small by lia. hammer.
Qed.
            


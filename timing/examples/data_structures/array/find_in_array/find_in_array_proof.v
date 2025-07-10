Require Import array.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Module find_in_arrayTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound s (array_bin a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x208 => true
    | _ => false
  end | _ => false end.
End find_in_arrayTime.

Module find_in_arrayAuto := TimingAutomation find_in_arrayTime.
Import find_in_arrayTime find_in_arrayAuto.

Definition key_in_array (mem : addr -> N) (arr : addr) (key : N) (len : N) : Prop :=
    exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key.

Lemma lt_impl_lt_or_eq : forall x y,
    x < 1 + y -> x = y \/ x < y.
Proof. lia. Qed.

Definition N_peano_ind_Set (P : N -> Set) := N.peano_rect P.

Fixpoint key_in_array_dec (mem : addr -> N) (arr : addr) (key len : N)
        : {key_in_array mem arr key len} + {~ key_in_array mem arr key len}.
    induction len using N_peano_ind_Set.
    - right. intro. destruct H as (idx & Contra & _). lia.
    - destruct IHlen as [IN | NOT_IN].
        -- left. destruct IN as (idx & Lt & Eq). exists idx.
            split. lia. assumption.
        -- destruct (N.eq_dec (mem Ⓓ[arr + (len << 2)]) key).
            + left. exists len. split. lia. assumption.
            + right. intro. destruct H as (idx & Lt & Eq).
                assert (idx = len). {
                destruct (lt_impl_lt_or_eq idx len). lia.
                    subst. reflexivity.
                exfalso. apply NOT_IN. exists idx. now split.
                } subst. contradiction.
Qed.

Definition time_of_find_in_array (mem : addr -> N) 
        (arr : addr) (key : N) (len : N) (found_idx : option N)
        (t : trace) :=
    cycle_count_of_trace t =
        (* setup time *)
        2 +
        (* loop iterations *)
        (match found_idx with None => len | Some i => i end) *
        (* loop body duration *)
        (3 + (3 + T_shift_latency 2) + 2 + time_mem + 3 + 2 + time_branch) +
        (* partial loop iteration before loop exit *)
        (match found_idx with 
         | None => time_branch (* loop condition fail *)
         | Some _ => 3 + (3 + T_shift_latency 2) + 2 + time_mem + time_branch
         end) +
        (* shutdown time *)
        2 + time_branch.

Definition timing_postcondition (mem : addr -> N) (arr : addr)
        (key : N) (len : N) (t : trace) : Prop :=
    (exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key /\
        (* i is the first index where the key is found *)
        (forall j, j < i -> mem Ⓓ[arr + (j << 2)] <> key) /\
        time_of_find_in_array mem arr key len (Some i) t) \/
    ((~ exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key) /\
        time_of_find_in_array mem arr key len None t).

Definition find_in_array_timing_invs (s : store) (base_mem : addr -> N)
    (sp : N) (arr : addr) (key : N) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_A0 = Ⓓarr /\ s R_A1 = Ⓓkey /\ 
            s R_A2 = Ⓓlen /\ 4 * len <= 2^32 - 1 /\
            cycle_count_of_trace t' = 0)
| 0x1e8 => Some (exists mem a5,
    (* bindings *)
    s V_MEM32 = Ⓜmem /\
    s R_A0 = Ⓓarr /\ s R_A1 = Ⓓkey /\ s R_A2 = Ⓓlen /\
    s R_A5 = Ⓓa5 /\
    (* preservation *)
    (forall i, i < len ->
        mem Ⓓ[arr + (i << 2)] = base_mem Ⓓ[arr + (i << 2)]) /\
    (* haven't found a match yet *)
    (forall i, i < a5 ->
        mem Ⓓ[arr + (i << 2)] <> key) /\
    a5 <= len /\
    cycle_count_of_trace t' =
        (* pre-loop time *)
        2 +
        (* loop counter stored in register a5 *)
        a5 *
        (* full loop body length - can't have broken out by this address *)
        (3 + (3 + T_shift_latency 2) + 2 + time_mem + 3 + 2 + time_branch)
    )
| 0x208 => Some (timing_postcondition base_mem arr key len t)
| _ => None end | _ => None end.

Definition lifted_find_in_array : program :=
    lift_riscv array_bin.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Theorem find_in_array_timing:
  forall s t s' x' base_mem sp arr key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (SP: s R_SP = Ⓓsp)
         (A0: s R_A0 = Ⓓarr)
         (A1: s R_A1 = Ⓓkey)
         (A2: s R_A2 = Ⓓlen)
         (* length must fit inside the address space, arr is 4-byte integers *)
         (LEN_VALID: 4 * len <= 2^32 - 1),
  satisfies_all 
    lifted_find_in_array
    (find_in_array_timing_invs s base_mem sp arr key len)
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

    destruct_inv 32 PRE.

    (* 0x101b0 -> 0x101e0 *)
    destruct PRE as (Mem & A0 & A1 & A2 & LEN_VALID & Cycles).
    repeat step.
        repeat eexists; auto.
        (* key not found yet *) intros; lia.
        (* idx <= len *) psimpl; lia.
        (* cycles *)
        hammer.

    destruct PRE as (mem & a5 & MEM & A0 & A1 & A2 & A5 & Preserved &
        NotFound & A5_LEN & Cycles).
    destruct (key_in_array_dec mem arr key len) as [IN | NOT_IN].
    (* There is a matching element in the array *) {
        step.
        repeat step.
        (* postcondition after loop condition fail *)
            left. exists a5. split.
                now apply N.ltb_lt. 
            split.
                rewrite <- Preserved. now apply N.eqb_eq in BC0.
                now apply N.ltb_lt in BC. 
            split.
                intros. rewrite <- Preserved by lia. now apply NotFound.
            unfold time_of_find_in_array.
            hammer. unfold T_shift_latency, CPU_FAST_SHIFT_EN. 
            psimpl. lia.
        (* loop invariant after going around *)
            repeat eexists; auto.
            (* key not found *)
            intros. apply N.ltb_lt in BC.
                rewrite N.mod_small in H. destruct (lt_impl_lt_or_eq _ _ H).
                subst. now apply N.eqb_neq in BC0. now apply NotFound.
                apply N.le_lt_trans with len. lia. apply (rv_regsize MDL A2).
            (* 1 + a5 <= len *)
            apply N.ltb_lt in BC. rewrite N.mod_small. lia.
                apply N.le_lt_trans with len. lia. apply (rv_regsize MDL A2).
            (* cycles *)
            hammer. unfold T_shift_latency, CPU_FAST_SHIFT_EN.
            rewrite N.mod_small. lia.
                apply Bool.negb_false_iff, N.ltb_lt in BC.
                apply N.le_lt_trans with len. lia.
                apply (rv_regsize MDL A2).
        (* iterated len times - contradiction *)
        exfalso. destruct IN as (idx & IDX_LEN & IN).
            apply (NotFound idx). apply N.ltb_ge in BC. lia.
            assumption.
    }

    (* There is not a matching element in the array *) {
        step.
        do 4 step.
        (* contradiction - BC0 says a match has been found *)
            exfalso. apply NOT_IN. exists a5. split. now apply N.ltb_lt.
            apply N.eqb_eq in BC0.
            assumption.
        (* a match has not been found, continue *)
        repeat step.
            repeat eexists; auto.
            (* key not found *)
            intros. apply N.ltb_lt in BC.
                rewrite N.mod_small in H. destruct (lt_impl_lt_or_eq _ _ H).
                subst. now apply N.eqb_neq in BC0. now apply NotFound.
                apply N.le_lt_trans with len. lia. apply (rv_regsize MDL A2).
            (* 1 + a5 <= len *)
            apply N.ltb_lt in BC. rewrite N.mod_small. lia.
                apply N.le_lt_trans with len. lia. apply (rv_regsize MDL A2).
            (* cycles *)
            hammer.
            unfold T_shift_latency, CPU_FAST_SHIFT_EN.
            rewrite N.mod_small. lia.
                apply Bool.negb_false_iff, N.ltb_lt in BC.
                apply N.le_lt_trans with len. lia.
                apply (rv_regsize MDL A2).
        (* a match has not been found, break and return *)
        repeat step.
            unfold timing_postcondition, time_of_find_in_array. right.
            split. intro. apply NOT_IN. destruct H as (idx & IDX_LEN & IN).
            exists idx. split. assumption. now rewrite Preserved.
            hammer. find_rewrites. replace a5 with len in * by
                (rewrite Bool.negb_true_iff, N.ltb_ge in BC; lia).
            unfold T_shift_latency, CPU_FAST_SHIFT_EN. lia.
    }
Qed.


Require Import array_opt.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Module find_in_arrayTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (array_opt_bin a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x10190.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x101bc | 0x101c0 => true
    | _ => false
  end | _ => false end.
End find_in_arrayTime.

Module find_in_arrayAuto := TimingAutomation find_in_arrayTime.
Import find_in_arrayTime find_in_arrayAuto.

Definition key_in_array (mem : addr -> N) (arr : addr) (key : N) (len : N) : Prop :=
    exists i, i < len /\ mem Ⓓ[arr + 4 * i] = key.

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
        -- destruct (N.eq_dec (mem Ⓓ[arr + 4 * len]) key).
            + left. exists len. split. lia. assumption.
            + right. intro. destruct H as (idx & Lt & Eq).
                assert (idx = len). {
                destruct (lt_impl_lt_or_eq idx len). lia.
                    subst. reflexivity.
                exfalso. apply NOT_IN. exists idx. now split.
                } subst. contradiction.
Qed.

Definition time_of_find_in_array_opt (mem : addr -> N) 
        (arr : addr) (key : N) (len : N) (found_idx : option N)
        (t : trace) :=
    cycle_count_of_trace t =
        (* setup time *)
        4 + 
        if len =? 0 then (
            time_branch + time_branch
        ) else (
            (* more setup *)
            3 + 2 + time_branch + time_mem + 2 +
            (* arr[0] check *)
            if mem Ⓓ[arr] =? key then (
                3 + 2 + time_branch
            ) else (
                time_branch +
                (* loop iterations *)
                (match found_idx with None => len - 1 | Some i => i end) *
                (* loop body duration *)
                (2 + 3 + time_mem + 2 + time_branch) +
                (* partial loop iteration before loop exit *)
                (match found_idx with
                 | None => 2 + time_branch
                 | Some _ => 2 + 3 + time_mem + 2 + 3 + 2
                 end) +
                (* return *)
                time_branch
            )
        ).

Definition timing_postcondition (mem : addr -> N) (arr : addr)
        (key : N) (len : N) (t : trace) : Prop :=
    (exists i, i < len /\ mem Ⓓ[arr + 4 * i] = key /\
        (* i is the first index where the key is found *)
        (forall j, j < i -> mem Ⓓ[arr + 4 * j] <> key) /\
        time_of_find_in_array_opt mem arr key len (Some (i - 1)) t) \/
    ((~ exists i, i < len /\ mem Ⓓ[arr + 4 * i] = key) /\
        time_of_find_in_array_opt mem arr key len None t).

Definition find_in_array_opt_timing_invs (s : store) (base_mem : addr -> N)
    (sp : N) (arr : addr) (key : N) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x10198 => Some (s V_MEM32 = Ⓜbase_mem /\ 
            s R_A5 = Ⓓarr /\ s R_A1 = Ⓓkey /\ s R_A0 = Ⓓlen /\ s R_A2 = Ⓓlen /\
            4 * len <= 2^32 - 1 /\ cycle_count_of_trace t' = 4)
| 0x101a4 => Some (exists mem a4,
    (* bindings *)
    s R_A5 = Ⓓ((4 * (1 + a4)) ⊕ arr) /\ s R_A1 = Ⓓkey /\ s R_A0 = Ⓓlen /\ 
    s R_A4 = Ⓓa4 /\ s V_MEM32 = Ⓜmem /\
    (* passed the zero-length check *)
    0 < len /\
    4 * len <= 2^32 - 1 /\
    a4 < len /\
    (* preservation *)
    (forall i, i < len ->
        mem Ⓓ[arr + 4 * i] = base_mem Ⓓ[arr + 4 * i]) /\
    (* haven't found a match yet *)
    (forall i, i < 1 + a4 ->
        mem Ⓓ[arr + 4 * i] <> key) /\
    cycle_count_of_trace t' =
        (* pre-loop time *)
        4 + 3 + 2 + time_branch + time_mem + 2 + time_branch +
        (* loop counter stored in register a4 *)
        a4 *
        (* full loop body length - can't have broken out by this address *)
        (2 + 3 + time_mem + 2 + time_branch)
    )
| 0x101bc | 0x101c0 => Some (timing_postcondition base_mem arr key len t)
| _ => None end | _ => None end.

Definition lifted_find_in_array_opt : program :=
    lift_riscv array_opt_bin.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Theorem find_in_array_opt_timing:
  forall s t s' x' base_mem sp arr key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (A0: s R_A0 = Ⓓarr)
         (A1: s R_A1 = Ⓓkey)
         (A2: s R_A2 = Ⓓlen)
         (* length must fit inside the address space, arr is 4-byte integers *)
         (LEN_VALID: 4 * len <= 2^32 - 1),
  satisfies_all 
    lifted_find_in_array_opt
    (find_in_array_opt_timing_invs s base_mem sp arr key len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. step.
    now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    (* 0x10198 : beqz a2,101bc <find_in_array+0x2c>  *)
    destruct PRE as (Mem & ARR & KEY & LEN & A2 & LEN_VALID & Cycles).
    step.
    (* len = 0 *)
        right. split. intro. destruct H as (idx & Contra & _).
            apply N.eqb_eq in BC. subst. lia.
        unfold time_of_find_in_array_opt.
        hammer. find_rewrites. unfold time_branch, time_mem. lia.
    (* len <> 0 *)
        do 5 step. (* 0x1019c -> 0x101b4 *)
        (* arr[0] <> key *)
            eexists. exists 0. repeat split; eauto.
            1-2: apply N.eqb_neq in BC; psimpl; lia.
            (* haven't found key yet *)
            intros. psimpl in H. replace i with 0 in * by lia. psimpl.
                now rewrite Bool.negb_true_iff, N.eqb_neq in BC0.
            (* cycles *)
            hammer. find_rewrites. unfold time_branch, time_mem. lia.
        (* arr[0] = key *)
            repeat step. unfold timing_postcondition. left. exists 0.
            repeat split. apply N.eqb_neq in BC. lia.
                psimpl. now apply Bool.negb_false_iff, N.eqb_eq in BC0.
                intros; lia.
            unfold time_of_find_in_array_opt.
            hammer. find_rewrites. unfold time_branch, time_mem. lia.

    (* 0x101a4 -> 0x101b4 *)
    destruct PRE as (mem & a4 & Arr & Key & Len & A4 & Mem & 
        LenPos & LenMax & IdxLen & Preserved & NotFound & Cycles).
    repeat step.
    (* idx = len *)
        apply N.eqb_eq in BC. rewrite N.mod_small in BC by lia. subst. 
        unfold timing_postcondition. right. split. intro.
        destruct H as (FoundIdx & FoundIdxLen & Found). 
        apply (NotFound FoundIdx). lia. now rewrite Preserved by lia.
        unfold time_of_find_in_array_opt. hammer. find_rewrites.
        rewrite N.mod_small, N.eqb_refl by lia.
        pose proof (NotFound 0 LenPos). rewrite <- N.eqb_neq in H.
        rewrite Preserved in H by lia. psimpl in H. find_rewrites.
        psimpl. unfold time_mem, time_branch. lia.
    (* idx <> len, key not found *)
        exists mem, (1 + a4).
        replace (1 ⊕ a4) with (1 + a4) in * by (now rewrite N.mod_small by lia).
        repeat split; auto.
        repeat rewrite N.mul_add_distr_l; now psimpl.
        apply N.eqb_neq in BC. lia.
        intros. destruct (lt_impl_lt_or_eq _ _ H). subst. 
            apply Bool.negb_true_iff, N.eqb_neq in BC0. now rewrite N.add_comm.
            now apply NotFound.
        hammer. find_rewrites. unfold time_branch, time_mem. lia.
    (* idx <> len, key found *)
        unfold timing_postcondition. left. exists (1 + a4).
        replace (1 ⊕ a4) with (1 + a4) in * by (now rewrite N.mod_small by lia).
        repeat split.
            apply N.eqb_neq in BC; lia.
            apply Bool.negb_false_iff, N.eqb_eq in BC0.
                apply N.eqb_neq in BC.
                rewrite <- Preserved, N.add_comm. assumption. lia.
            intros. rewrite <- Preserved. now apply NotFound. lia.
        unfold time_of_find_in_array_opt. hammer.
        assert (len =? 0 = false) by (apply N.eqb_neq; lia).
        assert (mem Ⓓ[ arr + 4 * 0 ] =? key = false) by (apply N.eqb_neq, NotFound; lia).
        find_rewrites. replace arr with (arr + 4 * 0) by lia. 
        rewrite <- Preserved by lia. rewrite H0. unfold time_mem, time_branch.
        psimpl. lia.
Qed.


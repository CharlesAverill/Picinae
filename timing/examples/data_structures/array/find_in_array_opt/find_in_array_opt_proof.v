Require Import array_opt.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_find_in_array_opt <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x20c => true
        | _ => false
    end | _ => false end.

    Definition binary := array_bin.
End Program_find_in_array_opt.

Module RISCVTiming := RISCVTiming cpu Program_find_in_array_opt.
Module find_in_array_optAuto := RISCVTimingAutomation RISCVTiming.
Import Program_find_in_array_opt find_in_array_optAuto.

Definition key_in_array (mem : memory) (arr : addr) (key : N) (len : N) : Prop :=
    exists i, i < len /\ mem Ⓓ[arr + 4 * i] = key.

Lemma lt_impl_lt_or_eq : forall x y,
    x < 1 + y -> x = y \/ x < y.
Proof. lia. Qed.

Definition N_peano_ind_Set (P : N -> Set) := N.peano_rect P.

Fixpoint key_in_array_dec (mem : memory) (arr : addr) (key len : N)
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

Definition time_of_find_in_array_opt (len : N) (found_idx : option N) (t : trace) :=
    cycle_count_of_trace t =
        if len =? 0 then (
            ttbeq + taddi + tjalr
        ) else (
            (* setup *)
            tfbeq + taddi + tjal + tlw + taddi +
            (* arr[0] check *)
            if (match found_idx with Some 0 => true | _ => false end) then (
                tfbne + taddi + taddi + tjalr
            ) else (
                ttbne +
                (* loop iterations *)
                (match found_idx with None => len - 1 | Some i => i - 1 end) *
                (* loop body duration *)
                (taddi + tfbeq + tlw + taddi + ttbne) +
                (* partial loop iteration before loop exit *)
                (match found_idx with
                 | None => taddi + ttbeq
                 | Some _ => taddi + tfbeq + tlw + taddi + tfbne + taddi
                 end) +
                (* return *)
                taddi + tjalr
            )
        ).

Definition timing_postcondition (mem : memory) (arr : addr)
        (key : N) (len : N) (t : trace) : Prop :=
    (exists i, i < len /\ mem Ⓓ[arr + 4 * i] = key /\
        (* i is the first index where the key is found *)
        (forall j, j < i -> mem Ⓓ[arr + 4 * j] <> key) /\
        time_of_find_in_array_opt len (Some i) t) \/
    ((~ exists i, i < len /\ mem Ⓓ[arr + 4 * i] = key) /\
        time_of_find_in_array_opt len None t).

Definition find_in_array_opt_timing_invs (s : store) (base_mem : memory)
    (sp : N) (arr : addr) (key : N) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (
    (* bindings *)
    s V_MEM32 = base_mem /\ s R_A0 = arr /\ s R_A1 = key /\
    s R_A2 = len /\
    (* valid array length *)
    4 * len <= 2^32 - 1 /\
    cycle_count_of_trace t' = 0)
| 0x1f0 => Some (
    (* bindings *)
    s V_MEM32 = base_mem /\ s R_A0 = (4 * (s R_A5 + 1) ⊕ arr) 
    /\ s R_A1 = key /\ s R_A2 = len /\
    (* passed the zero-length check *)
    0 < len /\
    4 * len <= 2^32 - 1 /\
    s R_A5 < len /\
    (* preservation *)
    (forall i, i < len ->
        (s V_MEM32) Ⓓ[arr + 4 * i] = base_mem Ⓓ[arr + 4 * i]) /\
    (* haven't found a match yet *)
    (forall i, i < 1 + s R_A5 ->
        (s V_MEM32) Ⓓ[arr + 4 * i] <> key) /\
    cycle_count_of_trace t' =
        (* pre-loop time *)
        tfbeq + taddi + tjal + tlw + taddi + ttbne +
        (* loop counter stored in register a4 *)
        s R_A5 *
        (* full loop body length - can't have broken out by this address *)
        (taddi + tfbeq + tlw + taddi + ttbne)
    )
| 0x20c => Some (timing_postcondition base_mem arr key len t)
| _ => None end | _ => None end.

Theorem find_in_array_opt_timing:
  forall s t s' x' base_mem sp arr key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = arr)
         (A1: s R_A1 = key)
         (A2: s R_A2 = len)
         (* length must fit inside the address space, arr is 4-byte integers *)
         (LEN_VALID: 4 * len <= 2^32 - 1),
  satisfies_all 
    lifted_prog
    (find_in_array_opt_timing_invs s base_mem sp arr key len)
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

    (* 0x1e4 : beqz	a2,208 <find_in_array+0x24> *)
    destruct PRE as (Mem & ARR & KEY & LEN & LEN_VALID & Cycles).
    step.
    (* len = 0 *)
        repeat step. right. split. intro. destruct H as (idx & Contra & _).
            apply N.eqb_eq in BC. lia.
        unfold time_of_find_in_array_opt.
        hammer.
    (* len <> 0 *)
        do 5 step. (* 0x1e4 -> 0x200 *)
        (* arr[0] <> key *)
            repeat split; eauto.
            1-2: apply N.eqb_neq in BC; psimpl; lia.
            (* haven't found key yet *)
            intros. psimpl in H. replace i with 0 in * by lia. psimpl.
                now rewrite Bool.negb_true_iff, N.eqb_neq in BC0.
            (* cycles *)
            hammer.
        (* arr[0] = key *)
            repeat step. left. exists 0.
            repeat split. apply N.eqb_neq in BC. lia.
                psimpl. now apply Bool.negb_false_iff, N.eqb_eq in BC0.
                intros; lia.
            unfold time_of_find_in_array_opt.
            hammer.

    (* 0x1f0 -> 0x200 *)
    destruct PRE as (mem & A0 & A1 & A2 &
        LenPos & LenMax & IdxLen & Preserved & NotFound & Cycles).
    repeat step.
    (* idx = len *)
        apply N.eqb_eq in BC. rewrite N.mod_small in BC by lia. subst. 
        right. split. intro.
            destruct H as (FoundIdx & FoundIdxLen & Found). 
            apply (NotFound FoundIdx). lia. assumption.
        unfold time_of_find_in_array_opt. hammer.
    (* idx <> len, key not found *)
        replace (1 ⊕ s' R_A5) with (1 + s' R_A5) in * by 
            (now rewrite N.mod_small by lia).
        repeat split; auto.
        repeat rewrite N.mul_add_distr_l; now psimpl.
        apply N.eqb_neq in BC. lia.
        intros. destruct (lt_impl_lt_or_eq _ _ H). subst. 
            apply Bool.negb_true_iff, N.eqb_neq in BC0.
            now rewrite N.add_comm.
            rewrite <- Preserved. now apply NotFound.
            lia.
        hammer.
    (* idx <> len, key found *)
        left. exists (1 + s' R_A5).
        replace (1 ⊕ s' R_A5) with (1 + s' R_A5) in * by 
            (now rewrite N.mod_small by lia).
        repeat split.
            apply N.eqb_neq in BC; lia.
            apply Bool.negb_false_iff, N.eqb_eq in BC0.
                apply N.eqb_neq in BC.
                now rewrite N.add_comm.
            intros. rewrite <- Preserved by lia. now apply NotFound.
        unfold time_of_find_in_array_opt. hammer.
        replace (len =? 0) with false by (symmetry; apply N.eqb_neq; lia).
        hammer.
Qed.

End TimingProof.

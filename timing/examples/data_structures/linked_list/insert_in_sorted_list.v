(* This proof and function are intended to be a simpler version of 
   sorted list insertion as seen in FreeRTOS/list.c:vListInsert

   We can assume the following:
   - the provided list pointer is non-null
   - the list is sorted
   - there is a final element with value INT_MAX
*)

Require Import linked_list.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu: CPUTimingBehavior).

Module Program_insert_in_sorted_list <: ProgramInformation.
    Definition entry_addr : N := 0x22c.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x25c => true
        | _ => false
    end | _ => false end.

    Definition binary := linked_list_bin.
End Program_insert_in_sorted_list.

Module RISCVTiming := RISCVTiming cpu Program_insert_in_sorted_list.
Module insert_in_sorted_list := RISCVTimingAutomation RISCVTiming.
Import Program_insert_in_sorted_list insert_in_sorted_list.

Module p <: LinkedListParams.
  Definition w := 32.
  Definition e := LittleE.
  Definition dw := 4.
  Definition pw := 4.
  Global Transparent w e dw pw.
End p.
Module LL := Theory_RISCV.LinkedLists p.
Import LL.
Ltac psimpl_hook ::= psimpl.
Ltac gdep x := generalize dependent x.
Global Ltac Zify.zify_pre_hook ::= idtac.

Definition INT_MAX := 0x7fffffff.
Definition NULL := 0.

Definition is_maximal (mem : memory)
    (l max_node : addr) (new_val max_val : N) (max_dist len : nat) : Prop :=
  node_distance mem l max_node max_dist /\
  (max_dist <= len)%nat /\
  list_node_value mem max_node = Some max_val/\
  new_val < max_val /\
  LLForall (fun m a =>
    match list_node_value m a with
    | None =>
        (* Can't have a non-null element in the list *)
        if a =? NULL then True else False
    | Some val =>
        val <= new_val
    end
  ) mem l.

Definition time_of_insert_in_sorted_list 
    (mem : memory) (l value : addr) (max_dist : N) (t : trace) :=
  cycle_count_of_trace t =
    tlw + tlui + taddi +
    (if mem Ⓓ[value] =? INT_MAX then (
        ttbeq
    ) else (
        tfbeq + max_dist * (
            taddi + tlw + tlw + ttbgeu
        ) + taddi + tlw + tlw + tfbgeu + taddi
    )) + tlw + tsw + tsw + tjalr.

Definition insert_in_sorted_list_timing_invs (base_mem : memory)
    (l value max_node : addr) (new_val max_val : N) (max_dist len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x22c => Some (
    is_maximal base_mem l max_node new_val max_val max_dist len /\
    s R_A0 = l /\ s R_A1 = value /\ s V_MEM32 = base_mem /\
    l <> NULL /\ len <> 0%nat /\
    node_distance base_mem l NULL len /\
    cycle_count_of_trace t' = 0
  )
| 0x23c => Some (exists ctr,
    is_maximal base_mem l max_node new_val max_val max_dist len /\
    (base_mem Ⓓ[value] =? INT_MAX) = false /\
    s R_A1 = value /\ s V_MEM32 = base_mem /\
    l <> NULL /\ len <> 0%nat /\
    (ctr <= max_dist)%nat /\
    node_distance base_mem l NULL len /\
    node_distance base_mem l (s R_A0) ctr /\
    list_node_next base_mem (s R_A0) = Some (base_mem Ⓓ[4 + s R_A0]) /\
    cycle_count_of_trace t' = tlw + tlui + taddi +
        tfbeq + (N.of_nat ctr) * (
            taddi + tlw + tlw + ttbgeu
        )
  )
| 0x25c => Some (time_of_insert_in_sorted_list base_mem l value (N.of_nat max_dist) t)
| _ => None end | _ => None end.

Lemma le_cases : forall n m,
    (n <= m -> n < m \/ n = m)%nat.
Proof. lia. Qed.

Lemma not_at_end_next : forall mem head len a1 dist1 a2 dist2,
    node_distance mem head NULL len ->
    node_distance mem head a1 dist1 ->
    node_distance mem head a2 dist2 ->
    (dist2 < dist1 <= len)%nat ->
    exists val2, list_node_next mem a2 = Some val2.
Proof.
    intros. unfold list_node_next. destruct a2.
    - pose proof (node_distance_uniq _ _ _ _ _ H H1).
        subst. lia.
    - eexists. reflexivity.
Qed.

Definition head_nonnull_impl_len_nonzero : forall mem head len,
    node_distance mem head NULL len ->
    head <> NULL ->
    len <> 0%nat.
Proof.
    intros. destruct len.
    - inversion H. contradiction.
    - discriminate.
Qed. 

Theorem insert_in_sorted_list_timing:
  forall s t s' x' base_mem l value max_node new_val max_val max_dist len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (A0: s R_A0 = l)
         (A1: s R_A1 = value)
         (MEM: s V_MEM32 = base_mem)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM32) l NULL len)
         (* l is non-null *)
         (L_NN: l <> NULL)
         (* there is a maximal node *)
         (MAX: is_maximal base_mem l max_node new_val max_val max_dist len),
  satisfies_all
    lifted_prog
    (insert_in_sorted_list_timing_invs base_mem l value max_node new_val max_val max_dist len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep r5_step.
    simpl. rewrite ENTRY. unfold entry_addr. repeat step.
    split. assumption. repeat split; auto.
    eapply head_nonnull_impl_len_nonzero; eassumption.
    now rewrite <- MEM.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    - destruct PRE as (MAX & A0 & A1 & MEM & L_NN & Len_Nz & Len & Cycles).
        repeat step.
        -- unfold INT_MAX. hammer.
        -- exists 0%nat. split. assumption.
            repeat split; auto. lia.
            rewrite A0. apply Dst0.
            unfold list_node_next.
                destruct (s' R_A0).
                    subst l. contradiction.
                reflexivity.
            hammer.
    - destruct PRE as (ctr & MAX & ValueValid & A1 & MEM & L_NN & Len_Nz & CtrMax &
                        Len & CtrDist & Next & Cycles).
        repeat step.
        -- hammer. replace ctr with max_dist.
            hammer. admit.
        -- exists (S ctr). split. assumption. repeat split; auto.
            admit.
            eapply node_distance_next_S_len. apply Next.
            eapply distance_null_imp_well_formed. now eassumption.
            assumption.
            destruct MAX, H0, H1, H2.
            pose proof (not_at_end_next _ _ _ _ _ _ _ Len H CtrDist).
            destruct (Nat.eq_dec ctr max_dist).
                subst ctr.
                pose proof (node_distance_uniq' _ _ _ _ _ _ CtrDist H eq_refl).
                rewrite H5 in *; clear H5.
                rewrite LLForall_forall in H3.
                specialize (H3 (s' R_A4)).
                
            unfold list_node_next.
                destruct (s' R_A0).
                    pose proof (node_distance_uniq _ _ _ _ _ Len CtrDist).
                        subst len.
                    
                reflexivity.


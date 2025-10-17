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

Definition insertion_index mem l le_node le_dist le_val new_val len :=
    exists gt_node gt_val,
    node_distance mem l le_node le_dist /\
    list_node_value mem le_node = Some le_val /\
    list_node_next mem le_node = Some gt_node /\
    list_node_value mem gt_node = Some gt_val /\
    gt_node <> NULL /\
    le_val <= new_val < gt_val /\
    gt_val <= INT_MAX /\
    (le_dist < len)%nat /\
    (* all nodes below le_dist satisfy n.val <= new_val *)
    forall n d v,
        node_distance mem l n d ->
        list_node_value mem n = Some v ->
        ((d <= le_dist)%nat <-> v <= new_val).

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
    (l value le_node sentry : addr) (new_val le_val : N) (le_dist len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x22c => Some (
    insertion_index base_mem l le_node le_dist le_val new_val len /\
    node_distance (s V_MEM32) l sentry (len - 1) /\
    list_node_value (s V_MEM32) sentry = Some INT_MAX /\
    s R_A0 = l /\ s R_A1 = value /\ s V_MEM32 = base_mem /\
    s R_A0 <> NULL /\
    s V_MEM32 Ⓓ[value] = new_val /\
    l <> NULL /\ len <> 0%nat /\
    node_distance base_mem l NULL len /\
    cycle_count_of_trace t' = 0
  )
| 0x23c => Some (exists ctr,
    insertion_index base_mem l le_node le_dist le_val new_val len /\
    node_distance (s V_MEM32) l sentry (len - 1) /\
    list_node_value (s V_MEM32) sentry = Some INT_MAX /\
    (base_mem Ⓓ[value] =? INT_MAX) = false /\
    s R_A0 <> NULL /\
    s R_A1 = value /\ s R_A4 = new_val /\ s V_MEM32 = base_mem /\
    l <> NULL /\ len <> 0%nat /\
    (ctr <= le_dist)%nat /\
    node_distance base_mem l NULL len /\
    node_distance base_mem l (s R_A0) ctr /\
    cycle_count_of_trace t' = tlw + tlui + taddi +
        tfbeq + (N.of_nat ctr) * (
            taddi + tlw + tlw + ttbgeu
        )
  )
| 0x25c => Some (time_of_insert_in_sorted_list base_mem l value (N.of_nat le_dist) t)
| _ => None end | _ => None end.

Lemma le_cases : forall n m,
    (n <= m -> n < m \/ n = m)%nat.
Proof. lia. Qed.

Lemma not_at_end_next : forall mem head len a dist,
    node_distance mem head NULL len ->
    node_distance mem head a dist ->
    (dist < len)%nat ->
    exists val, list_node_next mem a = Some val.
Proof.
    intros. unfold list_node_next. destruct a.
    - pose proof (node_distance_uniq _ _ _ _ _ H H0).
        subst. lia.
    - eexists. reflexivity.
Qed.

Lemma not_at_end_next' : forall mem head len a1 dist1 a2 dist2,
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

Lemma head_nonnull_impl_len_nonzero : forall mem head len,
    node_distance mem head NULL len ->
    head <> NULL ->
    len <> 0%nat.
Proof.
    intros. destruct len.
    - inversion H. contradiction.
    - discriminate.
Qed.

Lemma at_end_lens : forall mem head len a dst,
    head <> NULL ->
    node_distance mem head NULL len ->
    node_distance mem head a dst ->
    list_node_next mem a = Some NULL ->
    S dst = len.
Proof.
    intros. destruct a.
    - inversion H2.
    - pose proof (node_distance_len_nonzero _ _ _ H0).
        change NULL with LL.NULL in *.
        apply N.eqb_neq in H. rewrite H in H3.
        specialize (H3 ltac:(reflexivity)).
        pose proof distance_last_node.
        unfold LL.NULL in H4.
        specialize (H4 mem head (N.pos p) dst ltac:(lia) H1 H2).
        pose proof (node_distance_uniq _ _ _ _ _ H0 H4).
        now symmetry.
Qed.

Theorem insert_in_sorted_list_timing:
  forall s t s' x' base_mem l value le_node new_val le_val le_dist len sentry
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (A0: s R_A0 = l)
         (A1: s R_A1 = value)
         (MEM: s V_MEM32 = base_mem)
         (* contents of value *)
         (VAL: s V_MEM32 Ⓓ[value] = new_val)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM32) l NULL len)
         (* l is non-null *)
         (L_NN: l <> NULL)
         (* there is a sentry node *)
         (SENTRY: node_distance (s V_MEM32) l sentry (len - 1))
         (SENTRY_VAL: list_node_value (s V_MEM32) sentry = Some INT_MAX)
         (* there is an index to insert at *)
         (IDX: insertion_index base_mem l le_node le_dist le_val new_val len),
  satisfies_all
    lifted_prog
    (insert_in_sorted_list_timing_invs base_mem l value le_node sentry new_val le_val le_dist len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep r5_step.
    simpl. rewrite ENTRY. unfold entry_addr. repeat step.
    split. assumption. repeat split; auto.
    now rewrite A0.
    eapply head_nonnull_impl_len_nonzero; eassumption.
    now rewrite <- MEM.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    - destruct PRE as (IDX & SENTRY & SENTRY_VAL & A0 & A1 & MEM & NonNull & NewVal & L_NN & Len_Nz & Len & Cycles).
        repeat step.
        -- unfold INT_MAX. hammer.
        -- exists 0%nat. split. assumption.
            repeat split; auto; try now rewrite <- MEM. lia.
            rewrite A0. apply Dst0.
            hammer.
    - destruct PRE as (ctr & IDX & SENTRY & SENTRY_VAL & ValueValid & A0 & A1 & A4 & MEM & L_NN & Len_Nz & CtrMax &
                        Len & CtrDist & Cycles).
        repeat step.
        -- hammer. replace ctr with le_dist.
            hammer.
            destruct (le_cases ctr le_dist CtrMax); try lia.
            clear - H CtrDist IDX Len Len_Nz BC A0.
            destruct IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & _ & Vals & _ & Lens & Sorted).
            exfalso.
            pose proof (not_at_end_next _ _ _ _ _ Len CtrDist ltac:(lia)).
            destruct H0 as (a0nxt & a0eq).
            specialize (Sorted a0nxt (S ctr) (base_mem Ⓓ[base_mem Ⓓ[4 + s' R_A0]])).
            pose proof (node_distance_next_S_len _ _ _ _ _ a0eq (distance_null_imp_well_formed _ _ _ Len) CtrDist).
            specialize (Sorted H0).
            enough (list_node_value base_mem a0nxt = Some (base_mem Ⓓ[base_mem Ⓓ[ 4 + s' R_A0 ]])).
            destruct (s' R_A0).
                contradiction.
            specialize (Sorted H1).
            apply N.ltb_lt in BC. lia.
            pose proof (not_at_end_next _ _ _ _ _ Len H0 ltac:(lia)).
            destruct H1 as (a0nxt2 & a0eq2).
            destruct a0nxt eqn:E. inversion a0eq2.
            unfold list_node_value. rewrite <- E in *; clear E.
            replace a0nxt with (base_mem Ⓓ[ 4 + s' R_A0 ]). reflexivity.
            destruct (s' R_A0). contradiction.
                unfold list_node_next in a0eq.
                change 4 with p.dw. remember (p.dw + N.pos p0).
                injection a0eq. now intro.
        -- exists (S ctr). split. assumption.
            destruct IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & GtNN & Vals & MaxVal & Lens & Sorted).
            repeat split; auto; try lia; try now rewrite <- MEM.
            intro Contra.
                replace sentry with (s' R_A0) in *.
                rewrite MEM in *.
                specialize (Sorted _ _ _ SENTRY SENTRY_VAL).
                destruct (Nat.le_gt_cases (len - 1) le_dist). lia.
                assert (S ctr < len)%nat by lia.
                pose proof (at_end_lens _ _ _ _ _ L_NN Len CtrDist).
                destruct H1; try lia.
                destruct (s' R_A0). contradiction. change 4 with p.dw in Contra.
                unfold list_node_next. f_equal. apply Contra.
                pose proof (distance_last_node base_mem l (s' R_A0) ctr A0 CtrDist).
                destruct (s' R_A0). contradiction. unfold list_node_next in H.
                unfold p.w, p.e, p.pw, p.dw in H. rewrite Contra in H.
                specialize (H ltac:(reflexivity)).
                assert (S ctr = len) by eauto using node_distance_uniq.
                subst len. simpl in SENTRY. rewrite Nat.sub_0_r in SENTRY.
                eapply node_distance_uniq'; eauto. now rewrite <- MEM.
            destruct (le_cases ctr le_dist CtrMax). lia.
                subst ctr.
                pose proof (node_distance_uniq' _ _ _ _ _ _ LeDist CtrDist eq_refl).
                subst le_node.
                apply N.ltb_ge in BC.
                (* specialize (Sorted _ _ _ LeDist ltac:(lia) LeVal). *)
                destruct (s' R_A0). contradiction.
                replace gt_node with (base_mem Ⓓ[4 + N.pos p]) in *.
                destruct (base_mem Ⓓ[ 4 + N.pos p ]). contradiction.
                    inversion GtVal. subst gt_val. clear - Vals BC.
                    replace (getmem p.w p.e p.dw base_mem (N.pos p0)) with (base_mem Ⓓ[N.pos p0]) in Vals by reflexivity.
                    lia.
                now inversion LeNextGt.
            eapply node_distance_next_S_len with (dst := s' R_A0).
                destruct (s' R_A0). contradiction. reflexivity.
            eapply distance_null_imp_well_formed. now eassumption.
            assumption.
            hammer.
Qed.

End TimingProof.

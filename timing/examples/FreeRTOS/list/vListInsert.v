Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu: CPUTimingBehavior).

Module Program_vListInsert <: ProgramInformation.
    Definition entry_addr : N := 0x800023f0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80002428 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_vListInsert.

Module RISCVTiming := RISCVTiming cpu Program_vListInsert.
Module vListInsert := RISCVTimingAutomation RISCVTiming.
Import Program_vListInsert vListInsert.

Module p <: LinkedListParams.
  Definition w := 32.
  Definition e := LittleE.
  Definition dw := 8.
  Definition pw := 4.
  Global Transparent w e dw pw.
End p.
Module LL := Theory_RISCV.LinkedLists p.
Import LL.
Ltac psimpl_hook ::= psimpl.
Ltac gdep x := generalize dependent x.
Global Ltac Zify.zify_pre_hook ::= idtac.

Definition portMAX_DELAY := 2^32 - 1.

Definition time_of_vListInsert (mem : memory)
    (pxNewListItem : addr) (le_index : N) (t : trace) :=
  cycle_count_of_trace t =
    tlw + taddi + taddi +
    (if mem Ⓓ[pxNewListItem] =? portMAX_DELAY then (
      tfbne + tlw
    ) else (
      ttbne + le_index * (
        taddi + tlw + tlw + ttbgeu
      ) + taddi + tlw + tlw + tfbgeu + tjal
    )) + (
      tlw + 4 * tsw + tlw + tsw + taddi + tsw + tjalr
    ).

Definition insertion_index mem l le_node le_dist le_val new_val len :=
    exists gt_node gt_val,
    node_distance mem l le_node le_dist /\
    list_node_value mem le_node = Some le_val /\
    list_node_next mem le_node = Some gt_node /\
    list_node_value mem gt_node = Some gt_val /\
    gt_node <> NULL /\
    le_val <= new_val < gt_val /\
    gt_val <= portMAX_DELAY /\
    (le_dist < len)%nat /\
    (* all nodes below le_dist satisfy n.val <= new_val *)
    forall n d v,
        node_distance mem l n d ->
        list_node_value mem n = Some v ->
        ((d <= le_dist)%nat <-> v <= new_val).

Definition vListInsert_timing_invs (base_mem : memory)
    (pxList pxNewListItem le_node sentry : addr) 
    (new_val le_val : N)
    (le_dist len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800023f0 => Some (
    insertion_index base_mem pxList le_node le_dist le_val new_val len /\
    node_distance (s V_MEM32) pxList sentry (len - 1) /\
    list_node_value (s V_MEM32) sentry = Some portMAX_DELAY /\
    s R_A0 = pxList /\ s R_A1 = pxNewListItem /\ s V_MEM32 = base_mem /\
    s V_MEM32 Ⓓ[pxNewListItem] = new_val /\
    pxList <> NULL /\ len <> 0%nat /\
    node_distance base_mem pxList NULL len /\
    cycle_count_of_trace t' = 0
  )
| 0x8000242c => Some (exists ctr,
    insertion_index base_mem pxList le_node le_dist le_val new_val len /\
    node_distance (s V_MEM32) pxList sentry (len - 1) /\
    list_node_value (s V_MEM32) sentry = Some portMAX_DELAY /\
    (base_mem Ⓓ[pxNewListItem] =? portMAX_DELAY) = false /\
    s R_A0 <> NULL /\
    pxList <> NULL /\ s V_MEM32 = base_mem /\
    s R_A1 = pxNewListItem /\ s R_A3 = new_val /\
    len <> 0%nat /\
    (ctr <= le_dist)%nat /\
    node_distance base_mem pxList NULL len /\
    node_distance base_mem pxList (s R_A0) ctr /\
    cycle_count_of_trace t' =
      tlw + taddi + taddi +
      ttbne + (N.of_nat ctr) * (
        taddi + tlw + tlw + ttbgeu
      )
  )
| 0x80002428 => Some (time_of_vListInsert base_mem
                    pxNewListItem (N.of_nat le_dist) t)
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

Theorem vListInsert_timing:
  forall s t s' x' base_mem len pxList pxNewListItem le_node le_dist le_val sentry new_val
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = pxList)
         (A1: s R_A1 = pxNewListItem)
         (* contents of pxNewListItem *)
         (VAL: s V_MEM32 Ⓓ[pxNewListItem] = new_val)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM32) pxList NULL len)
         (* pxList is non-null *)
         (L_NN: pxList <> NULL)
         (* there is a sentry node *)
         (SENTRY: node_distance (s V_MEM32) pxList sentry (len - 1))
         (SENTRY_VAL: list_node_value (s V_MEM32) sentry = Some portMAX_DELAY)
         (* there is an index to insert at *)
         (IDX: insertion_index base_mem pxList le_node le_dist le_val new_val len),
  satisfies_all
    lifted_prog
    (vListInsert_timing_invs base_mem pxList pxNewListItem le_node sentry new_val le_val le_dist len)
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

    - destruct PRE as (IDX & SENTRY & SENTRY_VAL & A0 & A1 & MEM & NewVal & NonNull & L_NN & Len_Nz & Cycles).
        do 4 step.
        -- exists 0%nat. split. assumption.
            repeat split; auto; try now rewrite <- MEM.
            unfold portMAX_DELAY. lia. lia.
            apply Dst0.
            hammer.
        -- repeat step. unfold portMAX_DELAY. hammer.
    - destruct PRE as (ctr & IDX & SENTRY & SENTRY_VAL & ValueValid & A0 & L_NN & MEM & A1 & A3 & Len_Nz & CtrMax &
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
                destruct (N.pos p). contradiction. now inversion LeNextGt.
            eapply node_distance_next_S_len with (dst := s' R_A0).
                destruct (s' R_A0). contradiction. reflexivity.
            eapply distance_null_imp_well_formed. now eassumption.
            assumption.
            hammer.
Admitted.

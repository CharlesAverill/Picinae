From Picinae.timing.examples.arm_wcet_comparison.llsearch Require Import insert_in_sorted_list_lifted.
Require Import ARMv6MTiming.
Import ARMv6MNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : ARMv6MCPUTimingBehavior).
Import cpu.

Module p <: LinkedListParams.
  Definition w := 32.
  Definition e := LittleE.
  Definition dw := 4.
  Definition pw := 4.
  Global Transparent w e dw pw.
End p.
Module LL := Theory_ARMv6M.LinkedLists p.
Import LL.
Ltac psimpl_hook ::= psimpl.
Ltac gdep x := generalize dependent x.
Global Ltac Zify.zify_pre_hook ::= idtac.

Module Program_insert_in_sorted_list <: ProgramInformation.
    Definition entry_addr : N := 0x8000044.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800005c => true
        | _ => false
    end | _ => false end.

    Definition binary := linked_list_insert_in_sorted_list_armv6m.
End Program_insert_in_sorted_list.

Module ARMv6MTiming := ARMv6MTiming cpu Program_insert_in_sorted_list.
Module insert_in_sorted_listAuto := ARMv6MTimingAutomation ARMv6MTiming.
Import Program_insert_in_sorted_list insert_in_sorted_listAuto.

Definition optN_eqb (x y : option N) : bool :=
    match x, y with
    | Some x, Some y => N.eqb x y
    | None, None => true
    | _, _ => false
    end.

Lemma optN_eqb_refl : forall x, optN_eqb x x = true.
Proof.
    intros. unfold optN_eqb. destruct x.
        apply N.eqb_refl.
    reflexivity.
Qed.

Lemma optN_eqb_None_Some : forall n,
    optN_eqb None (Some n) = false.
Proof. reflexivity. Qed.

Definition INT_MAX : N := 2^31 - 1.

Definition time_of_insert_in_sorted_list
    (mem : memory) (l value : addr) (max_dist : N) (t : trace) :=
  cycle_count_of_trace t =
    tldr_imm + tldr_pc + (tpush_base + 1 + 1) + tcmp_reg +
    if optN_eqb (list_node_value mem value) (Some INT_MAX) then (
        tb_taken + tmovs_reg + tldr_imm + tb +
        tstr_imm + tstr_imm + (tpop_pc_base + 2)
    ) else (
        tb_not_taken +
        (* nodes passed over *)
        max_dist * (
            tmovs_reg + tldr_imm + tldr_imm + tcmp_reg + tb_taken
        ) +
        (* the node after which value is inserted *)
        tmovs_reg + tldr_imm + tldr_imm + tcmp_reg + tb_not_taken +
        tstr_imm + tstr_imm + (tpop_pc_base + 2)
    ).

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

Definition insert_in_sorted_list_timing_invs
    (l value sentry le_node : addr) (len le_dist : nat)
    (new_val le_val : N) (lmin lmax : N) (base_mem : memory) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000044 => Some (
        insertion_index base_mem l le_node le_dist le_val new_val len /\
        s R_R0 = l /\ s R_R1 = value /\
        s V_MEM32 = base_mem /\
        node_distance (s V_MEM32) l sentry (len - 1) /\
        list_node_value (s V_MEM32) sentry = Some INT_MAX /\
        s R_R0 <> NULL /\
        s V_MEM32 Ⓓ[value] = new_val /\
        l <> NULL /\ len <> 0%nat /\
        value <> NULL /\
        node_distance base_mem l NULL len /\
        LLBounds base_mem l lmin lmax /\
        ~ overlap 32 (s R_SP ⊖ 8) 8 lmin (8 + lmax - lmin) /\
        cycle_count_of_trace t' = 0
    )
| 0x800004e => Some (exists ctr,
        insertion_index base_mem l le_node le_dist le_val new_val len /\
        node_distance base_mem l sentry (len - 1) /\
        list_node_value base_mem sentry = Some INT_MAX /\
        optN_eqb (list_node_value base_mem value) (Some INT_MAX) = false /\
        s R_R0 <> NULL /\
        s R_R1 = value /\ s R_R2 = new_val /\
        (* the list is unchanged by the registers pushed on entry *)
        LLSame base_mem (s V_MEM32) l /\
        l <> NULL /\ len <> 0%nat /\
        (ctr <= le_dist)%nat /\
        node_distance base_mem l NULL len /\
        node_distance base_mem l (s R_R0) ctr /\
        cycle_count_of_trace t' =
            tldr_imm + tldr_pc + (tpush_base + 1 + 1) + tcmp_reg + tb_not_taken +
            (N.of_nat ctr) * (
                tmovs_reg + tldr_imm + tldr_imm + tcmp_reg + tb_taken
            )
    )
| 0x800005c => Some (
    time_of_insert_in_sorted_list base_mem l value (N.of_nat le_dist) t
)
| _ => None end | _ => None end.

(* The two words pushed on entry don't change the list. *)
Lemma push2_llsame :
    forall mem sp l lmin lmax v1 v2
        (LLB: LLBounds mem l lmin lmax)
        (NO: ~ overlap 32 (sp ⊖ 8) 8 lmin (8 + lmax - lmin)),
    LLSame mem (mem [Ⓓ sp ⊖ 8 := v1] [Ⓓ sp ⊖ 4 := v2]) l.
Proof.
    intros.
    assert (SP: sp ⊖ 4 = ((sp ⊖ 8) + 4) mod 2^32). {
        unfold msub. rewrite N.Div0.add_mod_idemp_l. f_equal.
        rewrite (N.mod_small 4), (N.mod_small 8) by lia. lia.
    }
    replace (8 + lmax - lmin) with (lmax + 4 + 4 - lmin) in NO by lia.
    apply noverlap_llsame_llbounds_trans with (min := lmin) (max := lmax); try assumption.
        apply noverlap_llsame_llbounds with (min := lmin) (max := lmax); try assumption.
        eapply noverlap_index_l with (index := 0) (size := 4) in NO; [| lia].
        rewrite N.add_0_r in NO. exact NO.
    rewrite SP, overlap_mod_l.
    apply noverlap_index_l with (len1 := 8); [ exact NO | lia ].
Qed.

(* Reads of the nodes of a list from a memory with the same list. *)
Lemma llsame_reads :
    forall m m' l n d
        (SAME: LLSame m m' l) (DIST: node_distance m l n d) (NN: n <> NULL),
    m' Ⓓ[n] = m Ⓓ[n] /\ m' Ⓓ[4 + n] = m Ⓓ[4 + n].
Proof.
    intros. revert m' SAME. induction DIST; intros.
    - inversion SAME; subst. contradiction.
        destruct node. contradiction.
        unfold list_node_value, list_node_next in *.
        injection H as H. injection H0 as H0. split; symmetry; assumption.
    - inversion SAME; subst. discriminate.
        rewrite NEXT in H1. injection H1 as H1. subst next0.
        apply IHDIST; assumption.
Qed.

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
    - pose proof (node_distance_uniq H H0).
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
    - pose proof (node_distance_uniq H H1).
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
        pose proof (node_distance_uniq H0 H4).
        now symmetry.
Qed.

Theorem insert_in_sorted_list_timing:
  forall s t s' x' l value len base_mem new_val sentry le_node le_dist le_val lmin lmax
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models armv6mtypctx s)
         (* bindings *)
         (R0: s R_R0 = l)
         (R1: s R_R1 = value)
         (MEM: s V_MEM32 = base_mem)
         (* contents of value *)
         (VAL: s V_MEM32 Ⓓ[value] = new_val)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM32) l NULL len)
         (* l is non-null *)
         (L_NN: l <> NULL)
         (V_NN: value <> NULL)
         (* there is a sentry node *)
         (SENTRY: node_distance (s V_MEM32) l sentry (len - 1))
         (SENTRY_VAL: list_node_value (s V_MEM32) sentry = Some INT_MAX)
         (* there is an index to insert at *)
         (IDX: insertion_index base_mem l le_node le_dist le_val new_val len)
         (* the registers pushed on entry don't overwrite the list *)
         (BOUNDS: LLBounds base_mem l lmin lmax)
         (NO: ~ overlap 32 (s R_SP ⊖ 8) 8 lmin (8 + lmax - lmin)),
  satisfies_all
    lifted_prog
    (insert_in_sorted_list_timing_invs l value sentry le_node len le_dist new_val le_val lmin lmax base_mem)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep armv6m_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto; try lia.
    eapply head_nonnull_impl_len_nonzero; eassumption.
    now rewrite <- MEM.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped_lift_armv6m].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.
    - destruct PRE as (IDX & R0 & R1 & MEM & SENTRY & SENTRY_VAL & NonNull &
            NewVal & L_NN & Len_Nz & V_NN & Len & BOUNDS & NO & Cycles).
        assert (LV: list_node_value base_mem value = Some (base_mem Ⓓ[value])).
            destruct value. contradiction. reflexivity.
        repeat step.
        -- (* value = INT_MAX: insert after the head *)
            unfold time_of_insert_in_sorted_list. rewrite LV.
            unfold optN_eqb, INT_MAX. change (2^31 - 1) with 2147483647.
            hammer.
        -- (* loop entry *)
            exists 0%nat. split. assumption.
            rewrite MEM in *; repeat split; auto; try lia.
            rewrite LV. unfold optN_eqb, INT_MAX. change (2^31 - 1) with 2147483647. assumption.
            apply push2_llsame with (lmin := lmin) (lmax := lmax); assumption.
            rewrite R0. apply Dst0.
            hammer.
            rewrite (N.mod_small new_val) by (rewrite <- NewVal; apply getmem_bound).
            rewrite <- NewVal, BC. lia.
    - destruct PRE as (ctr & IDX & SENTRY & SENTRY_VAL & ValueValid & NonNull & R1 &
            R2 & SAME & L_NN & Len_Nz & CtrMax & Len & CtrDist & Cycles).
        pose proof IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & GtNN &
            Vals & MaxVal & Lens & Sorted).
        pose proof (distance_null_imp_well_formed _ _ _ Len) as WF.
        (* the next node is at distance ctr + 1, and is not NULL *)
        assert (NEXTD: node_distance base_mem l (base_mem Ⓓ[4 + s' R_R0]) (S ctr)).
            eapply node_distance_next_S_len; try eassumption.
            destruct (s' R_R0). contradiction. reflexivity.
        assert (LEDIST: (S le_dist < len)%nat). {
            pose proof (node_distance_next_S_len _ _ _ _ _ LeNextGt WF LeDist) as GTD.
            pose proof (dist_node_le_dist_null _ _ _ _ _ Len GTD).
            destruct (Nat.eq_dec (S le_dist) len); [| lia].
            exfalso. apply GtNN. apply (node_distance_uniq' GTD Len). assumption.
        }
        assert (NEXTNN: base_mem Ⓓ[4 + s' R_R0] <> NULL).
            eapply dist_lt_null_not_null; try eassumption. lia.
        (* the list's nodes read the same as in base_mem *)
        destruct (llsame_reads _ _ _ _ _ SAME CtrDist NonNull) as (_ & READ1).
        destruct (llsame_reads _ _ _ _ _ SAME NEXTD NEXTNN) as (READ2 & _).
        assert (NV: list_node_value base_mem (base_mem Ⓓ[4 + s' R_R0]) =
                    Some (base_mem Ⓓ[base_mem Ⓓ[4 + s' R_R0]])).
            destruct (base_mem Ⓓ[4 + s' R_R0]). contradiction. reflexivity.
        repeat step.
        all: rewrite ?READ1 in *; rewrite ?READ2 in *.
        -- (* the next node's value is <= new_val: move to it *)
            apply N.leb_le in BC.
            exists (S ctr). split. assumption.
            repeat split; auto; try lia.
            apply (Sorted _ _ _ NEXTD NV). assumption.
            hammer.
        -- (* the next node's value is > new_val: insert here *)
            apply N.leb_gt in BC.
            assert (ctr = le_dist). {
                destruct (le_cases ctr le_dist CtrMax); [| assumption].
                exfalso. apply (Sorted _ _ _ NEXTD NV) in H. lia.
            }
            subst ctr.
            unfold time_of_insert_in_sorted_list. hammer.
Qed.

End TimingProof.

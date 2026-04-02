Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : RVCPUTimingBehavior).

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
  Definition dw := 4.
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

(* Try the proof again with these changes. *)
Definition insertion_index mem l le_node le_dist le_val new_val len :=
    exists gt_node gt_val,
    node_distance mem l le_node le_dist /\
    list_node_value mem le_node = Some le_val /\
    list_node_next mem le_node = Some gt_node /\
    list_node_value mem gt_node = Some gt_val /\
    gt_node <> NULL /\
    new_val < gt_val /\
    gt_val <= portMAX_DELAY /\
    (le_dist <= len)%nat /\
    (* all nodes below le_dist satisfy n.val <= new_val *)
    match len with
    | S _ =>
        match le_dist with
        | O => True
        | S _ =>
        le_val <= new_val /\
        forall n d v h,
            list_node_next mem l = Some h ->
            node_distance mem h n d ->
            list_node_value mem n = Some v ->
            ((d < le_dist)%nat <-> v <= new_val)
        end
    | _ => True
    end.

Definition vListInsert_timing_invs (base_mem : memory)
    (pxList pxListHead pxNewListItem le_node sentry : addr)
    (new_val le_val : N)
    (le_dist len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800023f0 => Some (
    insertion_index base_mem sentry le_node le_dist le_val new_val len /\
    node_distance base_mem pxListHead sentry (len) /\
    list_node_value base_mem sentry = Some portMAX_DELAY /\
    list_node_next base_mem sentry = Some pxListHead /\
    s R_A0 = pxList /\ s R_A1 = pxNewListItem /\ s V_MEM32 = base_mem /\
    s V_MEM32 Ⓓ[pxNewListItem] = new_val /\
    pxList ⊕ 8 = sentry /\
    pxListHead <> NULL /\
    sentry <> NULL /\
    cycle_count_of_trace t' = 0
  )
(* ctr is the number of nodes past the sentry we have seen are less than
   new_val. At the end of the loop ctr is le_dist and register R_A4 holds
   the first node with a value greater than new_val. *)
| 0x8000242c => Some (exists ctr curr,
    s R_A4 = curr /\
    insertion_index base_mem sentry le_node le_dist le_val new_val len /\
    node_distance base_mem pxListHead sentry (len) /\
    list_node_next base_mem sentry = Some pxListHead /\
    list_node_value base_mem sentry = Some portMAX_DELAY /\
    (base_mem Ⓓ[pxNewListItem] =? portMAX_DELAY) = false /\
    pxListHead <> NULL /\ s V_MEM32 = base_mem /\
    s R_A1 = pxNewListItem /\ s R_A3 = new_val /\
    (ctr <= le_dist)%nat /\
    node_distance base_mem sentry curr ctr /\
    sentry <> NULL /\
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

Lemma Some_inv : forall (X : Type) (x y : X),
    Some x = Some y -> x = y.
Proof. intros. now inversion H. Qed.

Lemma no_dist_from_null:
    forall mem node len,
        node <> NULL ->
        ~ node_distance mem NULL node len.
Proof.
    intros. intro Contra. inversion Contra; subst.
        contradiction.
    inversion NEXT.
Qed.

Theorem list_node_next_eq {m a b c}:
    list_node_next m a = Some b ->
    list_node_next m a = Some c ->
  c = b.
Proof.
  intros B C; rewrite C in B; inversion B; easy.
Qed.

Theorem vListInsert_timing:
  forall s t s' x' base_mem len pxList pxListHead pxNewListItem le_node le_dist le_val sentry new_val
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = pxList)
         (A1: s R_A1 = pxNewListItem)
         (* contents of pxNewListItem *)
         (VAL: s V_MEM32 Ⓓ[pxNewListItem] = new_val)
         (* pxListHead is non-null *)
         (L_NN: pxListHead <> NULL)
         (* there is a sentry node *)
         (HD: 8 ⊕ pxList = sentry)
         (SENTRY: node_distance base_mem pxListHead sentry (len))
         (SENTRY_VAL: list_node_value base_mem sentry = Some portMAX_DELAY)
         (SENTRY_NEXT: list_node_next base_mem sentry = Some pxListHead)
         (SENTRY_NN: sentry <> NULL)
         (* there is an index to insert at *)
         (IDX: insertion_index base_mem sentry le_node le_dist le_val new_val len),
  satisfies_all
    lifted_prog
    (vListInsert_timing_invs base_mem pxList pxListHead pxNewListItem le_node sentry new_val le_val le_dist len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep r5_step.
    simpl. rewrite ENTRY. unfold entry_addr. repeat step.
    split. assumption. repeat split; auto.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    - destruct PRE as (IDX & SENTRY & SENTRY_VAL & SENTRY_NEXT & A0 & A1 & MEM &
        NewVal & PXLH & NonNull & SENTRY_NN & Cycles).
        do 4 step.
        -- exists 0%nat, sentry. split. rewrite N.add_comm, PXLH; reflexivity.
            repeat split; auto; try now rewrite <- MEM.
            unfold portMAX_DELAY. lia. lia.
            constructor.
            hammer.
        -- repeat step. unfold portMAX_DELAY. hammer.
    - destruct PRE as (ctr & nxt & A4 & IDX & SENTRY & SENTRY_NEXT & SENTRY_VAL & ValueValid & PXLH_NN &
            MEM & A1 & A3 & CtrMax & CtrDist & S_NN & Cycles).
        repeat step.
        -- (* post condition, prove timing property. *)
            hammer.
            unfold insertion_index in IDX.
            destruct IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & GtNNull & NewLtGt & GtLeMax & Lens & Sorted).
            destruct le_dist as [|le_dist']; only 1: (destruct ctr; lia).
            destruct len; try lia.
            destruct Sorted as [LeNew Sorted].
            replace ctr with (S le_dist'). lia.
            destruct (le_cases ctr (S le_dist') CtrMax); try lia.
            erewrite <-(Sorted _ _ _ _ _ LeDist LeVal) in LeNew.
            Unshelve. lia.
            clear Cycles tail ACC A4 A3 A1 MEM ENTRY.
            rewrite N.ltb_lt in BC.
            enough (NXT':exists nxt', list_node_next base_mem nxt = Some nxt').
            destruct NXT' as [nxt' NXT'].
            assert (Help:node_distance base_mem sentry pxListHead (S O)). repeat (econstructor || eassumption).
              intro. subst pxListHead. inversion SENTRY; now subst.
            pose proof (H0:=cycle_distance_two_step SENTRY_NEXT SENTRY (Dst0 _ _) CtrDist SENTRY_NEXT NXT').
            assert (list_node_value base_mem nxt' = Some (base_mem Ⓓ[ base_mem Ⓓ[ 4 + nxt ] ])). {
              unfold list_node_value, list_node_next, p.e, p.w, p.dw, p.pw in NXT' |- *. destruct nxt; try discriminate. destruct nxt'; try discriminate.
              exfalso; apply (@cycle_imp_null_no_dist (S ctr) _ _ _ SENTRY_NEXT (distance_imp_in SENTRY)).
              econstructor; try eassumption.
              apply Some_inv in NXT'; rewrite NXT'; reflexivity.
            }
            specialize (Sorted _ _ _ _ SENTRY_NEXT H0 H1). rewrite Sorted in H. lia.

            destruct nxt; try discriminate; try (eexists; reflexivity).
            exfalso; eapply (cycle_imp_null_no_dist); try eassumption. eapply distance_imp_in; eassumption.
        --  exists (S ctr).
            rewrite A1 in *; clear MEM A1 A4 ENTRY.
            assert (IDX':=IDX).
            unfold insertion_index in IDX;
            destruct IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & GtNNull & NewLtGt & GtLeMax & Lens & Sorted).
            rewrite N.ltb_ge in BC.
            destruct len as [|len'] eqn:EQlen;[clear Sorted|]; destruct le_dist as [|le_dist'] eqn:EQle_dist; try lia. destruct ctr; try lia.
            inversion LeDist; inversion CtrDist; subst; rename nxt into sentry.
            (* ctr = le_dist = = len = 0: inserting in 0-length list; contradiction because we could not have iterated *)
            (* TODO: add a lia preprocessor to automate this. *)
            inversion SENTRY; subst. rewrite SENTRY_NEXT in LeNextGt; inversion LeNextGt; subst gt_node.
            unfold list_node_next in SENTRY_NEXT;
            unfold list_node_value in GtVal; destruct sentry; try contradiction; unfold p.w, p.e, p.dw, p.pw in *.
            apply Some_inv in SENTRY_NEXT, GtVal. rewrite SENTRY_NEXT in BC. rewrite GtVal in *. lia.
            (* ctr = le_dist = 0; 0 < len: inserting right after sentry, find contradiction somewhere? *)
            inversion CtrDist; subst nxt; subst; try lia.
            exfalso; clear tail Cycles CtrMax CtrDist Lens Sorted.
            inversion LeDist; subst le_node; inversion SENTRY; subst.
            rewrite LeNextGt in SENTRY_NEXT; inversion SENTRY_NEXT; subst pxListHead.
            unfold list_node_next, p.w, p.e, p.dw, p.pw in LeNextGt. destruct sentry as [|p]; try contradiction; remember (N.pos p) as sentry.
            apply Some_inv in LeNextGt. rewrite LeNextGt in *.
            unfold list_node_value, p.w, p.e, p.dw, p.pw in GtVal. destruct gt_node as [|p0]; try contradiction; remember (N.pos p0) as gt_node.
            apply Some_inv in GtVal; rewrite GtVal in *; lia.
            (* ctr = le_dist = 0; 0 <= len: iterating to find le_dist. *)
            eexists. split; try reflexivity.
            repeat (eassumption || lia || split); clear IDX'.
            destruct (Nat.lt_trichotomy ctr (S le_dist')) as [Lt | [Eq | Gt]]; try lia.
            rewrite <-Eq in *; exfalso.
            destruct Sorted as [LeNv Sorted]. clear Cycles tail.
            enough (H:exists nxt', list_node_next base_mem nxt = Some nxt').
            destruct H as [nxt' NXT'].
            pose proof (H:=cycle_distance_step SENTRY_NEXT SENTRY CtrDist NXT').
            destruct H as [EQ | DstNxt'].
              subst nxt'. unfold list_node_next, list_node_value, p.w, p.e, p.pw, p.dw in NXT', SENTRY_VAL. destruct nxt; try discriminate.
              destruct sentry; try discriminate. apply Some_inv in NXT', SENTRY_VAL. rewrite NXT', SENTRY_VAL in *. lia.

              clear Eq; inversion DstNxt'; subst. align_next.
              unfold list_node_next, p.w, p.e, p.dw, p.pw in NXT'. destruct nxt; try discriminate. apply Some_inv in NXT'. rewrite NXT' in BC.
              assert (Help:list_node_value base_mem nxt' = Some (base_mem Ⓓ[ nxt' ])). { unfold list_node_value, p.w, p.e, p.dw. destruct nxt'; try discriminate.
              eapply (cycle_imp_null_no_dist SENTRY_NEXT) in DstNxt'. contradiction. eapply distance_imp_in; eassumption.
              reflexivity. }
              specialize (Sorted _ _ _ _ SENTRY_NEXT LEN Help). rewrite <-Sorted in BC; lia.

              destruct nxt; try (eexists; reflexivity).
              eapply (cycle_imp_null_no_dist SENTRY_NEXT) in CtrDist. contradiction. eapply distance_imp_in; eassumption.

            (* we can combine this with the above somehow - we do the same case analysis twice. *)
            destruct Sorted as [LeNv Sorted]. clear Cycles tail.
            enough (H:exists nxt', list_node_next base_mem nxt = Some nxt').
            destruct H as [nxt' NXT'].
            pose proof (cycle_distance_step SENTRY_NEXT SENTRY CtrDist NXT').
            destruct H as [EQ | DstNxt'].
              subst nxt'. unfold list_node_next, list_node_value, p.w, p.e, p.pw, p.dw in NXT', SENTRY_VAL. destruct nxt; try discriminate.
              destruct sentry; try discriminate. apply Some_inv in NXT', SENTRY_VAL. rewrite NXT', SENTRY_VAL in *. lia.

              unfold list_node_next, p.w, p.e, p.dw, p.pw in NXT'. destruct nxt; try discriminate; apply Some_inv in NXT'; rewrite NXT' in *; assumption.

              destruct nxt; try (eexists; reflexivity).
              eapply (cycle_imp_null_no_dist SENTRY_NEXT) in CtrDist. contradiction. eapply distance_imp_in; eassumption.


              hammer. rewrite <-N.leb_le, N.leb_antisym in BC. hammer.
Qed.

End TimingProof.

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal forall mem t pxNewListItem le_addr,
    time_of_vListInsert mem pxNewListItem le_addr t = 
    (vListInsert.cycle_count_of_trace t =
      23 +
      (if mem Ⓓ[ pxNewListItem ] =? portMAX_DELAY
        then 15 + T_data_latency + T_data_latency
        else
        31 + T_data_latency + T_inst_latency +
        le_addr * (15 + 2 * T_data_latency + T_inst_latency) +
        2 * T_data_latency + T_inst_latency) + T_data_latency +
      4 * (4 + T_data_latency) + T_data_latency + 2 * T_data_latency +
      T_inst_latency).
Proof.
    intros. unfold time_of_vListInsert.
    unfold tlw, tsw, taddi, tfbne, ttbne, ttbgeu, tfbgeu, tjal, tjalr.
    psimpl. repeat rewrite <- N.add_assoc.
    replace (15 + (T_data_latency + (T_data_latency + T_inst_latency))) with
      (15 + 2 * T_data_latency + T_inst_latency) by lia.
    replace (T_data_latency + (T_data_latency + T_inst_latency)) with
      (2 * T_data_latency + T_inst_latency) by lia.
    psimpl. psimpl. reflexivity.
Qed.

Require Import insert_in_sorted_list_lifted.
Require Import AMD64Timing.
Import X64Notations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : amd64CPUTimingBehavior).
Import cpu.

Module p <: LinkedListParams.
  Definition w := 64.
  Definition e := LittleE.
  Definition dw := 8.
  Definition pw := 8.
  Global Transparent w e dw pw.
End p.
Module LL := Theory_amd64.LinkedLists p.
Import LL.
Ltac psimpl_hook ::= psimpl.
Ltac gdep x := generalize dependent x.
Global Ltac Zify.zify_pre_hook ::= idtac.

Module Program_insert_in_sorted_list <: ProgramInformation.
    Definition entry_addr : N := 0x0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x24 | 0x37 => true
        | _ => false
    end | _ => false end.

    Definition time_of_addr (s : store) (a : addr) : N :=
        match a with
        (* 0x0: MOV RAX,[RSI] *)
        | 0x0  => mov_r64_m64
        (* 0x3: CMP RAX,0x7fffffff *)
        | 0x3  => cmp_r64_i
        (* 0x9: JZ 0x00101388 *)
        | 0x9  => jz_addr
        (* 0xb: NOP dword ptr [RAX + RAX*0x1] *)
        | 0xb  => nop
        (* 0x10: MOV RDX,RDI *)
        | 0x10 => mov_r64_r64
        (* 0x13: MOV RDI,[RDI + 0x8] *)
        | 0x13 => mov_r64_m64
        (* 0x17: CMP RAX,[RDI] *)
        | 0x17 => cmp_r64_m64
        (* 0x1a: JNC 0x00101370 *)
        | 0x1a => jnc_addr
        (* 0x1c: MOV [RSI + 0x8],RDI *)
        | 0x1c => mov_m64_r64
        (* 0x20: MOV [RDX + 0x8],RSI *)
        | 0x20 => mov_m64_r64
        (* 0x24: RET *)
        | 0x24 => ret

        (* 0x28: MOV RDX,RDI *)
        | 0x28 => mov_r64_r64
        (* 0x2b: MOV RDI,[RDI + 0x8] *)
        | 0x2b => mov_r64_m64
        (* 0x2f: MOV [RSI + 0x8],RDI *)
        | 0x2f => mov_m64_r64
        (* 0x33: MOV [RDX + 0x8],RSI *)
        | 0x33 => mov_m64_r64
        (* 0x37: RET *)
        | 0x37 => ret

        | _ => time_inf
        end.

    Definition lifted_prog := linked_list_insert_in_sorted_list_amd64.
End Program_insert_in_sorted_list.

Module AMD64Timing := AMD64Timing cpu Program_insert_in_sorted_list.
Module insert_in_sorted_listAuto := AMD64TimingAutomation AMD64Timing.
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
  cycle_count_of_trace t <=
    mov_r64_m64 + cmp_r64_i + jz_addr +
    if optN_eqb (list_node_value mem value) (Some INT_MAX) then (
        mov_r64_r64 + mov_r64_m64 + mov_m64_r64 + mov_m64_r64 + ret
    ) else (
        nop + (1 + max_dist) * (
            mov_r64_r64 + mov_r64_m64 + cmp_r64_m64 + jnc_addr
        ) + mov_m64_r64 + mov_m64_r64 + ret
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
    (new_val le_val : N) (base_mem : memory) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x0 => Some (
        insertion_index base_mem l le_node le_dist le_val new_val len /\
        s R_RDI = l /\ s R_RSI = value /\
        s V_MEM64 = base_mem /\
        node_distance (s V_MEM64) l sentry (len - 1) /\
        list_node_value (s V_MEM64) sentry = Some INT_MAX /\
        s R_RDI <> NULL /\
        s V_MEM64 Ⓠ[value] = new_val /\
        l <> NULL /\ len <> 0%nat /\
        value <> NULL /\
        node_distance base_mem l NULL len /\
        cycle_count_of_trace t' = 0
    )
| 0x10 => Some (exists ctr,
        insertion_index base_mem l le_node le_dist le_val new_val len /\
        node_distance (s V_MEM64) l sentry (len - 1) /\
        list_node_value (s V_MEM64) sentry = Some INT_MAX /\
        optN_eqb (list_node_value base_mem value) (Some 2147483647) = false /\
        s R_RDI <> NULL /\
        s R_RSI = value /\ s R_RAX = new_val /\ s V_MEM64 = base_mem /\
        l <> NULL /\ len <> 0%nat /\
        (ctr <= le_dist)%nat /\
        node_distance base_mem l NULL len /\
        node_distance base_mem l (s R_RDI) ctr /\
        cycle_count_of_trace t' <=
            mov_r64_m64 + cmp_r64_i + jz_addr +
            nop + (N.of_nat ctr) * (
                mov_r64_r64 + mov_r64_m64 + cmp_r64_m64 + jnc_addr
            )
    )
| 0x24 | 0x37 => Some (
    time_of_insert_in_sorted_list base_mem l value (N.of_nat le_dist) t
)
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

Theorem insert_in_sorted_list_timing:
  forall s t s' x' l value len base_mem new_val sentry le_node le_dist le_val
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models x64typctx s)
         (* bindings *)
         (RDI: s R_RDI = l)
         (RSI: s R_RSI = value)
         (MEM: s V_MEM64 = base_mem)
         (* contents of value *)
         (VAL: s V_MEM64 Ⓠ[value] = new_val)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM64) l NULL len)
         (* l is non-null *)
         (L_NN: l <> NULL)
         (V_NN: value <> NULL)
         (* there is a sentry node *)
         (SENTRY: node_distance (s V_MEM64) l sentry (len - 1))
         (SENTRY_VAL: list_node_value (s V_MEM64) sentry = Some INT_MAX)
         (* there is an index to insert at *)
         (IDX: insertion_index base_mem l le_node le_dist le_val new_val len),
  satisfies_all
    lifted_prog
    (insert_in_sorted_list_timing_invs l value sentry le_node len le_dist new_val le_val base_mem)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep x64_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto; try lia.
    eapply head_nonnull_impl_len_nonzero; eassumption.
    now rewrite <- MEM.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 64 PRE.
    - destruct PRE as (IDX & RDI & RSI & MEM & SENTRY & SENTRY_VAL & NonNull & 
            NewVal & L_NN & Len_Nz & V_NN & Len & Cycles).
        repeat step.
        -- unfold NULL. destruct (list_node_value base_mem value) eqn:E.
            destruct value. inversion E.
                simpl in E. apply Some_inv in E.
                apply N.eqb_eq in BC.
                unfold p.w, p.e, p.dw in E. rewrite E in BC.
                rewrite BC. rewrite optN_eqb_refl. hammer.
                rewrite optN_eqb_None_Some. hammer.
        -- exists 0%nat. split. assumption.
            rewrite <- MEM in *; repeat split; auto; try lia.
            destruct value. contradiction. simpl.
                now unfold p.w, p.e, p.dw.
            rewrite RDI. apply Dst0.
            hammer.
    - destruct PRE as (ctr & IDX & SENTRY & SENTRY_VAL & ValueValid & RDI & RSI & 
            RAX & MEM & L_NN & Len_Nz & CtrMax & Len & CtrDist & Cycles).
        repeat step.
        -- hammer. replace ctr with le_dist in Cycles. lia.
            destruct (le_cases ctr le_dist CtrMax); try lia.
            clear - H CtrDist IDX Len Len_Nz BC RDI.
            destruct IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & _ & Vals & _ & Lens & Sorted).
            exfalso.
            pose proof (not_at_end_next _ _ _ _ _ Len CtrDist ltac:(lia)).
            destruct H0 as (a0nxt & a0eq).
            specialize (Sorted a0nxt (S ctr) (base_mem Ⓠ[base_mem Ⓠ[8 + s' R_RDI]])).
            pose proof (node_distance_next_S_len _ _ _ _ _ a0eq (distance_null_imp_well_formed _ _ _ Len) CtrDist).
            specialize (Sorted H0).
            enough (list_node_value base_mem a0nxt = Some (base_mem Ⓠ[base_mem Ⓠ[ 8 + s' R_RDI ]])).
            destruct (s' R_RDI).
                contradiction.
            specialize (Sorted H1).
            apply N.ltb_lt in BC. lia.
            pose proof (not_at_end_next _ _ _ _ _ Len H0 ltac:(lia)).
            destruct H1 as (a0nxt2 & a0eq2).
            destruct a0nxt eqn:E. inversion a0eq2.
            unfold list_node_value. rewrite <- E in *; clear E.
            replace a0nxt with (base_mem Ⓠ[ 8 + s' R_RDI ]). reflexivity.
            destruct (s' R_RDI). contradiction.
                unfold list_node_next in a0eq. apply Some_inv in a0eq.
            apply a0eq.
        -- exists (S ctr). split. assumption.
            destruct IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & GtNN & Vals & MaxVal & Lens & Sorted).
            rewrite <- MEM in *; repeat split; auto; try lia.
            intro Contra.
                replace sentry with (s' R_RDI) in *.
                rewrite MEM in *.
                specialize (Sorted _ _ _ SENTRY SENTRY_VAL).
                destruct (Nat.le_gt_cases (len - 1) le_dist). lia.
                assert (S ctr < len)%nat by lia.
                pose proof (at_end_lens _ _ _ _ _ L_NN Len CtrDist).
                destruct H1; try lia.
                destruct (s' R_RDI). contradiction.
                unfold list_node_next. f_equal. apply Contra.
                pose proof (distance_last_node base_mem l (s' R_RDI) ctr RDI).
                rewrite <- MEM in H.
                destruct (s' R_RDI). contradiction. unfold list_node_next in H.
                unfold p.w, p.e, p.pw, p.dw in H. rewrite Contra in H.
                specialize (H CtrDist eq_refl).
                assert (S ctr = len) by eauto using node_distance_uniq.
                subst len. simpl in SENTRY. rewrite Nat.sub_0_r in SENTRY.
                eapply node_distance_uniq'; eauto.
            destruct (le_cases ctr le_dist CtrMax). lia.
                subst ctr.
                pose proof (node_distance_uniq' LeDist CtrDist eq_refl).
                subst le_node.
                apply N.ltb_ge in BC.
                (* specialize (Sorted _ _ _ LeDist ltac:(lia) LeVal). *)
                destruct (s' R_RDI). contradiction.
                replace gt_node with (base_mem Ⓠ[8 + N.pos p]) in *.
                rewrite MEM in *.
                destruct (base_mem Ⓠ[ 8 + N.pos p ]). contradiction.
                    inversion GtVal. subst gt_val. clear - Vals BC.
                    replace (getmem p.w p.e p.dw base_mem (N.pos p0)) with (base_mem Ⓠ[N.pos p0]) in Vals by reflexivity.
                    lia.
                rewrite MEM in *. now inversion LeNextGt.
            eapply node_distance_next_S_len with (dst := s' R_RDI).
                destruct (s' R_RDI). contradiction. reflexivity.
            eapply distance_null_imp_well_formed. now eassumption.
            assumption.
            hammer.
Qed.

End TimingProof.

Require Import i5_7300u.
Module i5_7300u_insert_in_sorted_list := TimingProof i5_7300u.

Goal forall (mem : memory) (l value : addr) (max_dist : N) (t : trace),
    i5_7300u_insert_in_sorted_list.time_of_insert_in_sorted_list mem l value max_dist t =
    (i5_7300u_insert_in_sorted_list.insert_in_sorted_listAuto.cycle_count_of_trace t <= 
        (if
            i5_7300u_insert_in_sorted_list.optN_eqb
                (i5_7300u_insert_in_sorted_list.LL.list_node_value mem value)
                (Some (2 ^ 31 - 1))
            then 54
            else 49 + (1 + max_dist) * 23)).
    intros.
    unfold i5_7300u_insert_in_sorted_list.time_of_insert_in_sorted_list. simpl.
    unfold i5_7300u.ret, i5_7300u.mov_m64_r64, i5_7300u.nop,
        i5_7300u_insert_in_sorted_list.INT_MAX. psimpl.
    reflexivity.
Qed. 

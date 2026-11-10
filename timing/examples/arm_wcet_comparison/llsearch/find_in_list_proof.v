From Picinae.timing.examples.arm_wcet_comparison.llsearch Require Import find_in_list_lifted.
Require Import ARMv6MTiming.
Import ARMv6MNotations.
Require Import TimingAutomation.
From Stdlib Require Import Arith.

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
Global Ltac Zify.zify_pre_hook ::= idtac.

Module Program_find_in_list <: ProgramInformation.
    Definition entry_addr : N := 0x800002c.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x800003c => true
        | _ => false
    end | _ => false end.

    Definition binary := linked_list_find_in_list_armv6m.
End Program_find_in_list.

Module ARMv6MTiming := ARMv6MTiming cpu Program_find_in_list.
Module find_in_listAuto := ARMv6MTimingAutomation ARMv6MTiming.
Import Program_find_in_list find_in_listAuto.

(* One pass over a node whose value isn't the key:
     ldr r3, [r0]; cmp r3, r1; beq (not taken);
     ldr r0, [r0, #4]; cmp r0, #0; bne (taken) *)
Definition t_miss : N :=
    tldr_imm + tcmp_reg + tb_not_taken + tldr_imm + tcmp_imm + tb_taken.

Definition time_of_find_in_list
    (l : addr) (len : nat) (found_idx : option nat) (t : trace) :=
  cycle_count_of_trace t =
    tcmp_imm +
    if (l =? NULL) then
        (* empty list: movs r0, #0; b; bx lr *)
        tb_taken + tmovs_imm + tb + tbx
    else (
        tb_not_taken +
        match found_idx with
        | Some idx =>
            (* nodes passed over, then the one holding the key *)
            N.of_nat idx * t_miss +
            tldr_imm + tcmp_reg + tb_taken + tbx
        | None =>
            (* every node but the last, then the last, whose next is NULL *)
            N.of_nat (len - 1) * t_miss +
            tldr_imm + tcmp_reg + tb_not_taken +
            tldr_imm + tcmp_imm + tb_not_taken + tbx
        end
    ).

(* Either the key is first found at index idx, and that node is returned, or
   the key is in none of the len nodes, and NULL is returned. *)
Definition find_in_list_post (mem : memory) (l : addr) (key : N) (len : nat)
    (s : store) (t : trace) : Prop :=
  (exists idx,
    key_in_linked_list mem l key idx /\
    node_distance mem l (s R_R0) idx /\
    time_of_find_in_list l len (Some idx) t)
  \/
  ((forall idx, (idx < len)%nat -> ~ key_in_linked_list mem l key idx) /\
    s R_R0 = NULL /\
    time_of_find_in_list l len None t).

Definition find_in_list_timing_invs
    (l : addr) (key : N) (len : nat) (base_mem : memory) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800002c => Some (
    s R_R0 = l /\ s R_R1 = key /\ s V_MEM32 = base_mem /\
    node_distance base_mem l NULL len /\
    cycle_count_of_trace t' = 0
  )
| 0x8000030 => Some (exists ctr,
    s R_R1 = key /\ s V_MEM32 = base_mem /\
    l <> NULL /\ s R_R0 <> NULL /\
    node_distance base_mem l (s R_R0) ctr /\
    node_distance base_mem l NULL len /\
    (* the key isn't in any node passed over *)
    (forall i, (i < ctr)%nat -> ~ key_in_linked_list base_mem l key i) /\
    cycle_count_of_trace t' =
        tcmp_imm + tb_not_taken + N.of_nat ctr * t_miss
  )
| 0x800003c => Some (find_in_list_post base_mem l key len s t)
| _ => None end | _ => None end.

(* If the key is in none of the first ctr nodes, then wherever it is, it is at
   index ctr or later. *)
Lemma not_in_min : forall mem l key ctr,
    (forall i, (i < ctr)%nat -> ~ key_in_linked_list mem l key i) ->
    forall i, key_in_linked_list mem l key i -> (ctr <= i)%nat.
Proof.
    intros mem l key ctr NotIn i In.
    destruct (Nat.lt_ge_cases i ctr) as [Lt|Ge]; [|assumption].
    exfalso. exact (NotIn i Lt In).
Qed.

(* A node whose value isn't the key isn't where the key first occurs. *)
Lemma node_not_key : forall mem l node ctr key,
    node_distance mem l node ctr ->
    node <> NULL ->
    list_node_value mem node <> Some key ->
    ~ key_in_linked_list mem l key ctr.
Proof.
    intros mem l node ctr key Dist NN NotKey In.
    apply NotKey.
    symmetry. exact (key_in_linked_list_value_equal _ _ _ _ _ In Dist).
Qed.

Theorem find_in_list_timing:
  forall s t s' x' l key len base_mem
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models armv6mtypctx s)
         (* bindings *)
         (R0: s R_R0 = l)
         (R1: s R_R1 = key)
         (MEM: s V_MEM32 = base_mem)
         (* list length is finite *)
         (LEN: node_distance base_mem l NULL len),
  satisfies_all
    lifted_prog
    (find_in_list_timing_invs l key len base_mem)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep armv6m_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped_lift_armv6m].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.
    - (* entry *)
        destruct PRE as (R0 & R1 & MEM & Len & Cycles).
        repeat step.
        -- (* l = NULL: the list is empty *)
            right. apply N.eqb_eq in BC. subst l.
            assert (len = 0%nat) by
                (inversion Len; [reflexivity | contradiction]).
            subst len. repeat split.
            intros. lia.
            unfold time_of_find_in_list. hammer.
        -- (* l <> NULL: enter the loop *)
            apply N.eqb_neq in BC.
            exists 0%nat.
            repeat split; auto.
            apply Dst0.
            intros. lia.
            hammer.
    - (* loop head *)
        destruct PRE as (ctr & R1 & MEM & L_NN & Curr_NN & CtrDist & Len & NotIn & Cycles).
        pose proof (distance_null_imp_well_formed _ _ _ Len) as WF.
        assert (CV: list_node_value base_mem (s' R_R0) = Some (base_mem Ⓓ[s' R_R0])).
            destruct (s' R_R0). contradiction. reflexivity.
        assert (CN: list_node_next base_mem (s' R_R0) = Some (base_mem Ⓓ[4 + s' R_R0])).
            destruct (s' R_R0). contradiction. reflexivity.
        pose proof (node_distance_next_S_len _ _ _ _ _ CN WF CtrDist) as NextDist.
        repeat step.
        -- (* the node holds the key: return it *)
            apply N.eqb_eq in BC.
            left. exists ctr. repeat split; auto.
            eapply key_at_node; try eassumption.
                rewrite CV, BC. reflexivity.
                apply not_in_min. assumption.
            unfold time_of_find_in_list.
            apply N.eqb_neq in L_NN. rewrite L_NN. hammer. rewrite N.eqb_refl. lia.
        -- (* the next node is NULL: the key isn't in the list *)
            apply N.eqb_eq in BC0.
            rewrite BC0 in NextDist.
            pose proof (node_distance_uniq NextDist Len) as Ctr. subst len.
            right. repeat split; auto.
            intros i Lt. assert (i < ctr \/ i = ctr)%nat as [Lt'|Eq] by lia.
                now apply NotIn.
                subst i. apply (node_not_key _ _ _ _ _ CtrDist Curr_NN).
                rewrite CV. intro H. inversion H. apply N.eqb_neq in BC.
                apply BC. assumption.
            unfold time_of_find_in_list.
            apply N.eqb_neq in L_NN. rewrite L_NN.
            replace (S ctr - 1)%nat with ctr by lia.
            hammer.
        -- (* the next node is not NULL: go on to it *)
            apply N.eqb_neq in BC0.
            exists (S ctr). repeat split; auto.
            intros i Lt. assert (i < ctr \/ i = ctr)%nat as [Lt'|Eq] by lia.
                now apply NotIn.
                subst i. apply (node_not_key _ _ _ _ _ CtrDist Curr_NN).
                rewrite CV. intro H. inversion H. apply N.eqb_neq in BC.
                apply BC. assumption.
            hammer.
            change (N.pos (Pos.of_succ_nat ctr)) with (N.of_nat (S ctr)).
            rewrite Nat2N.inj_succ. unfold t_miss. lia.
Qed.

End TimingProof.

(* The closed form on the Cortex-M0 used in the aiT comparison:
   empty list 11, key at idx 11 + 10 idx, key absent 3 + 10 len. *)
Require Import CortexM0NoWait.
Module M0 := TimingProof CortexM0NoWait.
Import M0 CortexM0NoWait.

Goal forall l len found_idx t,
    time_of_find_in_list l len found_idx t <->
    (find_in_listAuto.cycle_count_of_trace t =
        if (l =? LL.NULL) then 11 else
        match found_idx with
        | Some idx => 11 + 10 * N.of_nat idx
        | None => 13 + 10 * N.of_nat (len - 1)
        end).
Proof.
    intros. unfold time_of_find_in_list, t_miss.
    destruct (l =? LL.NULL); [reflexivity|].
    destruct found_idx; cbv - [N.of_nat N.mul N.add find_in_listAuto.cycle_count_of_trace];
    split; intro H; rewrite H; lia.
Qed.

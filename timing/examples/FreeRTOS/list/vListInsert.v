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
    (pxNewListItem : addr) (maximal_index : N) (t : trace) :=
  cycle_count_of_trace t =
    tlw + taddi + taddi +
    (if mem Ⓓ[pxNewListItem] =? portMAX_DELAY then (
      tfbne + tlw
    ) else (
      ttbne + (maximal_index - 1) * (
        taddi + tlw + tlw + ttbgeu
      ) + taddi + tlw + tlw + tfbgeu + tjal
    )) + (
      tlw + 4 * tsw + tlw + tsw + taddi + tsw + tjalr
    ).

Definition exists_maximal (mem : memory) (pxList pxNewListItem maximal : addr)
    (max_val new_val : N) (max_dist : nat):=
  node_distance mem pxList maximal max_dist /\
  list_node_value mem maximal = Some max_val /\
  max_val <= new_val /\
  LLForall (fun m a => 
    match list_node_value m a with
    | None => True
    | Some val => val <= max_val
    end
  ) mem pxList.

Definition vListInsert_timing_invs (base_mem : memory) (len : nat) (max_val new_val : N)
    (pxList pxNewListItem maximal : addr) (dist_to_maximal : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800023f0 => Some (
    exists_maximal (s V_MEM32) pxList pxNewListItem maximal
      max_val new_val dist_to_maximal /\
    s R_A0 = pxList /\ s R_A1 = pxNewListItem /\
    s V_MEM32 = base_mem /\
    pxList <> NULL /\
    node_distance (s V_MEM32) pxList NULL len /\
    cycle_count_of_trace t' = 0
  )
| 0x8000242c => Some (exists ctr,
    exists_maximal (s V_MEM32) pxList pxNewListItem maximal
      max_val new_val dist_to_maximal /\
    pxList <> NULL /\
    s V_MEM32 = base_mem /\
    (base_mem Ⓓ[pxNewListItem] =? portMAX_DELAY) = false /\
    node_distance (s V_MEM32) pxList NULL len /\
    node_distance (s V_MEM32) pxList ((s V_MEM32) Ⓓ[s R_A4]) ctr /\
    cycle_count_of_trace t' =
      tlw + taddi + taddi +
      ttbne + (N.of_nat ctr - 1) * (
        taddi + tlw + tlw + ttbgeu
      )
  )
| 0x80002428 => Some (time_of_vListInsert base_mem
                    pxNewListItem (N.of_nat dist_to_maximal) t)
| _ => None end | _ => None end.

Lemma le_cases : forall n m,
    (n <= m -> n < m \/ n = m)%nat.
Proof. lia. Qed.

Theorem vListInsert_timing:
  forall s t s' x' base_mem len pxList pxNewListItem maximal max_val
            dist_to_maximal new_val
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = pxList)
         (A1: s R_A1 = pxNewListItem)
         (* pxList is non-null (guaranteed by vListInitialise) *)
         (PXL_NN: pxList <> NULL)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM32) pxList NULL len)
         (NLI_VAL: list_node_value base_mem pxNewListItem = Some new_val)
         (* there exists a maximal node in the list with a value
            less than or equal to that of pxNewListItem *)
         (MAX: exists_maximal base_mem pxList pxNewListItem maximal max_val new_val dist_to_maximal),
  satisfies_all
    lifted_prog
    (vListInsert_timing_invs base_mem len max_val new_val pxList pxNewListItem maximal dist_to_maximal)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep r5_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    rewrite MEM.
    split. assumption. repeat split; auto.
    now rewrite <- MEM.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    - destruct PRE as (EMax & A0 & A1 & MEM & PXL_NN & Len & Cycles).
      repeat step.
      -- (* 0x8000242c invariant *)
        exists 1%nat. rewrite MEM in *. split. assumption.
        repeat split; auto.
        now apply Bool.negb_true_iff in BC. 
        apply node_distance_next_S_len with (dst := pxList).
          unfold list_node_next. destruct pxList.
            contradiction.
            reflexivity.
          eapply distance_null_imp_well_formed; eassumption.
          apply Dst0.
          hammer.
      -- (* 0x80002428 postcondition *)
        unfold portMAX_DELAY.
        hammer.
    - destruct PRE as (ctr & EMax & PXL_NN & MEM & NLI_VALID & Len & DstCurr & 
          Cycles).
      repeat step.
      -- (* 0x80002428 postcondition *)
        rewrite NLI_VALID.
        hammer. replace ctr with dist_to_maximal.
        lia.
        destruct EMax, H0, H1.
        enough (s' V_MEM32 Ⓓ[s' R_A4] = maximal).
          rewrite H3 in *.
          eapply node_distance_uniq; eassumption.
        (* If we can show that we have reached the maximal 
           list item, this is proven
        *)
        admit.
      -- exists (S ctr). rewrite MEM in *.
         split. assumption. repeat split; auto.
         eapply node_distance_next_S_len; eauto.
         unfold list_node_next.
         admit.
         eapply distance_null_imp_well_formed; eassumption.
         replace (N.of_nat (S ctr) - 1) with (N.of_nat ctr) by lia.
         hammer. replace (N.of_nat ctr) with (1 + N.of_nat ctr - 1) at 2 by lia.
         rewrite <- N.add_sub_assoc. lia.
         admit.
Admitted.

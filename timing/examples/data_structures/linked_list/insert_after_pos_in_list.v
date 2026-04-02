Require Import linked_list.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_insert_after_pos_in_list <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x1f0 | 0x210 => true
        | _ => false
    end | _ => false end.

    Definition binary := linked_list_bin.
End Program_insert_after_pos_in_list.

Module RISCVTiming := RISCVTiming cpu Program_insert_after_pos_in_list.
Module insert_after_pos_in_list := RISCVTimingAutomation RISCVTiming.
Import Program_insert_after_pos_in_list insert_after_pos_in_list.

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

Definition time_of_insert_after_pos_in_list 
    (l value : addr) (position len : N) (t : trace) :=
  cycle_count_of_trace t =
    if (l =? NULL) then (
      ttbeq + tjalr
    ) else (
      tfbeq + taddi + 
      if (value =? NULL) then (
        tfbne + tjalr
      ) else (
        ttbne + tlw + if (position =? 0) then (
          tfbne + tsw + tsw + tjalr
        ) else (
          ttbne + (if (position <? len) then (
            (position - 1) * (
                tfbeq + taddi + taddi + tlw + ttbne
            ) + tfbeq + taddi + taddi + tlw + tfbne
          ) else (
            (len - 1) * (
                tfbeq + taddi + taddi + tlw + ttbne
            ) + ttbeq
          )) + tsw + tsw + tjalr
        )
      )
    ).

Definition insert_after_pos_in_list_timing_invs
    (l value : addr) (position : N) (len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (
    s R_A0 = l /\ s R_A1 = value /\ s R_A2 = position /\
    node_distance (s V_MEM32) l NULL len /\
    cycle_count_of_trace t' = 0
  )
| 0x1f4 => Some (exists ctr, s R_A4 = N.of_nat ctr - 1 /\
    s R_A2 = position /\
    position < 2^32 /\
    (1 <= ctr)%nat /\
    node_distance (s V_MEM32) l (s R_A5) ctr /\
    node_distance (s V_MEM32) l NULL len /\
    (* (ctr <= len)%nat /\ *)
    (ctr <= N.to_nat position)%nat /\
    (l =? 0) = false /\
    (value =? 0) = false /\
    (position =? 0) = false /\
    cycle_count_of_trace t' =
      tlw + ttbne + taddi + tfbeq + ttbne +
      (N.of_nat ctr - 1) * (
        tfbeq + taddi + taddi + tlw + ttbne
      )
  )
| 0x1f0 | 0x210 => Some (time_of_insert_after_pos_in_list 
                    l value position (N.of_nat len) t)
| _ => None end | _ => None end.

Lemma le_cases : forall n m,
    (n <= m -> n < m \/ n = m)%nat.
Proof. lia. Qed.

Theorem insert_after_pos_in_list_timing:
  forall s t s' x' l value position len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (A0: s R_A0 = l)
         (A1: s R_A1 = value)
         (A2: s R_A2 = position)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM32) l NULL len),
  satisfies_all
    lifted_prog
    (insert_after_pos_in_list_timing_invs l value position len)
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

    - destruct PRE as (A0 & A1 & A2 & Dist & Cycles).
      repeat step.
      -- (* 0x1f0 postcondition *)
        unfold NULL. rewrite BC.
        hammer.
      -- (* 0x1f4 invariant *)
        exists 1%nat. repeat split; auto.
        pose proof (models_var R_A2 MDL). simpl in H.
          rewrite A2 in H. lia.
        apply node_distance_next_S_len with (dst := l).
          unfold list_node_next. destruct l.
            inversion BC.
            reflexivity.
          eapply distance_null_imp_well_formed; eassumption.
          apply Dst0.
          destruct len.
            inversion Dist. rewrite H1 in BC. inversion BC.
            lia.
          lia. lia.
          hammer.
      -- (* 0x210 postcondition *)
        unfold NULL. hammer.
        apply Bool.negb_false_iff in BC1.
        rewrite N.eqb_sym in BC1.
        hammer.
      -- (* 0x1f0 postcondition *)
        unfold NULL. hammer.
    - destruct PRE as (ctr & A4 & A2 & PosValid & CtrPos & 
              DstCurr & Len & CtrP & LNz & Vnz & Pnz & Cycles).
      repeat step.
      -- (* 0x210 postcondition *)
        unfold NULL. hammer.
        replace ctr with len in *.
        enough ((position <? N.of_nat len) = false).
          hammer.
        destruct (N.eq_dec position (N.of_nat len)).
          lia. lia. 
        apply N.eqb_eq in BC. rewrite BC in DstCurr.
        eapply node_distance_uniq; eauto.
      -- (* 0x1f4 invariant *) 
        exists (S ctr). repeat split; auto.
        rewrite N.mod_small, Nat2N.inj_succ, <- N.add_1_l.
          rewrite N.add_sub_assoc. reflexivity.
        lia.
        assert (N.of_nat ctr - 1 < 2^32).
          pose proof (models_var R_A4 MDL). simpl in H.
          lia.
        lia.
        apply node_distance_next_S_len with (dst := s' R_A5).
          destruct (s' R_A5). inversion BC. reflexivity.
        eapply distance_null_imp_well_formed; eauto.
        assumption. lia.
        rewrite Nat2N.inj_succ, N.sub_succ_l by lia.
        hammer. rewrite N.mod_small by lia. 
        rewrite N.mod_small in BC0 by lia.
        rewrite BC0. hammer.
      -- (* 0x210 postcondition *)
        unfold NULL. hammer.
        pose proof (models_var R_A4 MDL). simpl in H.
        enough ((position <? N.of_nat len) = true).
          rewrite H0. rewrite N.mod_small in * by lia.
          rewrite BC0. hammer.
        destruct (N.eq_dec position (N.of_nat len)).
          rewrite e in *; clear e.
          rewrite N.mod_small in BC0 by lia.
          apply Bool.negb_false_iff, N.eqb_eq in BC0.
          rewrite N.add_sub_assoc in BC0 by lia.
          psimpl in BC0. apply Nat2N.inj in BC0. subst ctr.
          enough (s' R_A5 = NULL). rewrite H0 in BC. inversion BC.
          eapply node_distance_uniq'; eauto.
        apply Bool.negb_false_iff, N.eqb_eq in BC0.
        rewrite N.mod_small, N.add_sub_assoc in BC0 by lia.
        psimpl in BC0. rewrite <- BC0 in *; clear BC0.
        pose proof (dist_node_le_dist_null _ _ _ _ _ Len DstCurr).
        lia.
Qed.

End TimingProof.

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal forall l value position len t,
    time_of_insert_after_pos_in_list l value position len t = 
    (insert_after_pos_in_list.cycle_count_of_trace t =
      (if l =? LL.NULL
      then 10 + T_inst_latency + T_inst_latency
      else
        5 +
        (if value =? LL.NULL
        then 8 + T_inst_latency
        else
          if position =? 0
          then
          25 + T_inst_latency + T_data_latency +
          T_data_latency + T_data_latency + T_inst_latency
          else
          22 + T_inst_latency + T_data_latency +
          (if position <? len
            then
            19 + T_inst_latency +
            (position - 1) *
            (16 + T_data_latency + T_inst_latency) +
            T_data_latency
            else
            10 + T_inst_latency +
            (len - 1) *
            (16 + T_data_latency + T_inst_latency) +
            T_inst_latency) + T_data_latency +
          T_data_latency + T_inst_latency))).
Proof.
    intros. unfold time_of_insert_after_pos_in_list. f_equal.
    unfold ttbeq, tjalr, tfbeq, taddi, tfbne, ttbne, tlw, tsw.
    psimpl. psimpl. reflexivity.
Qed.

Require Import linked_list.
Require Import RISCVTiming.
Require Import Arith.
Import RISCVNotations.
Require Import TimingAutomation.

(** Eliminate the store by rewriting the expressions stored in registers and
    inferring their bounds from the type context. *)
Global Ltac elimstore :=
  repeat lazymatch goal with
  | [ H: ?s ?v = _, MDL: models ?typs ?s |- _] =>
      let Hyp := fresh "SBound" in
      pose proof (Hyp:=models_var v MDL); cbv -[N.lt N.pow] in Hyp;
      (** Keep limit if bitwidth is small; if it is large lia will hang. *)
      match type of Hyp with
      | _ < 2 ^ ?w => assert (temp:(w <=? 256) = true) by reflexivity; clear temp
      | _ => clear Hyp
      end;
      try rewrite H in *; clear H; try clear s MDL
  end.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_find_in_list <: ProgramInformation.
    Definition entry_addr : N := 0x214.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x228 => true
        | _ => false
    end | _ => false end.

    Definition binary := linked_list_bin.
End Program_find_in_list.

Module RISCVTiming := RISCVTiming cpu Program_find_in_list.
Module find_in_list := RISCVTimingAutomation RISCVTiming.
Import Program_find_in_list find_in_list.

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
Global Ltac Zify.zify_pre_hook ::= elimstore; unfold msub in *; llunfold.

Definition time_of_find_in_linked_list
        (len : nat) (found_idx : option nat) (t : trace) :=
    cycle_count_of_trace t =
        match found_idx with
        | None =>
            N.of_nat len
        | Some idx =>
            N.of_nat idx
        end * (
          tfbeq + tlw + tfbeq + tlw + tjal
        ) + (match found_idx with
            | None =>
              ttbeq
            | Some _ =>
              tfbeq + tlw + ttbeq
            end) + tjalr.

Definition timing_postcondition (mem : memory) 
    (head : addr) (key : N) (len : nat) (t : trace) : Prop :=
  (exists loc, 
    key_in_linked_list mem head key loc /\ 
    time_of_find_in_linked_list len (Some loc) t)
  \/
  ((~ exists loc, (loc < len)%nat /\
    key_in_linked_list mem head key loc) /\ 
    time_of_find_in_linked_list len None t).

Definition find_in_linked_list_timing_invs (s : store)
    (sp : N) (head : addr) (key : N) (len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x214 => Some (exists ctr mem curr, 
    s V_MEM32 = mem /\ s R_A0 = curr /\
    s R_A1 = key /\
    node_distance mem head curr ctr /\
    node_distance mem head NULL len /\
    (ctr <= len)%nat /\
    (forall i, (i < ctr)%nat -> ~ key_in_linked_list mem head key i) /\
    (forall fuel, key_in_linked_list mem head key fuel -> (ctr <= fuel)%nat) /\
    cycle_count_of_trace t' =
      (N.of_nat ctr) * (
        tfbeq + tlw + tfbeq + tlw + tjal
      )
  )
| 0x228 => Some (timing_postcondition (s V_MEM32) head key len t)
| _ => None end | _ => None end.

Lemma node_distance_same_len : forall mem h p1 p2 len,
  node_distance mem h p1 len ->
  node_distance mem h p2 len ->
  p1 = p2.
Proof.
  intros. induction H.
  - now inversion H0.
  - inversion H0; subst; clear H0.
    rewrite NEXT0 in NEXT. inversion NEXT; subst; clear NEXT.
    apply IHnode_distance, LEN.
Qed.

Lemma le_cases : forall n m,
    (n <= m -> n < m \/ n = m)%nat.
Proof. lia. Qed.

Lemma curr_not_in : forall mem head curr ctr key,
  node_distance mem head curr ctr ->
  (curr =? 0) = false ->
  (mem Ⓓ[curr] =? key) = false ->
  ~ key_in_linked_list mem head key ctr.
Proof.
  intros. destruct (key_in_linked_list_dec mem head key ctr).
    pose proof (key_in_linked_list_value_equal _ _ _ _ _
                  k H).
    unfold list_node_value in H2.
    destruct curr. inversion H0.
    inversion H2; subst.
      rewrite N.eqb_refl in H1. inversion H1.
    assumption.
Qed.

Theorem find_in_linked_list_timing:
  forall s t s' x' sp head key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (A0: s R_A0 = head)
         (A1: s R_A1 = key)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM32) head NULL len),
  satisfies_all
    lifted_prog
    (find_in_linked_list_timing_invs s sp head key len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep r5_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    exists 0%nat, (s V_MEM32), head.
    repeat split; auto; try lia.
    apply Dst0.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (ctr & mem & curr & MEM & A0 & A1 & DstCurr & Len &
                      CtrLen & NotIn & In & Cycles).
    step.
    - (* curr = NULL *)
      apply N.eqb_eq in BC; subst curr. rewrite BC in *.
      unfold NULL in Len.
      replace ctr with len in * by (eapply node_distance_uniq; eauto).
      right. split. intros (loc & LocLen & Contra).
        elimstore. now apply (NotIn loc).
      unfold time_of_find_in_linked_list.
        hammer. rewrite N.eqb_refl. hammer.
    - (* curr <> NULL *)
      repeat step.
      -- (* mem[curr] = key *)
        left. exists ctr. split.
          eapply key_at_node; eauto.
          apply N.eqb_neq in BC. assumption.
          cbv [list_node_value].
          destruct curr. inversion BC.
          apply N.eqb_eq in BC0. now rewrite <- BC0.
        unfold time_of_find_in_linked_list. hammer.
      -- (* mem[curr] <> key *)
        exists (S ctr), mem. eexists.
        repeat split; eauto.
        eapply node_distance_next_S_len; try eassumption.
        destruct curr. inversion BC. reflexivity.
        eapply distance_null_imp_well_formed, Len.
        destruct (Nat.eq_dec ctr len).
          subst ctr. replace curr with NULL in * by
              (eapply node_distance_same_len; eassumption).
            inversion BC.
          lia.
        intros. apply PeanoNat.lt_n_Sm_le in H.
          apply le_cases in H.
          destruct H.
            now apply NotIn.
            subst.
            apply curr_not_in with (curr := s' R_A0); try assumption.
          eapply fuel_le_incr; eauto.
          unfold list_node_value.
            destruct curr. inversion BC.
            intro. inversion H. rewrite H1 in BC0.
            rewrite N.eqb_refl in BC0. inversion BC0.
          hammer.
Qed.

End TimingProof.

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal forall t len found_idx,
    time_of_find_in_linked_list len found_idx t = 
    (find_in_list.cycle_count_of_trace t =
      5 +
      match found_idx with
      | Some idx => N.of_nat idx
      | None => N.of_nat len
      end *
      (19 + T_data_latency + T_data_latency +
      T_inst_latency) +
      match found_idx with
      | Some _ =>
          12 + T_data_latency + T_inst_latency
      | None => 5 + T_inst_latency
      end + T_inst_latency).
Proof.
    intros. unfold time_of_find_in_linked_list. f_equal.
    unfold tfbeq, tlw, tjal, ttbeq, tjalr.
    psimpl. repeat rewrite N.add_assoc. f_equal. destruct found_idx;
    psimpl; lia.
Qed.


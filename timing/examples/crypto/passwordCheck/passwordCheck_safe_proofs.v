Require Import passwordCheck_safe.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_passwordCheck <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x21c => true
        | _ => false
    end | _ => false end.

    Definition binary := passwordCheck.
End Program_passwordCheck.

Module RISCVTiming := RISCVTiming cpu Program_passwordCheck.
Module passwordCheckAuto := RISCVTimingAutomation RISCVTiming.
Import Program_passwordCheck passwordCheckAuto.

Definition nilfree (mem : memory) (p : addr) (k : N) := 
    forall i, i < k -> 0 < mem Ⓑ[p+i].

(* A string has length len *)
Definition strlen (mem : memory) (p : addr) (len : N) :=
    nilfree mem p len /\ mem Ⓑ[p + len] = 0.

Lemma le_cases : forall n m,
    n <= m -> n < m \/ n = m.
Proof. lia. Qed.

Definition time_of_passwordCheck (len_user : N) (t : trace) :=
    cycle_count_of_trace t =
        taddi +
        len_user * (
            tlbu + tlbu + tsub + tsltiu + tsltiu +
            tor + tand + taddi + tsltu + tadd + ttbne
        ) + tlbu + tlbu + tsub + tsltiu + tsltiu +
            tor + tand + taddi + tsltu + tadd + tfbne +
        taddi + tandi + tjalr.

Definition passwordCheck_timing_invs (s : store) (base_mem : memory)
    (stored user : addr) (user_len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e8 => Some (
    exists i,
    i <= user_len /\
    s V_MEM32 = base_mem /\ s R_A0 = stored ⊕ i /\ s R_A1 = user ⊕ i /\
    strlen base_mem user user_len /\
    cycle_count_of_trace t' = taddi +
        i * (tlbu + tlbu + tsub + tsltiu + tsltiu +
            tor + tand + taddi + tsltu + tadd + ttbne)
)
| 0x21c => Some (time_of_passwordCheck user_len t)
| _ => None end | _ => None end.

Lemma strlen_Sidx_le_len : forall i len mem p,
    i <= len ->
    strlen mem p len ->
    mem Ⓑ[p + i] =? 0 = false ->
    1 + i <= len.
Proof.
    intros. destruct H0.
    apply le_cases in H. destruct H.
        lia.
    subst. rewrite H2 in H1. inversion H1.
Qed.

Lemma strlen_idx_eq_len : forall i len mem p,
    i <= len ->
    strlen mem p len ->
    mem Ⓑ[p + i] =? 0 = true ->
    i = len.
Proof.
    intros. destruct H0.
    apply le_cases in H. destruct H.
        specialize (H0 i H). apply N.eqb_eq in H1. lia.
    assumption.
Qed.

Theorem passwordCheck_timing:
  forall s (t : trace) s' x' base_mem stored user user_len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (ULEN: strlen base_mem user user_len)
         (Stored: s R_A0 = stored)
         (User: s R_A1 = user),
  satisfies_all 
    lifted_prog
    (passwordCheck_timing_invs s base_mem stored user user_len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    exists 0.
    psimpl. repeat (split; auto; lia).

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (i & ILEN & MEM & A0 & A1 & Strlen & Cycles).
    repeat step.
    - (* user[i] <> NULL *)
        exists (1 + i). repeat (split; auto).
        apply Bool.negb_true_iff in BC.
            eapply strlen_Sidx_le_len; eauto.
        now psimpl.
        apply Bool.negb_true_iff in BC.
            replace (0 <? _) with true by lia. now psimpl.
        hammer.
    - (* user[i] = NULL *)
        hammer.
        destruct Strlen.
        rewrite (strlen_idx_eq_len i user_len base_mem user).
            lia.
        assumption. now split.
        now apply Bool.negb_false_iff in BC.
Qed.

End TimingProof.

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal forall t ulen,
    time_of_passwordCheck ulen t = 
    (passwordCheckAuto.cycle_count_of_trace t = 
      38 + ulen * (29 + 2 * T_data_latency + T_inst_latency) +
        2 * T_data_latency + T_inst_latency).
Proof.
    intros. unfold time_of_passwordCheck. f_equal.
    unfold taddi, tlbu, tsub, tsltiu, tor, tand, tsltu, ttbne, tadd,
        tsub, tandi, tjalr, tfbne. lia.
Qed.

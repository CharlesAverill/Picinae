Require Import passwordCheck_vuln.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_passwordCheck <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x214 | 0x200 => true
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

(* Two strings at p1 and p2 are equal up to k bytes *)
Definition streq (mem : memory) (p1 p2 : addr) (k : N) :=
    nilfree mem p1 k /\ nilfree mem p2 k /\
    forall i, i < k -> mem Ⓑ[p1+i] = mem Ⓑ[p2+i].

Lemma le_cases : forall n m,
    n <= m -> n < m \/ n = m.
Proof. lia. Qed.

Lemma lt_Sn : forall n m,
    n < 1 + m -> n <= m.
Proof. lia. Qed.

Lemma nilfree_plus_one : forall mem p k,
    nilfree mem p k ->
    0 < mem Ⓑ[p + k] ->
    nilfree mem p (1 + k).
Proof.
    intros. intros i ilt.
    apply lt_Sn, le_cases in ilt. destruct ilt.
        now apply H.
    now subst.
Qed.

Theorem streq_plus_one : forall mem p1 p2 k,
    streq mem p1 p2 k ->
    mem Ⓑ[p1 + k] = mem Ⓑ[p2 + k] ->
    0 < mem Ⓑ[p1 + k] ->
    0 < mem Ⓑ[p2 + k] ->
    streq mem p1 p2 (1 + k).
Proof.
    intros. repeat split.
    destruct H as (NF1 & NF2 & Eq).
        now apply nilfree_plus_one.
    destruct H as (NF1 & NF2 & Eq).
        now apply nilfree_plus_one.
    intros. apply lt_Sn, le_cases in H3.
    destruct H3. now apply H. now subst.
Qed.

Definition time_of_passwordCheck (stored_len : N) (diff_idx : option N) (t : trace) :=
    cycle_count_of_trace t =
        (match diff_idx with None => stored_len | Some idx => idx end) *
        (tlbu + tlbu + ttbeq + taddi + taddi + ttbne) +
        match diff_idx with
        | None => tlbu + tlbu + ttbeq +
            taddi + taddi + tfbne +
            taddi + tjalr
        | Some _ => tlbu + tlbu + tfbeq + 
                    tsltiu + tsub + tandi + taddi + tjalr
        end.

Definition timing_postcondition (mem : memory) 
        (stored user : addr) (len : N) (t : trace) : Prop :=
    (streq mem stored user len /\
        time_of_passwordCheck len None t) \/
    (exists i, i <= len /\ streq mem stored user i /\
        time_of_passwordCheck len (Some i) t).

Definition passwordCheck_timing_invs (s : store) (base_mem : memory)
    (stored user : addr) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (
    exists i,
    s V_MEM32 = base_mem /\ s R_A0 = stored ⊕ i /\ s R_A1 = user ⊕ i /\
    i <= len /\
    strlen base_mem stored len /\
    streq base_mem stored user i /\
    cycle_count_of_trace t' =
        i * (tlbu + tlbu + ttbeq + taddi + taddi + ttbne)
)
| 0x214 | 0x200 => Some (timing_postcondition base_mem stored user len t)
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
  forall s (t : trace) s' x' base_mem stored user len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (LEN: strlen base_mem stored len)
         (Stored: s R_A0 = stored)
         (User: s R_A1 = user),
  satisfies_all 
    lifted_prog
    (passwordCheck_timing_invs s base_mem stored user len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    exists 0. repeat split; try lia; try apply LEN.
    1-2: (rewrite N.add_0_r, N.mod_small; [assumption|subst]).
    pose proof (models_var R_A0 MDL) as H; simpl in H.
        apply H.
    pose proof (models_var R_A1 MDL) as H; simpl in H.
        apply H.
    1-2: intros i X; lia.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (i & MEM & A0 & A1 & ILen & Strlen & Streq &
                        Cycles).
    repeat step.
    - (* stored[i] = user[i] *)
        apply Bool.negb_true_iff in BC0.
        apply N.eqb_eq in BC.
        exists (i + 1). psimpl.
        split. reflexivity.
        split. reflexivity.
        split. reflexivity.
        split. eapply strlen_Sidx_le_len; eauto.
        split. assumption.
        split. apply streq_plus_one; auto;
            apply N.eqb_neq in BC0. lia.
            rewrite <- BC. lia.
        hammer. rewrite <- BC, BC0. hammer.
    - (* stored[i] = NULL *)
        replace i with len in *.
        left. split. assumption.
        unfold time_of_passwordCheck. hammer. 
        symmetry. eapply strlen_idx_eq_len; eauto.
        now apply Bool.negb_false_iff in BC0.
    - (* stored[i] <> user[i] *)
        apply N.eqb_neq in BC. right. exists i.
        split. assumption.
        split. assumption.
        unfold time_of_passwordCheck.
        hammer.
Qed.

End TimingProof.

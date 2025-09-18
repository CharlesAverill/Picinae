Require Import passwordCheck_safe.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

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

Definition time_of_passwordCheck (len_stored len_user : N) (t : trace) :=
    cycle_count_of_trace t =
        taddi +
        (N.min len_stored len_user) * (
            tlbu + tlbu + taddi + tsltiu + tsub + tsltiu +
            tor + tand + taddi + tfbeq + ttbne
        ) + (tlbu + tlbu + taddi + tsltiu + tsub + tsltiu +
            tor + tand + taddi) + 
        (if len_user <=? len_stored then (
            ttbeq
        ) else (
            tfbeq + tfbne
        )) + taddi + tandi + tjalr.

Definition passwordCheck_timing_invs (s : store) (base_mem : memory)
    (stored user : addr) (len1 len2 : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e8 => Some (
    exists i,
    s V_MEM32 = base_mem /\ s R_A0 = stored ⊕ i /\ s R_A1 = user ⊕ i /\
    i <= N.min len1 len2 /\
    strlen base_mem stored len1 /\
    strlen base_mem user len2 /\
    cycle_count_of_trace t' = taddi +
        i * (tlbu + tlbu + taddi + tsltiu + tsub + tsltiu +
            tor + tand + taddi + tfbeq + ttbne)
)
| 0x21c => Some (time_of_passwordCheck len1 len2 t)
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
  forall s (t : trace) s' x' base_mem stored user len1 len2
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (LEN1: strlen base_mem stored len1)
         (LEN2: strlen base_mem user len2)
         (Stored: s R_A0 = stored)
         (User: s R_A1 = user),
  satisfies_all 
    lifted_prog
    (passwordCheck_timing_invs s base_mem stored user len1 len2)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    exists 0. repeat split; try lia; try apply LEN1; try apply LEN2.
    1-2: (rewrite N.add_0_r, N.mod_small; [assumption|subst]).
    pose proof (models_var R_A0 MDL) as H; simpl in H.
        apply H.
    pose proof (models_var R_A1 MDL) as H; simpl in H.
        apply H.
    hammer.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (i & MEM & A0 & A1 & ILen & Strlen1 & Strlen2 &
                        Cycles).
    repeat step.
    - (* user[i] = NULL *)
        hammer. apply N.min_glb_iff in ILen.
        destruct ILen.
        pose proof (strlen_idx_eq_len i 
            len2 base_mem user H0 Strlen2 BC). subst.
        rewrite (N.min_r _ _ H).
        destruct (N.eq_dec len2 len1).
            subst. rewrite N.leb_refl. lia.
        replace (len2 <=? len1) with true. lia.
        symmetry. now apply N.leb_le in H.
    -(* user[i] <> NULL, stored[i] <> NULL *)
        apply N.min_glb_iff in ILen.
        apply Bool.negb_true_iff in BC0.
        destruct ILen.
        pose proof (strlen_Sidx_le_len i
            len1 base_mem stored H Strlen1 BC0).
        pose proof (strlen_Sidx_le_len i
            len2 base_mem user H0 Strlen2 BC).
        exists (i + 1). psimpl.
        split. reflexivity.
        split. reflexivity.
        split. reflexivity.
        split. now apply N.min_glb.
        split. assumption.
        split. assumption.
        hammer.
    - (* user[i] <> NULL, stored[i] = NULL *)
        hammer. apply N.min_glb_iff in ILen.
        destruct ILen.
        apply Bool.negb_false_iff in BC0.
        pose proof (strlen_idx_eq_len i 
            len1 base_mem stored H Strlen1 BC0). subst.
        pose proof (strlen_Sidx_le_len len1
            len2 (s' V_MEM32) user ltac:(lia) Strlen2 BC).
        assert (len1 < len2) by lia.
        replace (len2 <=? len1) with false.
        rewrite (N.min_l _ _ H0). lia.
        symmetry. apply N.leb_gt. assumption.
Qed.

End TimingProof.

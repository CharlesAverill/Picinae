From Picinae.timing.examples.arm_wcet_comparison.llsearch Require Import insert_after_pos_in_list_lifted.
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

Module Program_insert_after_pos_in_list <: ProgramInformation.
    Definition entry_addr : N := 0x8000000.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x8000024 => true
        | _ => false
    end | _ => false end.

    Definition binary := linked_list_insert_after_pos_in_list_armv6m.
End Program_insert_after_pos_in_list.

Module ARMv6MTiming := ARMv6MTiming cpu Program_insert_after_pos_in_list.
Module insert_after_pos_in_listAuto := ARMv6MTimingAutomation ARMv6MTiming.
Import Program_insert_after_pos_in_list insert_after_pos_in_listAuto.

Definition time_of_insert_after_pos_in_list
    (l value : addr) (pos : N) (len : nat) (t : trace) :=
  cycle_count_of_trace t =
    (tpush_base + 1 + 1) + tcmp_imm +
    if (l =? NULL) then tb_taken + (tpop_pc_base + 2) else (
        tb_not_taken + tcmp_imm +
        if (value =? NULL) then tb_taken + (tpop_pc_base + 2) else (
            tb_not_taken + tmovs_imm + tcmp_imm +
            if (pos =? 0) then (
                tb_not_taken + tb + tmovs_reg + tldr_imm + tb +
                tstr_imm + tstr_imm + (tpop_pc_base + 2)
            ) else (
                tb_taken +
                (* nodes passed over *)
                (N.min pos (N.of_nat len) - 1) * (
                    tmovs_reg + tldr_imm + tcmp_imm + tb_taken +
                    tadds_imm8 + tcmp_reg + tb_not_taken
                ) +
                (* the last node visited: either position pos was reached,
                   or the end of the list was *)
                tmovs_reg + tldr_imm + tcmp_imm +
                (if pos <? N.of_nat len then
                    tb_taken + tadds_imm8 + tcmp_reg + tb_taken +
                    tmovs_reg + tldr_imm + tb
                 else tb_not_taken) +
                tstr_imm + tstr_imm + (tpop_pc_base + 2)
            )
        )
    ).

Definition insert_after_pos_in_list_timing_invs
    (l value : addr) (pos : N) (len : nat) (lmin lmax : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000000 => Some (
        s R_R0 = l /\ s R_R1 = value /\ s R_R2 = pos /\
        node_distance (s V_MEM32) l NULL len /\
        LLBounds (s V_MEM32) l lmin lmax /\
        ~ overlap 32 (s R_SP ⊖ 8) 8 lmin (8 + lmax - lmin) /\
        cycle_count_of_trace t' = 0
    )
| 0x8000018 => Some (
        s R_R1 = value /\ s R_R2 = pos /\
        s R_R3 < pos /\
        s R_R3 < N.of_nat len /\
        node_distance (s V_MEM32) l (s R_R0) (N.to_nat (s R_R3)) /\
        node_distance (s V_MEM32) l NULL len /\
        (l =? NULL) = false /\
        (value =? NULL) = false /\
        (pos =? 0) = false /\
        cycle_count_of_trace t' =
            (tpush_base + 1 + 1) + tcmp_imm + tb_not_taken + tcmp_imm + tb_not_taken +
            tmovs_imm + tcmp_imm + tb_taken +
            (s R_R3) * (
                tmovs_reg + tldr_imm + tcmp_imm + tb_taken +
                tadds_imm8 + tcmp_reg + tb_not_taken
            )
    )
| 0x8000024 => Some (time_of_insert_after_pos_in_list l value pos len t)
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

Lemma next_of_nonnull :
    forall mem c, c <> NULL -> list_node_next mem c = Some (mem Ⓓ[4 + c]).
Proof.
    intros. unfold list_node_next. destruct c. contradiction. reflexivity.
Qed.

Theorem insert_after_pos_in_list_timing:
  forall s t s' x' l value pos len lmin lmax
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models armv6mtypctx s)
         (* bindings *)
         (R0: s R_R0 = l)
         (R1: s R_R1 = value)
         (R2: s R_R2 = pos)
         (LEN: node_distance (s V_MEM32) l NULL len)
         (* the registers pushed on entry don't overwrite the list *)
         (BOUNDS: LLBounds (s V_MEM32) l lmin lmax)
         (NO: ~ overlap 32 (s R_SP ⊖ 8) 8 lmin (8 + lmax - lmin)),
  satisfies_all
    lifted_prog
    (insert_after_pos_in_list_timing_invs l value pos len lmin lmax)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep armv6m_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto; lia.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped_lift_armv6m].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.
    - destruct PRE as (R0 & R1 & R2 & Len & Bounds & NO & Cycles).
        repeat step.
        -- (* l = NULL *) unfold NULL. hammer.
        -- (* value = NULL *) unfold NULL. hammer.
        -- (* pos = 0 *) unfold NULL. hammer.
        -- (* loop entry *)
            assert (LEN0: (0 < len)%nat).
                apply (node_distance_len_nonzero _ _ _ Len).
                rewrite Bool.negb_true_iff. assumption.
            repeat split; auto; try lia.
            constructor.
            eapply llsame_distance; [| exact Len].
            apply push2_llsame with (lmin := lmin) (lmax := lmax); assumption.
            hammer.
    - destruct PRE as (R1 & R2 & R3P & R3L & DstCurr & Len & LNN & VNN & PNZ & Cycles).
        (* the current node is in the list, so not NULL *)
        assert (CNN: s' R_R0 <> NULL).
            eapply dist_lt_null_not_null; try eassumption. lia.
        pose proof (distance_null_imp_well_formed _ _ _ Len) as WF.
        repeat step.
        -- (* the current node is the last: insert after it *)
            assert (LEN': len = S (N.to_nat (s' R_R3))). {
                eapply node_distance_uniq; [ exact Len |].
                eapply node_distance_next_S_len; try eassumption.
                rewrite next_of_nonnull by assumption. apply N.eqb_eq in BC. now rewrite BC.
            }
            unfold time_of_insert_after_pos_in_list. hammer.
            rewrite ?LNN, ?VNN, ?PNZ.
            replace (pos <? N.of_nat len) with false by (symmetry; apply N.ltb_ge; lia).
            replace (N.min pos (N.of_nat len)) with (1 + s' R_R3) by lia.
            lia.
        -- (* position pos reached: insert after the next node *)
            assert (NEXT: node_distance (s' V_MEM32) l (s' V_MEM32 Ⓓ[4 + s' R_R0]) (S (N.to_nat (s' R_R3)))).
                eapply node_distance_next_S_len; try eassumption.
                apply next_of_nonnull. assumption.
            assert (LT: (S (N.to_nat (s' R_R3)) < len)%nat). {
                pose proof (dist_node_le_dist_null _ _ _ _ _ Len NEXT).
                destruct (Nat.eq_dec (S (N.to_nat (s' R_R3))) len); [| lia].
                exfalso. apply N.eqb_neq in BC. apply BC.
                apply (node_distance_uniq' NEXT Len). assumption.
            }
            assert (POS: pos = 1 + s' R_R3). {
                apply N.eqb_eq in BC0. rewrite msub_nowrap in BC0 by (psimpl; lia).
                psimpl in BC0. lia.
            }
            unfold time_of_insert_after_pos_in_list. hammer.
            rewrite ?LNN, ?VNN, ?PNZ.
            replace (pos <? N.of_nat len) with true by (symmetry; apply N.ltb_lt; lia).
            replace (N.min pos (N.of_nat len)) with (1 + s' R_R3) by lia.
            lia.
        -- (* move to the next node *)
            assert (NEXT: node_distance (s' V_MEM32) l (s' V_MEM32 Ⓓ[4 + s' R_R0]) (S (N.to_nat (s' R_R3)))).
                eapply node_distance_next_S_len; try eassumption.
                apply next_of_nonnull. assumption.
            assert (LT: (S (N.to_nat (s' R_R3)) < len)%nat). {
                pose proof (dist_node_le_dist_null _ _ _ _ _ Len NEXT).
                destruct (Nat.eq_dec (S (N.to_nat (s' R_R3))) len); [| lia].
                exfalso. apply N.eqb_neq in BC. apply BC.
                apply (node_distance_uniq' NEXT Len). assumption.
            }
            assert (POS: pos <> 1 + s' R_R3). {
                apply N.eqb_neq in BC0. rewrite msub_nowrap in BC0 by (psimpl; lia).
                psimpl in BC0. lia.
            }
            assert (pos < 2^32). rewrite <- R2. apply (models_var R_R2 MDL).
            rewrite (N.mod_small (1 + s' R_R3)) by lia.
            repeat split; auto; try lia.
            replace (N.to_nat (1 + s' R_R3)) with (S (N.to_nat (s' R_R3))) by lia.
            exact NEXT.
            hammer.
Qed.

End TimingProof.

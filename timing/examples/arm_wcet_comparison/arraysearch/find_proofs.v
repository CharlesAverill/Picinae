From Picinae.timing.examples.arm_wcet_comparison.arraysearch Require Import find.
Require Import ARMv6MTiming.
Import ARMv6MNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : ARMv6MCPUTimingBehavior).
Import cpu.

Module Program_find <: ProgramInformation.
    Definition entry_addr : N := 0x8000000.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x8000024 => true
        | _ => false
    end | _ => false end.

    Definition binary := arraysearch_find_armv6m.
End Program_find.

Module ARMv6MTiming := ARMv6MTiming cpu Program_find.
Module findAuto := ARMv6MTimingAutomation ARMv6MTiming.
Import Program_find findAuto.

(* Element i of the array (of 64-bit integers) equals the key, given as its low
   and high words *)
Definition elem_eq (mem : memory) (arr : addr) (klo khi : N) (i : N) : Prop :=
    mem Ⓓ[arr + 8 * i] = klo /\ mem Ⓓ[arr + 8 * i + 4] = khi.

Definition key_in_array (mem : memory) (arr : addr) (klo khi : N) (len : N) : Prop :=
    exists i, i < len /\ elem_eq mem arr klo khi i.

(* The number of the first n elements whose low word equals the key's.  The
   loop compares an element's high word only when its low word matches. *)
Fixpoint partial_matches (mem : memory) (arr : addr) (klo : N) (n : nat) : N :=
    match n with
    | O => 0
    | S n' => partial_matches mem arr klo n' +
              (if mem Ⓓ[arr + 8 * N.of_nat n'] =? klo then 1 else 0)
    end.

Definition time_of_find (mem : memory) (arr : addr) (klo : N) (len : N)
        (found_idx : option N) (t : trace) :=
    cycle_count_of_trace t =
        (tpush_base + 2 + 1) + tcmp_imm +
        if len =? 0 then
            tb_taken + tldr_pc + (tpop_pc_base + 3)
        else
            tb_not_taken + tmovs_imm + tb +
            (* extra time for elements whose low word matches *)
            partial_matches mem arr klo
                (N.to_nat (match found_idx with None => len | Some idx => idx end)) *
                (tb_not_taken + tldr_imm + tcmp_reg) +
            match found_idx with
            | Some idx =>
                (* elements that don't match *)
                idx * (
                    tldr_imm + tcmp_reg + tb_taken +
                    tadds_imm8 + tadds_imm8 + tcmp_reg + tb_not_taken
                ) +
                (* the matching element *)
                tldr_imm + tcmp_reg + tb_not_taken + tldr_imm + tcmp_reg + tb_not_taken +
                tuxth + tb + (tpop_pc_base + 3)
            | None =>
                (* elements that don't match, except the last *)
                (len - 1) * (
                    tldr_imm + tcmp_reg + tb_taken +
                    tadds_imm8 + tadds_imm8 + tcmp_reg + tb_not_taken
                ) +
                (* the last element, after which the loop exits *)
                tldr_imm + tcmp_reg + tb_taken +
                tadds_imm8 + tadds_imm8 + tcmp_reg + tb_taken +
                tldr_pc + (tpop_pc_base + 3)
            end.

Definition timing_postcondition (mem : memory) (arr : addr)
        (klo khi : N) (len : N) (t : trace) : Prop :=
    (exists i, i < len /\ elem_eq mem arr klo khi i /\
        (* i is the first index where the key is found *)
        (forall j, j < i -> ~ elem_eq mem arr klo khi j) /\
        time_of_find mem arr klo len (Some i) t) \/
    (~ key_in_array mem arr klo khi len /\
        time_of_find mem arr klo len None t).

Definition find_timing_invs (base_mem : memory)
    (arr : addr) (klo khi : N) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000000 => Some (s V_MEM32 = base_mem /\
               s R_R0 = arr /\ s R_R1 = len /\ s R_R2 = klo /\ s R_R3 = khi /\
               len < 2^16 /\
               ~ overlap 32 (s R_SP ⊖ 12) 12 arr (8 * len) /\
               cycle_count_of_trace t' = 0)
| 0x8000012 => Some (
    s R_R0 = arr ⊕ 8 * s R_R4 /\ s R_R1 = len /\ s R_R2 = klo /\ s R_R3 = khi /\
    0 < len < 2^16 /\
    (* preservation *)
    (forall i, i < len ->
        (s V_MEM32) Ⓓ[arr + 8 * i] = base_mem Ⓓ[arr + 8 * i] /\
        (s V_MEM32) Ⓓ[arr + 8 * i + 4] = base_mem Ⓓ[arr + 8 * i + 4]) /\
    (* haven't found a match yet *)
    (forall i, i < s R_R4 -> ~ elem_eq base_mem arr klo khi i) /\
    s R_R4 < len /\
    cycle_count_of_trace t' =
        (tpush_base + 2 + 1) + tcmp_imm + tb_not_taken + tmovs_imm + tb +
        partial_matches base_mem arr klo (N.to_nat (s R_R4)) *
            (tb_not_taken + tldr_imm + tcmp_reg) +
        s R_R4 * (
            tldr_imm + tcmp_reg + tb_taken +
            tadds_imm8 + tadds_imm8 + tcmp_reg + tb_not_taken
        )
    )
| 0x8000024 => Some (timing_postcondition base_mem arr klo khi len t)
| _ => None end | _ => None end.

(* The three words pushed on entry don't overwrite the array. *)
Lemma push3_preserves :
    forall m sp arr len i k v1 v2 v3
        (NO: ~ overlap 32 (sp ⊖ 12) 12 arr (8 * len)) (I: i < len) (K: k + 4 <= 8),
    m [Ⓓ sp ⊖ 12 := v1] [Ⓓ sp ⊖ 8 := v2] [Ⓓ sp ⊖ 4 := v3] Ⓓ[arr + 8 * i + k] =
    m Ⓓ[arr + 8 * i + k].
Proof.
    intros.
    assert (SP: forall c, c <= 12 -> sp ⊖ c = ((sp ⊖ 12) + (12 - c)) mod 2^32). {
        intros. unfold msub. rewrite N.Div0.add_mod_idemp_l.
        f_equal. rewrite (N.mod_small c) by lia. rewrite (N.mod_small 12) by lia. lia.
    }
    rewrite !getmem_noverlap; [ reflexivity | .. ];
    match goal with |- ~ overlap _ _ _ (msub _ _ ?c) _ => rewrite (SP c) by lia end;
    rewrite overlap_mod_r, <- N.add_assoc;
    apply noverlap_index_index with (len1 := 8 * len) (len2 := 12); try lia;
    apply noverlap_symmetry, NO.
Qed.

Lemma partial_matches_succ :
    forall mem arr klo i,
    partial_matches mem arr klo (N.to_nat (1 + i)) =
    partial_matches mem arr klo (N.to_nat i) + (if mem Ⓓ[arr + 8 * i] =? klo then 1 else 0).
Proof.
    intros. rewrite N.add_1_l, N2Nat.inj_succ. simpl. rewrite N2Nat.id. reflexivity.
Qed.

Theorem find_timing:
  forall s (t : trace) s' x' base_mem arr klo khi len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models armv6mtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_R0 = arr)
         (A1: s R_R1 = len)
         (A2: s R_R2 = klo)
         (A3: s R_R3 = khi)
         (LEN_RANGE: len < 2^16)
         (* the registers pushed on entry don't overwrite the array *)
         (NO: ~ overlap 32 (s R_SP ⊖ 12) 12 arr (8 * len)),
  satisfies_all
    lifted_prog
    (find_timing_invs base_mem arr klo khi len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep armv6m_step.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped_lift_armv6m].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.
    - destruct PRE as (Mem & A0 & A1 & A2 & A3 & LEN_VALID & NO & Cycles).
        repeat step.
        -- (* len = 0: return -1 *)
            replace len with 0 in * by lia. right.
            split. intros (i & Contra & _). lia.
            unfold time_of_find. hammer.
        -- (* loop entry *)
            repeat split; auto; try lia.
            (* preservation *)
            intros. rewrite ?Mem.
                replace (arr + 8 * i) with (arr + 8 * i + 0) by lia.
                apply push3_preserves with (len := len); auto; lia.
            intros. rewrite ?Mem. apply push3_preserves with (len := len); auto; lia.
            (* cycles *)
            hammer. simpl (partial_matches _ _ _ (N.to_nat 0)). lia.
    - destruct PRE as (A0 & A1 & A2 & A3 & LEN_VALID & Preserved & NotFound & I_LEN & Cycles).
        repeat step.
        all: try rewrite (N.mod_small (1 + s' R_R4)) in * by lia.
        all: try replace (4 + arr + 8 * s' R_R4) with (arr + 8 * s' R_R4 + 4) in * by lia.
        all: destruct (Preserved (s' R_R4) I_LEN) as (PLo & PHi).
        -- (* both words match: found *)
            left. exists (s' R_R4). split. assumption.
            split. split.
                rewrite <- PLo. apply N.eqb_eq, BC.
                rewrite <- PHi. apply N.eqb_eq, BC0.
            split. assumption.
            unfold time_of_find. hammer.
            replace (len =? 0) with false by (symmetry; apply N.eqb_neq; lia). lia.
        -- (* low word matches, last element: not found *)
            right. split.
                intros (j & Jlen & EQlo & EQhi).
                assert (j = s' R_R4 \/ j < s' R_R4) as [J|J] by (apply N.leb_le in BC1; lia).
                    subst j. rewrite <- PHi in EQhi. apply N.eqb_neq in BC0. contradiction.
                    apply (NotFound j J). split; assumption.
            unfold time_of_find. hammer.
            assert (LEN: len = 1 + s' R_R4) by (apply N.leb_le in BC1; lia).
            replace (len =? 0) with false by (symmetry; apply N.eqb_neq; lia).
            rewrite LEN, partial_matches_succ, <- PLo, BC. lia.
        -- (* low word matches: continue *)
            apply N.leb_gt in BC1.
            repeat split; auto; try lia.
                1,2: match goal with H: ?j < _ |- _ => destruct (Preserved j H); assumption end.
                intros j J (EQlo & EQhi).
                assert (j = s' R_R4 \/ j < s' R_R4) as [J'|J'] by lia.
                    subst j. rewrite <- PHi in EQhi. apply N.eqb_neq in BC0. contradiction.
                    apply (NotFound j J'). split; assumption.
                hammer. rewrite partial_matches_succ, <- PLo, BC. lia.
        -- (* low word doesn't match, last element: not found *)
            right. split.
                intros (j & Jlen & EQlo & EQhi).
                assert (j = s' R_R4 \/ j < s' R_R4) as [J|J] by (apply N.leb_le in BC0; lia).
                    subst j. rewrite <- PLo in EQlo. apply N.eqb_neq in BC. contradiction.
                    apply (NotFound j J). split; assumption.
            unfold time_of_find. hammer.
            assert (LEN: len = 1 + s' R_R4) by (apply N.leb_le in BC0; lia).
            replace (len =? 0) with false by (symmetry; apply N.eqb_neq; lia).
            rewrite LEN, partial_matches_succ, <- PLo, BC. lia.
        -- (* low word doesn't match: continue *)
            apply N.leb_gt in BC0.
            repeat split; auto; try lia.
                1,2: match goal with H: ?j < _ |- _ => destruct (Preserved j H); assumption end.
                intros j J (EQlo & EQhi).
                assert (j = s' R_R4 \/ j < s' R_R4) as [J'|J'] by lia.
                    subst j. rewrite <- PLo in EQlo. apply N.eqb_neq in BC. contradiction.
                    apply (NotFound j J'). split; assumption.
                hammer. rewrite partial_matches_succ, <- PLo, BC. lia.
Qed.

End TimingProof.

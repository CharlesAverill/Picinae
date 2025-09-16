Require Import array.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_find_in_array <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x208 => true
        | _ => false
    end | _ => false end.

    Definition binary := array_bin.
End Program_find_in_array.

Module RISCVTiming := RISCVTiming cpu Program_find_in_array.
Module find_in_arrayAuto := RISCVTimingAutomation RISCVTiming.
Import Program_find_in_array find_in_arrayAuto.

Definition key_in_array (mem : memory) (arr : addr) (key : N) (len : N) : Prop :=
    exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key.

Lemma lt_impl_lt_or_eq : forall x y,
    x < 1 + y -> x = y \/ x < y.
Proof. lia. Qed.

Definition N_peano_ind_Set (P : N -> Set) := N.peano_rect P.

Fixpoint key_in_array_dec (mem : memory) (arr : addr) (key len : N)
        : {key_in_array mem arr key len} + {~ key_in_array mem arr key len}.
    induction len using N_peano_ind_Set.
    - right. intro. destruct H as (idx & Contra & _). lia.
    - destruct IHlen as [IN | NOT_IN].
        -- left. destruct IN as (idx & Lt & Eq). exists idx.
            split. lia. assumption.
        -- destruct (N.eq_dec (mem Ⓓ[arr + (len << 2)]) key).
            + left. exists len. split. lia. assumption.
            + right. intro. destruct H as (idx & Lt & Eq).
                assert (idx = len). {
                destruct (lt_impl_lt_or_eq idx len). lia.
                    subst. reflexivity.
                exfalso. apply NOT_IN. exists idx. now split.
                } subst. contradiction.
Qed.

Definition time_of_find_in_array (len : N) (found_idx : option N) (t : trace) :=
    cycle_count_of_trace t =
        (* setup time *)
        taddi +
        (* loop iterations *)
        (match found_idx with None => len | Some i => i end) *
        (* loop body duration *)
        (tfbgeu + tslli 2 + tadd + tlw + tfbeq + taddi + tjal) +
        (* partial loop iteration before loop exit *)
        (match found_idx with 
         | None => ttbgeu
         | Some _ => tfbgeu + tslli 2 + tadd + tlw + ttbeq
         end) +
        (* shutdown time *)
        taddi + tjalr.

Definition timing_postcondition (mem : memory) (arr : addr)
        (key : N) (len : N) (t : trace) : Prop :=
    (exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key /\
        (* i is the first index where the key is found *)
        (forall j, j < i -> mem Ⓓ[arr + (j << 2)] <> key) /\
        time_of_find_in_array len (Some i) t) \/
    ((~ exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key) /\
        time_of_find_in_array len None t).

Definition tbgeu (rs1 rs2 : N) : N :=
    if negb (rs1 <? rs2) then ttbgeu else tfbgeu.

Definition find_in_array_timing_invs (s : store) (base_mem : memory)
    (sp : N) (arr : addr) (key : N) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (s V_MEM32 = base_mem /\ s R_A0 = arr /\ s R_A1 = key /\ 
            s R_A2 = len /\ 4 * len <= 2^32 - 1 /\
            cycle_count_of_trace t' = 0)
| 0x1e8 => Some (exists mem a5,
    (* bindings *)
    s V_MEM32 = mem /\
    s R_A0 = arr /\ s R_A1 = key /\ s R_A2 = len /\
    s R_A5 = a5 /\
    (* preservation *)
    (forall i, i < len ->
        mem Ⓓ[arr + (i << 2)] = base_mem Ⓓ[arr + (i << 2)]) /\
    (* haven't found a match yet *)
    (forall i, i < a5 ->
        mem Ⓓ[arr + (i << 2)] <> key) /\
    a5 <= len /\
    cycle_count_of_trace t' =
        (* pre-loop time *)
        taddi +
        (* loop counter stored in register a5 *)
        a5 *
        (* full loop body length - can't have broken out by this address *)
        (tfbgeu + tslli 2 + tadd + tlw + tfbeq + taddi + tjal)
    )
| 0x208 => Some (timing_postcondition base_mem arr key len t)
| _ => None end | _ => None end.

Theorem find_in_array_timing:
  forall s t s' x' base_mem sp arr key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (SP: s R_SP = sp)
         (A0: s R_A0 = arr)
         (A1: s R_A1 = key)
         (A2: s R_A2 = len)
         (* length must fit inside the address space, arr is 4-byte integers *)
         (LEN_VALID: 4 * len <= 2^32 - 1),
  satisfies_all 
    lifted_prog
    (find_in_array_timing_invs s base_mem sp arr key len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac generalize_timing_trace Heq TSI l a s t :=
        let x := fresh "x" in
        remember ((Addr a, _) :: t) as l eqn:Heq;
        (* I promise this is necessary *)
        (* if instead eassert is used, it likes to try and *)
        (* fill in the hole on its own. *)
        evar (x : N);
        assert (cycle_count_of_trace l = x) as TSI by
            (rewrite Heq; hammer; psimpl;
            match goal with
            | [|- ?v = x] => instantiate (x := v)
            end; reflexivity);
        subst x.
    Local Ltac step := time r5_step;
        match goal with
        (* After a step has already been taken *)
        | [t: list (exit * store), 
           TSI: cycle_count_of_trace ?t = ?x
            |- context[_ :: (Addr ?a, ?s) :: ?t]] =>
            let Heq := fresh "Heq" in
            let H0 := fresh "TSI" in
            let l := fresh "t" in
            generalize_timing_trace Heq H0 l a s t;
            clear Heq TSI;
            try clear t;
            rename H0 into TSI
        | _ => idtac
        end.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    (* 0x101b0 -> 0x101e0 *)
    destruct PRE as (Mem & A0 & A1 & A2 & LEN_VALID & Cycles).
    repeat step.
        repeat eexists; auto.
        (* preservation *) intros; now rewrite Mem.
        (* key not found yet *) intros; lia.
        (* idx <= len *) psimpl; lia.
        (* cycles *) hammer.

    destruct PRE as (mem & a5 & MEM & A0 & A1 & A2 & A5 & Preserved &
        NotFound & A5_LEN & Cycles).
    destruct (key_in_array_dec mem arr key len) as [IN | NOT_IN].
    (* There is a matching element in the array *) {
        step. repeat step.
        (* postcondition, match found *)
            left. exists a5. split.
                now apply N.ltb_lt. 
            split.
                rewrite <- Preserved. now apply N.eqb_eq in BC0.
                now apply N.ltb_lt in BC. 
            split.
                intros. rewrite <- Preserved by lia. now apply NotFound.
            unfold time_of_find_in_array.
            hammer.
        (* loop invariant after going around *)
            repeat eexists; auto.
            (* key not found *)
            intros. apply N.ltb_lt in BC.
                rewrite N.mod_small in H. destruct (lt_impl_lt_or_eq _ _ H).
                subst. now apply N.eqb_neq in BC0. now apply NotFound.
                apply N.le_lt_trans with len. lia.
                rewrite <- A2; apply (models_var R_A2 MDL).
            (* 1 + a5 <= len *)
            apply N.ltb_lt in BC. rewrite N.mod_small. lia.
                apply N.le_lt_trans with len. lia.
                rewrite <- A2; apply (models_var R_A2 MDL).
            (* cycles *)
            rewrite (N.mod_small (1 + a5)). hammer.
                apply N.ltb_lt in BC.
                apply N.le_lt_trans with len. lia.
                rewrite <- A2; apply (models_var R_A2 MDL).
        (* iterated len times - contradiction *)
        exfalso. destruct IN as (idx & IDX_LEN & IN).
            apply (NotFound idx). apply N.ltb_ge in BC. lia.
            assumption.
    }

    (* There is not a matching element in the array *) {
        step.
        do 4 step.
        (* contradiction - BC0 says a match has been found *)
            exfalso. apply NOT_IN. exists a5. split. now apply N.ltb_lt.
            apply N.eqb_eq in BC0.
            assumption.
        (* a match has not been found, continue *)
        repeat step.
            repeat eexists; auto.
            (* key not found *)
            intros. apply N.ltb_lt in BC.
                rewrite N.mod_small in H. destruct (lt_impl_lt_or_eq _ _ H).
                subst. now apply N.eqb_neq in BC0. now apply NotFound.
                apply N.le_lt_trans with len. lia.
                rewrite <- A2; apply (models_var R_A2 MDL).
            (* 1 + a5 <= len *)
            apply N.ltb_lt in BC. rewrite N.mod_small. lia.
                apply N.le_lt_trans with len. lia.
                rewrite <- A2; apply (models_var R_A2 MDL).
            (* cycles *)
            rewrite (N.mod_small (1 + a5)). hammer.
                apply N.ltb_lt in BC.
                apply N.le_lt_trans with len. lia.
                rewrite <- A2; apply (models_var R_A2 MDL).
        (* a match has not been found, break and return *)
        repeat step.
            unfold timing_postcondition, time_of_find_in_array. right.
            split. intro. apply NOT_IN. destruct H as (idx & IDX_LEN & IN).
            exists idx. split. assumption. now rewrite Preserved.
            replace a5 with len in * by
                (rewrite N.ltb_ge in BC; lia).
            hammer.
    }
Qed.

End TimingProof.

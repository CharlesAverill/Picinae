Require Import array.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Variable ML : N.
Variable ML_pos : 1 <= ML.

Definition time_mem : N :=
    5 + (ML - 2).
Definition time_branch : N :=
    5 + (ML - 1).

Module find_in_arrayTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (array_bin a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x101b0.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x10214 => true
    | _ => false
  end | _ => false end.
End find_in_arrayTime.

Module find_in_arrayAuto := TimingAutomation find_in_arrayTime.
Import find_in_arrayTime find_in_arrayAuto.

Definition key_in_array (mem : addr -> N) (arr : addr) (key : N) (len : N) : Prop :=
    exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key.

Definition mem_layout (sp : N) (arr : addr) (len : N) :=
    create_noverlaps [(4, sp ⊖ 4); (4, sp ⊖ 8); 
                      (4, sp ⊖ 20); (4, sp ⊖ 36); 
                      (4, sp ⊖ 40); (4, sp ⊖ 44); 
                      (4 * len, arr)].

Definition time_of_find_in_array (mem : addr -> N) 
        (arr : addr) (key : N) (len : N) (found_idx : option N)
        (t : trace) :=
    cycle_count_of_trace t =
        (* setup time *)
        4 + 10 * time_mem +
        (* loop iterations *)
        (match found_idx with None => len | Some i => i end) *
        (* loop body duration *)
        (10 + (3 + (2/4) + (2 mod 4)) + time_mem + time_branch) +
        (* partial loop iteration in found case *)
        (match found_idx with None => time_branch (* loop condition fail *)
         | _ => 3 + (3 + (2/4) + (2 mod 4)) + 2 + time_mem + time_branch
         end) +
        (* shutdown time *)
        2 * time_mem + 2 + 2 * time_mem + 2 + time_branch.

Definition timing_postcondition (mem : addr -> N) (arr : addr)
        (key : N) (len : N) (t : trace) : Prop :=
    (exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key /\
        (forall j, j < i -> mem Ⓓ[arr + (j << 2)] <> key) /\
        time_of_find_in_array mem arr key len (Some i) t) \/
    ((~ exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key) /\
        time_of_find_in_array mem arr key len None t).

Definition find_in_array_timing_invs (s : store) (base_mem : addr -> N)
    (sp : N) (arr : addr) (key : N) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x101b0 => Some (mem_layout sp arr len /\ s V_MEM32 = Ⓜbase_mem /\
            s R_SP = Ⓓsp /\
            s R_A0 = Ⓓarr /\ s R_A1 = Ⓓkey /\ s R_A2 = Ⓓlen /\
            (key_in_array base_mem arr key len \/ ~ key_in_array base_mem arr key len) /\
            4 * len < 2^32 - 1 /\
            cycle_count_of_trace t' = 0)
| 0x101e0 => Some (mem_layout sp arr len /\ exists mem a5,
    (* bindings *)
    s R_S0 = Ⓓsp /\ s R_A2 = Ⓓlen /\ s R_A3 = Ⓓkey /\
    s R_A4 = Ⓓarr /\ s R_A5 = Ⓓa5 /\ s V_MEM32 = Ⓜmem /\
    (* preservation *)
    (forall i, i < len ->
        mem Ⓓ[arr + (i << 2)] = base_mem Ⓓ[arr + (i << 2)]) /\
    (* haven't found a match yet *)
    (forall i, i < a5 ->
        mem Ⓓ[arr + (i << 2)] <> key) /\
    (key_in_array base_mem arr key len \/ ~ key_in_array base_mem arr key len) /\
    a5 <= len /\
    cycle_count_of_trace t' =
        (* pre-loop time *)
        4 + 10 * time_mem +
        (* loop counter stored in register a5 *)
        a5 *
        (* full loop body length - can't have broken out by this address *)
        (10 + (3 + (2/4) + (2 mod 4)) + time_mem + time_branch)
    )
| 0x10214 => Some (timing_postcondition base_mem arr key len t)
| _ => None end | _ => None end.

Definition lifted_find_in_array : program :=
    lift_riscv array_bin.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Ltac fold_big_subs :=
    repeat match goal with
    | [ |- context[?M [Ⓓ ?X + ?B + ?N := ?V]] ] =>
      rewrite <-(setmem_mod_l _ _ _ M (X+B+N) V);
      replace (M [ⒹX+B⊕N := V]) with
        (M [Ⓓ(msub 32 B (2^32 - X)) ⊕ N := V]) by
        (unfold msub; now psimpl);
      simpl (2^32 - X)
    | [ |- context[?M [Ⓓ?X + ?Y := ?V]]] =>
      rewrite <- setmem_mod_l with (a := X + Y);
      replace (X⊕Y) with (msub 32 Y (2^32 - X)) by (now rewrite N.add_comm);
      simpl (2^32 - X)
    | [ |- context[?M Ⓓ[ ?X + ?B + ?N]] ] =>
      rewrite <-(getmem_mod_l _ _ _ M (X+B+N));
      replace (M Ⓓ[X+B⊕N]) with
        (M Ⓓ[(msub 32 B (2^32 - X)) ⊕ N]) by
        (unfold msub; now psimpl);
      simpl (2^32 - X)
    | [ |- context[?M Ⓓ[?X + ?Y]]] =>
      rewrite <- getmem_mod_l with (a := X + Y);
      replace (X⊕Y) with (msub 32 Y (2^32 - X)) by (now rewrite N.add_comm);
      simpl (2^32 - X)
    end.

Lemma lt_impl_lt_or_eq : forall x y,
    x < 1 + y -> x = y \/ x < y.
Proof. lia. Qed.

Theorem find_in_array_timing:
  forall s t s' x' base_mem sp arr key len
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (SP: s R_SP = Ⓓsp)
         (A0: s R_A0 = Ⓓarr)
         (A1: s R_A1 = Ⓓkey)
         (A2: s R_A2 = Ⓓlen)
         (IN: key_in_array base_mem arr key len \/ ~ key_in_array base_mem arr key len)
         (MEMLAYOUT: mem_layout sp arr len)
         (LEN_VALID: 4 * len < 2^32 - 1),
  satisfies_all 
    lifted_find_in_array
    (find_in_array_timing_invs s base_mem sp arr key len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    split. unfold mem_layout in *. noverlaps_preserved idtac.
    now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (Layout & Mem & SP & A0 & A1 & A2 & IN & 
        LEN_VALID & Cycles).
    repeat step.
        split. 
        (* noverlaps *)
        unfold mem_layout in *; noverlaps_preserved idtac. 
        repeat eexists.
        (* preservation *)
        intros.
            unfold mem_layout in *. unfold_create_noverlaps.
            fold_big_subs.
            repeat rewrite getmem_noverlap. reflexivity.
            1-6:
                rewrite N.shiftl_mul_pow2;
                eapply noverlap_shrink with (a1 := arr) (len1 := 4 * len);
                    auto using noverlap_symmetry;
                    psimpl; rewrite N.mod_small; lia.
        (* key not found yet *)
        intros. lia.
        (* key in or not in *) assumption. (* idx <= len *) psimpl; lia.
        (* cycles *)
        hammer. find_rewrites. unfold time_mem, time_branch. lia.

    destruct PRE as (Layout & mem & a5 & S0 & A2 & A3 & A4 & A5 & 
        MEM & Preserved & NotFound & IN_OR_NOT & LEN & Cycles).
    destruct IN_OR_NOT as [IN | NOT_IN].
    (* There is a matching element in the array *) {
        step.
        repeat step.
        (* postcondition after loop condition fail *)
            left.
            exists a5. split. now apply N.ltb_lt. split. 
            rewrite <- Preserved. now apply N.eqb_eq in BC0.
            now apply N.ltb_lt in BC. split.
            intros. rewrite <- Preserved. now apply NotFound. lia.
            unfold time_of_find_in_array.
            hammer. find_rewrites. change (2/4) with 0. 
            unfold time_mem, time_branch. psimpl. lia.
        (* loop invariant after going around *)
            split. unfold mem_layout in *. noverlaps_preserved idtac.
            repeat eexists; auto.
            (* key not found *)
            intros. apply N.ltb_lt in BC.
                rewrite N.mod_small in H. destruct (lt_impl_lt_or_eq _ _ H).
                subst. now apply N.eqb_neq in BC0. now apply NotFound.
                apply N.le_lt_trans with len. lia. apply (rv_regsize MDL A2).
            (* 1 + a5 <= len *)
            apply N.ltb_lt in BC. rewrite N.mod_small. lia.
            apply N.le_lt_trans with len. lia. apply (rv_regsize MDL A2).
            (* cycles *)
            hammer. find_rewrites.
            unfold time_mem, time_branch. psimpl.
            change (2/4) with 0.
            rewrite N.mod_small. lia.
                apply Bool.negb_false_iff, N.ltb_lt in BC.
                apply N.le_lt_trans with len. lia.
                apply (rv_regsize MDL A2).
        (* iterated len times - contradiction *)
        exfalso. destruct IN as (idx & IDX_LEN & IN).
            apply (NotFound idx). apply N.ltb_ge in BC. lia.
            now rewrite Preserved.
    }

    (* There is not a matching element in the array *) {
        step.
        do 4 step.
        (* contradiction - BC0 says a match has been found *)
            exfalso. apply NOT_IN. exists a5. split. now apply N.ltb_lt.
            rewrite <- Preserved. apply N.eqb_eq in BC0.
            assumption. now apply N.ltb_lt in BC.
        (* a match has not been found, continue *)
        repeat step. split.
            unfold mem_layout in *. noverlaps_preserved idtac.
            repeat eexists; auto.
            (* key not found *)
            intros. apply N.ltb_lt in BC.
                rewrite N.mod_small in H. destruct (lt_impl_lt_or_eq _ _ H).
                subst. now apply N.eqb_neq in BC0. now apply NotFound.
                apply N.le_lt_trans with len. lia. apply (rv_regsize MDL A2).
            (* 1 + a5 <= len *)
                apply N.ltb_lt in BC. rewrite N.mod_small. lia.
                apply N.le_lt_trans with len. lia. apply (rv_regsize MDL A2).
            (* cycles *)
            hammer. find_rewrites.
            unfold time_mem, time_branch. psimpl.
            change (2/4) with 0.
            rewrite N.mod_small. lia.
                apply Bool.negb_false_iff, N.ltb_lt in BC.
                apply N.le_lt_trans with len. lia.
                apply (rv_regsize MDL A2).
        (* a match has not been found, break and return *)
        repeat step.
            unfold timing_postcondition, time_of_find_in_array. right.
            split. intro. apply NOT_IN. destruct H as (idx & IDX_LEN & H).
            exists idx. auto.
            hammer. find_rewrites. replace a5 with len in *.
            (* 4 + 2 * time_branch + 4 * time_mem *)
            unfold time_mem, time_branch. change (2/4) with 0. 
            psimpl. lia.
            rewrite Bool.negb_true_iff, N.ltb_ge in BC. lia.
    }
Qed.


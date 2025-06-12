Require Import riscvTiming.
Require Export List.
Require Export Bool.
Export ListNotations.

Module Type TimingModule.
    Parameter time_of_addr : store -> addr -> N.
    Parameter entry_addr : N.
    Parameter exits : trace -> bool.
End TimingModule.

Module TimingAutomation (tm : TimingModule).

Export Lia.

Definition cycle_count_of_trace := cycle_count_of_trace tm.time_of_addr.

Ltac unfold_decompose :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype 
        decompose_Stype decompose_Utype mask_bit_section]; cbn [N.land].
Tactic Notation "unfold_decompose" "in" hyp(H) :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype 
        decompose_Stype decompose_Utype mask_bit_section] in H; cbn [N.land] in H.
Ltac unfold_time_of_addr :=
    cbv [tm.time_of_addr neorv32_cycles_upper_bound]; cbn - [setmem getmem].
Tactic Notation "unfold_time_of_addr" "in" hyp(H) :=
    cbv [tm.time_of_addr neorv32_cycles_upper_bound] in H; cbn - [setmem getmem].
Ltac unfold_cycle_count_list :=
    unfold cycle_count_of_trace; repeat rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single; fold cycle_count_of_trace.
Ltac hammer :=
    unfold_cycle_count_list; unfold_time_of_addr; unfold_decompose; psimpl; try lia.

Ltac find_rewrites :=
    repeat (match goal with
    | [H: ?x = _ |- context[match ?x with _ => _ end]] =>
        rewrite H; cbn [negb]
    | [H: negb ?x = ?y |- context[if ?x then _ else _]] =>
        (match y with 
        | true => apply Bool.negb_true_iff in H 
        | false => apply Bool.negb_false_iff in H
        end);
        rewrite H; cbn [negb]
    | [H: cycle_count_of_trace ?t = _ |- context[cycle_count_of_trace ?t]] =>
        rewrite H
    end).

Ltac handle_ex := 
    repeat (match goal with
    | [|- exists _, _] => eexists
    end); repeat split; try eassumption.

Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

End TimingAutomation.

(* Memory layout 

   Basically, for each (size, addr) pair in a list l of buffers,
   the pair does not overlap with any pair in the tail of l.
   Warning: there should not be duplicates in the list of buffers!
   If there are, you will introduce unsoundness.
*)
Fixpoint _create_noverlaps (l : list (N * addr)) (idx : nat) : Prop :=
    match l with
    | [] => True
    | (size, addr) :: t => snd (fold_left 
        (fun acc item => 
            let '(idx', P) := acc in 
            let '(size', addr') := item in 
            (S idx',
                if (idx =? idx')%nat then P else
                    P /\ ~overlap 32 addr size addr' size')
        ) l (idx, True)) /\ _create_noverlaps t (S idx)
    end.
Definition create_noverlaps (l : list (N * addr)) : Prop :=
    _create_noverlaps l 0.

Ltac unfold_create_noverlaps unfolds :=
    unfolds;
    match goal with
    | [H: create_noverlaps _ |- _] =>
        unfold create_noverlaps, _create_noverlaps in H; 
        unfolds;
        cbn [map fold_left snd Nat.eqb] in H;
        psimpl in H;
        repeat (match goal with [H: _ /\ _ |- _] => destruct H end)
    end;
    repeat match goal with [H: True |- _] => clear H end;
    unfolds.

Ltac noverlaps_preserved unfolds :=
    unfolds;
    match goal with
    | [H: create_noverlaps _ |- create_noverlaps _] => 
        solve [unfold_create_noverlaps unfolds;
                  repeat split;
                  repeat rewrite getmem_noverlap; auto using noverlap_symmetry]
    | _ => fail "Goal must be in form of create_noverlaps l -> create_noverlaps l'"
    end.

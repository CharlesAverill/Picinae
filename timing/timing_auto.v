Require Import riscvTiming.
Require Export List.
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
        rewrite H
    | [H: ?x = _ |- context[if ?x then _ else _]] =>
        rewrite H
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

(* Memory layout *)
Fixpoint create_noverlaps (l l' : list (N * addr)) : Prop :=
    match l' with
    | [] => True
    | (size, addr) :: t => (fold_left 
        (fun P item => 
            match item with (size', addr') =>
            P /\ ~ overlap 32 addr size addr' size'
            end) l True) /\ create_noverlaps l t
    end.

Ltac unfold_create_noverlaps unfolds :=
    unfolds;
    match goal with
    | [H: create_noverlaps _ _ |- _] =>
        unfold create_noverlaps in H; cbn [map fold_left] in H;
        repeat (match goal with [H: _ /\ _ |- _] => destruct H end)
    | [H: let _ := _ in create_noverlaps _ _ |- _] =>
        unfold create_noverlaps in H; cbn [map fold_left] in H;
        repeat (match goal with [H: _ /\ _ |- _] => destruct H end)
    end;
    repeat match goal with [H: True |- _] => clear H end.

Ltac noverlaps_preserved unfolds :=
    solve [unfold_create_noverlaps unfolds; unfolds;
           repeat split;
           repeat rewrite getmem_noverlap; auto].

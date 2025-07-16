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
    | [H: ?x = ?y |- context[if negb ?x then _ else _]] =>
        (match y with
        | true => apply Bool.negb_false_iff in H
        | false => apply Bool.negb_true_iff in H
        end);
        rewrite H; cbn [negb]
    | [H: cycle_count_of_trace ?t = _ |- context[cycle_count_of_trace ?t]] =>
        rewrite H
    end).

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
Ltac unfold_latencies :=
    unfold T_shift_latency, T_mul_latency, CPU_FAST_SHIFT_EN, CPU_FAST_MUL_EN in *.
Ltac hammer :=
    unfold_cycle_count_list; unfold_time_of_addr; unfold_decompose;
        unfold_latencies;
        psimpl; find_rewrites; try lia.

Ltac handle_ex := 
    repeat (match goal with
    | [|- exists _, _] => eexists
    end); repeat (split; [solve [eauto]|]).

Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

End TimingAutomation.

(* Memory layout 

   Basically, for each (size, addr) pair in a list l of buffers,
   the pair does not overlap with any pair in the tail of l.
   Warning: there should not be duplicates in the list of buffers!
   If there are, you will introduce unsoundness.
*)
Fixpoint create_noverlaps (l : list (N * addr)) : Prop :=
    match l with
    | [] => True
    | (size, addr) :: t => fold_left 
        (fun P item =>
            let '(size', addr') := item in 
            P /\ ~overlap 32 addr size addr' size'
        ) t True /\ create_noverlaps t
    end.

(* Split a create_noverlaps hypothesis into all of its ~ overlap _ _ _ _ 
   constituents *)
Ltac unfold_create_noverlaps :=
    match goal with
    | [H: create_noverlaps _ |- _] =>
        unfold create_noverlaps in *; 
        cbn [fold_left] in H;
        repeat rewrite getmem_mod_l in H;
        repeat rewrite getmem_mod_r in H;
        repeat rewrite overlap_mod_l in H;
        repeat rewrite overlap_mod_r in H;
        repeat (
            match goal with 
            [H: _ /\ _ |- _] =>
                destruct H
            end
        )
    end;
    (* We'll end up with a ton of True hypotheses, so get rid of them *)
    repeat match goal with [H: True |- _] => clear H end.

Ltac solve_single_noverlap :=
    cbn [map fold_left snd Nat.eqb];
    
    (* These all get in the way of auto *)
    repeat rewrite getmem_noverlap; 
    repeat rewrite getmem_mod_l;
    repeat rewrite getmem_mod_r;
    repeat rewrite overlap_mod_l;
    repeat rewrite overlap_mod_r;

    auto using noverlap_symmetry.

Ltac _count_conj expr n :=
    match expr with
    | ?X /\ ?Y =>
        let n' := eval compute in (n + 1) in 
        let x := _count_conj X constr:(0) in 
        let y := _count_conj Y constr:(0) in
        eval compute in (n' + x + y)
    | _ => n
    end.
Ltac count_conj :=
    match goal with
    | [|- ?X] =>
        _count_conj X 0
    end.

Ltac solve_noverlaps n total :=
    idtac "solved " n " / " total " noverlaps";
    match goal with 
    | [|- _ /\ _] =>
        split; [
            solve_single_noverlap 
            | solve_noverlaps ltac:(eval compute in (n+1)) total ]
    | [|- _] => solve_single_noverlap
    end.

(* Prove that noverlaps are preserved *)
Ltac noverlaps_preserved unfolds :=
    unfolds;
    match goal with
    | [H: create_noverlaps _ |- create_noverlaps _] => 
        (idtac "Unfolding create_noverlaps";
         unfold_create_noverlaps;
         unfolds;
         idtac "Solving noverlaps";
         let conjs := ltac:(count_conj) in
         repeat (solve_noverlaps 0 conjs))
        (* idtac "Unable to solve goal" *)
    end || fail "Goal must be in form of create_noverlaps l -> create_noverlaps l'".

(* Take big numbers that should really be subtractions and turn them into modsubs *)
Ltac invert tac :=
    first [(tac; fail 1) | idtac].

Ltac is_get_set_mem x :=
    lazymatch x with
    | getmem _ _ _ _ _ => idtac
    | setmem _ _ _ _ _ _ => idtac
    | _ => fail 0
    end.

Ltac is_large_const x :=
  invert ltac:(is_var x);
  lazymatch x with
    | getmem _ _ _ _ _ => fail
    | setmem _ _ _ _ _ _ => fail
    | _ => idtac
  end;
  match eval cbv in x with
  | ?n =>
    let n' := eval compute in (n <? 2^31)%N in
    match n' with
    | true => fail 1 "Not large enough"
    | false => idtac
    end
  end. 

Ltac fold_big_subs :=
    repeat match goal with
    (* Goal *)
    | [ |- context[setmem ?BW ?END 4 ?M (?X + ?B + ?N) ?V] ] =>
        rewrite <-(setmem_mod_l _ _ _ M (X+B+N) V);
        replace (setmem BW END 4 M ((X+B+N) mod 2^BW) V) with
            (setmem BW END 4 M ((msub BW B (2^32 - X)) + N mod 2^BW) V) by
            (unfold msub; now psimpl);
        simpl (2^BW - X)
    | [ |- context[setmem ?BW ?END 4 ?M (?X + ?Y) ?V] ] =>
        first [is_large_const X | is_large_const Y];
        rewrite <- setmem_mod_l with (a := X + Y);
        replace ((X + Y) mod 2^BW) with (msub BW Y (2^32 - X)) by 
            (now rewrite N.add_comm);
        simpl (2^BW - X)
    | [ |- context[getmem ?BW ?END 4 ?M (?X + ?B + ?N)] ] =>
        rewrite <-(getmem_mod_l _ _ _ M (X+B+N));
        replace (getmem BW END 4 M ((X + B + N) mod 2^BW)) with
            (getmem BW END 4 M ((msub BW B (2^BW - X)) + N mod 2^BW)) by
            (now rewrite N.add_comm);
        simpl (2^BW - X)
    | [ |- context[getmem ?BW ?END 4 ?M (?X + ?Y)] ] =>
        first [is_large_const X | is_large_const Y];
        rewrite <- getmem_mod_l with (a := X + Y);
        replace ((X + Y) mod 2^BW) with (msub BW Y (2^BW - X)) by 
            (now rewrite N.add_comm);
        simpl (2^BW - X)
    (* Assumptions *)
    | [ H: context[setmem ?BW ?END 4 ?M (?X + ?B + ?N) ?V] |- _ ] =>
        rewrite <-(setmem_mod_l _ _ _ M (X+B+N) V) in H;
        replace (setmem BW END 4 M ((X+B+N) mod 2^BW) V) with
            (setmem BW END 4 M ((msub BW B (2^32 - X)) + N mod 2^BW) V) in H by
            (unfold msub; now psimpl);
        simpl (2^BW - X) in H
    | [ H: context[setmem ?BW ?END 4 ?M (?X + ?Y) ?V] |- _ ] =>
        first [is_large_const X | is_large_const Y];
        rewrite <- setmem_mod_l with (a := X + Y) in H;
        replace ((X + Y) mod 2^BW) with (msub BW Y (2^32 - X)) in H by 
            (now rewrite N.add_comm);
        simpl (2^BW - X) in H
    | [ H: context[getmem ?BW ?END 4 ?M (?X + ?B + ?N)] |- _ ] =>
        rewrite <-(getmem_mod_l _ _ _ M (X+B+N)) in H;
        replace (getmem BW END 4 M ((X + B + N) mod 2^BW)) with
            (getmem BW END 4 M ((msub BW B (2^BW - X)) + N mod 2^BW)) in H by
            (now rewrite N.add_comm);
        simpl (2^BW - X) in H
    | [ H: context[getmem ?BW ?END 4 ?M (?X + ?Y)] |- _ ] =>
        first [is_large_const X | is_large_const Y];
        rewrite <- getmem_mod_l with (a := X + Y) in H;
        replace ((X + Y) mod 2^BW) with (msub BW Y (2^BW - X)) in H by 
            (now rewrite N.add_comm);
        simpl (2^BW - X) in H
    end.

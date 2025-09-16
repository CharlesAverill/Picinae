Require Import Picinae_core Picinae_statics Picinae_finterp
    Picinae_theory Picinae_simplifier_base Picinae_simplifier_v1_1.
Require Export List.
Require Import NArith.
Require Export Bool.
Export ListNotations.

Module Type TimingModule (il : PICINAE_IL).
    Export il.
    Export Lia.

    Parameter time_of_addr : store -> addr -> N.
    Parameter time_inf : N.
End TimingModule.

Module TimingAutomation (IL : PICINAE_IL) (THEORY : PICINAE_THEORY IL)
    (STATICS: PICINAE_STATICS IL THEORY)
    (FIL: PICINAE_FINTERP IL THEORY STATICS) (SIMPL : PICINAE_SIMPLIFIER_V1_1 IL THEORY STATICS FIL)
    (tm : TimingModule IL).

Include IL.
Include THEORY.

Import SIMPL.
Module PSB := Picinae_Simplifier_Base IL.
Import PSB.
Export IL.
Export tm.

Ltac PSimplifier ::= SIMPL.PSimplifier.

Definition cycle_count_of_trace (t : trace) : N :=
    List.fold_left N.add (List.map 
        (fun '(e, s) => match e with 
            | Addr a => time_of_addr s a
            | Raise n => time_inf
            end) t) 0.

Lemma fold_left_cons : forall {X : Type} (t : list X) (h : X) (f : X -> X -> X) (base : X) 
    (Comm : forall a b, f a b = f b a) (Assoc : forall a b c, f a (f b c) = f (f a b) c),
    List.fold_left f (h :: t) base = f h (List.fold_left f t base).
Proof.
    induction t; intros.
    - simpl. now rewrite Comm.
    - simpl in *. rewrite IHt, IHt, IHt,
        Assoc, Assoc, (Comm a h); auto.
Qed.

Lemma cycle_count_of_trace_single :
    forall (e : exit) (s : store),
    cycle_count_of_trace [(e, s)] = 
        match e with 
        | Addr a => time_of_addr s a
        | Raise n => time_inf
        end.
Proof. reflexivity. Qed.

Lemma cycle_count_of_trace_cons :
    forall (t : trace) (e : exit) (s : store),
    cycle_count_of_trace ((e, s) :: t) = cycle_count_of_trace [(e, s)] + cycle_count_of_trace t.
Proof.
    intros. unfold cycle_count_of_trace at 2. rewrite map_cons, fold_left_cons; try lia. simpl.
    unfold cycle_count_of_trace at 1. rewrite map_cons, fold_left_cons. rewrite N.add_0_r. reflexivity.
    lia. lia.
Qed.

Lemma cycle_count_of_trace_app :
    forall (t1 t2 : trace) (e : exit) (s : store),
    cycle_count_of_trace (t1 ++ t2) = cycle_count_of_trace t1 + cycle_count_of_trace t2.
Proof.
    intros; induction t1; simpl.
        reflexivity.
    destruct a.
    rewrite cycle_count_of_trace_cons,
        (cycle_count_of_trace_cons t1 e0 s0), IHt1.
    lia.
Qed.

Ltac find_rewrites :=
    repeat (match goal with
    | [s: store, H: ?s ?x = ?y |- context[?s ?x]] =>
        rewrite H
    | [H: ?x = _ |- context[match ?x with _ => _ end]] =>
        rewrite H
    | [H: negb ?x = ?y |- context[if ?x then _ else _]] =>
        (match y with 
        | true => apply Bool.negb_true_iff in H 
        | false => apply Bool.negb_false_iff in H
        end);
        rewrite H
    | [H: ?x = ?y |- context[if negb ?x then _ else _]] =>
        (match y with
        | true => apply Bool.negb_false_iff in H
        | false => apply Bool.negb_true_iff in H
        end);
        rewrite H
    | [H: cycle_count_of_trace ?t = _ |- context[cycle_count_of_trace ?t]] =>
        rewrite H
    end); cbn [negb].

(* Grabbing each cpi_at_addr one-by-one seems to prevent explosions in cbv 
   evaluation time *)
Ltac unfold_time_of_addr :=
    cbv [time_of_addr]; cbn - [setmem getmem].
Ltac unfold_cycle_count_list :=
    repeat rewrite cycle_count_of_trace_app;
    repeat rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single.
Ltac hammer :=
    (* easy rewrites *)
    find_rewrites;
    (* unfolding timing definitions *)
    unfold_cycle_count_list; unfold_time_of_addr;
    (* simplify, harder rewrites, solve *)
    psimpl; find_rewrites; try lia.

Ltac handle_ex := 
    repeat (match goal with
    | [|- exists _, _] => eexists
    end); repeat (split; [solve [eauto]|]).

Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

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
            P /\ ~ overlap 32 addr size addr' size'
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

End TimingAutomation.

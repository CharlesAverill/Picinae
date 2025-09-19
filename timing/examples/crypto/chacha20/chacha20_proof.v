Require Import ChaCha20.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : CPUTimingBehavior).

Module Program_ChaCha20 <: ProgramInformation.
    Definition entry_addr : N := 0x224.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0xcc0 => true
        | _ => false
    end | _ => false end.

    Definition binary := ChaCha20.
End Program_ChaCha20.

Module RISCVTiming := RISCVTiming cpu Program_ChaCha20.
Module ChaCha20Auto := RISCVTimingAutomation RISCVTiming.
Import Program_ChaCha20 ChaCha20Auto.

Definition time_of_chacha20_quarter : N :=
  tadd + txor + tslli 0x10 +
  tadd + txor + tslli 0xc +
  tadd + txor + tslli 0x8 +
  tadd + txor + tsw + tslli 0x7 +
  tsw + tsw + tjalr.

Definition time_of_chacha20_block (t : trace) : Prop :=
  cycle_count_of_trace t = taddi + 13 * tsw + 4 * taddi +
      4 * (tsw + tlui + taddi) + 
      8 * (tsw + taddi + 4 * tlbu + 4 * tsb + tlw) +
      tsw + 4 * tlbu + 4 * tsb + tlw + 
      2 * (taddi + 4 * tlbu + 4 * tsb + tlw) +
      4 * taddi + 10 * tsw + taddi + tsw + tsw +
      10 * (4 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        5 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        tsw + 6 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        8 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        4 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        5 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter +
        4 * taddi + 4 * tlw + tjal +
        time_of_chacha20_quarter +
        5 * taddi + 3 * tlw + tjal +
        time_of_chacha20_quarter + 
        taddi + taddi) + 9 * ttbne + tfbne +
    172 * tsb + 108 * tlbu + 65 * tlw +
    16 * (tsrli 0x8 + tsrli 0x10 + tsrli 0x18) +
    16 * tadd + 16 * txor + 7 * taddi + 
    4 * tlui + tjalr.

Definition ChaCha20_timing_invs (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x224 => Some (cycle_count_of_trace t' = 0)
| 0x4b8 => Some (1 <= s R_S3 <= 10 /\
    cycle_count_of_trace t' = taddi + 13 * tsw + 4 * taddi +
        4 * (tsw + tlui + taddi) + 
        8 * (tsw + taddi + 4 * tlbu + 4 * tsb + tlw) +
        tsw + 4 * tlbu + 4 * tsb + tlw + 
        2 * (taddi + 4 * tlbu + 4 * tsb + tlw) +
        4 * taddi + 10 * tsw + taddi + tsw + tsw +
        (10 - s R_S3) * (4 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          5 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          tsw + 6 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          8 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          4 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          5 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter +
          4 * taddi + 4 * tlw + tjal +
          time_of_chacha20_quarter +
          5 * taddi + 3 * tlw + tjal +
          time_of_chacha20_quarter + 
          taddi + taddi + ttbne)
  )
| 0xcc0 => Some (time_of_chacha20_block t)
| _ => None end | _ => None end.

Local Ltac step := tstep r5_step.
(* "Forget" step - throw away the store after each step
    This is convenient for many segments of ChaCha in which functional
    semantics do not affect timing or control flow at all
*)
Local Ltac fstep := step; 
    match goal with
    | [old_s : store |- context[(Addr _, update ?old_s _ _) :: _]] =>
        let trash := fresh "s''" in
        rename old_s into trash;
        match goal with [|- context[update trash ?k ?v]] =>
          set (old_s := update trash k v)
        end;
        try match goal with [ACC: MemAcc _ _ _ _ _ |-_] =>
          clear ACC
        end;
        clearbody old_s;
        try clear trash
    end.

Notation "f '[U' x := y ]" := (update f x y) (at level 50, left associativity, format "f '/'  [U  x  :=  y ]").

(* fstep except keep one variable in the store *)
Local Ltac fstep_keep val := step; 
    lazymatch goal with
    | [old_s:store |- context[(Addr _, update (update ?old_s val _) R_RA _) :: _]] =>
        idtac (* don't want to get rid of RA *)
    | [old_s:store |- context[(Addr _, update (update ?old_s val _) _ _) :: _]] =>
        rewrite update_swap by discriminate;
        let trash := fresh "s''" in
        rename old_s into trash;
        match goal with [|- context[update trash ?k ?v]] =>
          set (old_s := update trash k v)
        end;
        try match goal with [ACC: MemAcc _ _ _ _ _ |-_] =>
          clear ACC
        end;
        clearbody old_s;
        try clear trash
    | [|- context[(Addr _, update _ val _) :: _]] => idtac
    | [old_s : store |- context[(Addr _, update ?old_s _ _) :: _]] =>
        let trash := fresh "s''" in
        rename old_s into trash;
        match goal with [|- context[update trash ?k ?v]] =>
          set (old_s := update trash k v)
        end;
        try match goal with [ACC: MemAcc _ _ _ _ _ |-_] =>
          clear ACC
        end;
        clearbody old_s;
        try clear trash
    end.

Ltac clear_unused :=
  repeat match goal with
  | H : N |- _ =>
    tryif (clear dependent H) then idtac else fail
  | H : memory |- _ =>
    tryif (clear dependent H) then idtac else fail
  end.

Ltac generalize_reg :=
  repeat multimatch goal with
  | [|- context[_ [U ?r := ?f ?x]]] =>
    match r with
    | R_S3 => idtac | R_RA => idtac
    | _ => generalize (f x); intros
    end
  | _ => idtac
  end;
  clear_unused.

Ltac gstep := step; generalize_reg.

Theorem ChaCha20_timing:
  forall s (t : trace) s' x'
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s),
  satisfies_all 
    lifted_prog
    (ChaCha20_timing_invs)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    simpl. rewrite ENTRY. unfold entry_addr. step. reflexivity.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.
    - (* 0x224 -> 4b8 *)
      repeat gstep. 
      split.
        lia.
        hammer.
    - (* 0x4b8 -> 0x5ec *)
      destruct PRE as (S3 & Cycles).
        do 206 gstep.
          replace (s' R_S3 ⊖ 1) with (s' R_S3 - 1) in * by
            (rewrite msub_nowrap; psimpl; lia).
          apply Bool.negb_true_iff in BC.
          split.
            apply N.eqb_neq in BC. lia.
          replace (10 - (s' R_S3 - 1)) with 
            (1 + (10 - s' R_S3)) by lia.
          repeat rewrite (N.mul_add_distr_r 1).

          match goal with
          |[|-context[(10 - _) * ?x]] =>
            remember x as loop_body_time
          end.

          (* Ltac recurse_add x :=
            match x with
            | N.add ?a ?b => recurse_add a; idtac " +" b
            | _ => idtac x
            end.
          match goal with
          | [|- context[?x + ?y]] => recurse_add (x + y)
          end. *)

          remember (10 - s' R_S3).
          hammer. psimpl.

          Ltac append l1 l2 :=
            lazymatch l1 with
            | [] => l2
            | ?x :: ?xs =>
                let tail := append xs l2 in
                constr:(x :: tail)
            end.

          Ltac flatten_plus t :=
            lazymatch t with
            | ?a + ?b =>
                let la := flatten_plus a in
                let lb := flatten_plus b in
                append la lb
            | ?x => constr:([x])
            end.


          Ltac remove_once x l :=
            lazymatch l with
            | [] => fail "no match for" x
            | x :: ?xs => xs
            | ?y :: ?ys =>
                let ys' := remove_once x ys in
                constr:(y :: ys')
            end.

          Ltac multiset_match lhs rhs :=
            lazymatch lhs with
            | [] => 
              match rhs with
              | [] => idtac
              | ?rhs' => 
                idtac "Extras:" rhs' (* leftover RHS terms = extras *)
              end
            | ?x :: ?xs =>
                tryif (let rhs' := remove_once x rhs in
                      multiset_match xs rhs')
                then idtac
                else (
                  idtac "could not find match for" x)
            | _ => idtac lhs
            end.

          Ltac compare_sums :=
            match goal with
            | [|- ?lhs = ?rhs] =>
                let L := flatten_plus lhs in
                let R := flatten_plus rhs in
                (* idtac L;
                idtac R; *)
                multiset_match L R
                (* tryif (multiset_match L R; idtac)
                then idtac "all terms matched"
                else fail "mismatch between" L "and" R *)
            end.

          compare_sums.

          Ltac count_occurrences x t :=
  lazymatch t with
  | x => constr:(1)                                (* exact match *)
  | ?f ?a =>
      let n1 := count_occurrences x f in
      let n2 := count_occurrences x a in
      let n := eval compute in (n1 + n2) in
      constr:(n)
  | ?a + ?b =>
      let n1 := count_occurrences x a in
      let n2 := count_occurrences x b in
      let n := eval compute in (n1 + n2) in
      constr:(n)
  | _ => constr:(0)
  end.

  Ltac count_in_goal x :=
  match goal with
  | |- ?g =>
      let n := count_occurrences x g in
      idtac x "appears" n "time(s) in the goal"
  end.

  (* count_in_goal ttbne. *)
  subst n6 loop_body_time.
  unfold time_of_chacha20_quarter.
  (* count_in_goal ttbne. *)
  (* compare_sums. *)
  (* count_in_goal tlw. *)
  hammer.

  (* postcondition *)
  repeat gstep.

  unfold time_of_chacha20_quarter.
  hammer.
  unfold time_of_chacha20_quarter.
  apply Bool.negb_false_iff in BC.
  apply N.eqb_eq in BC.
  rewrite msub_nowrap in BC.
  psimpl in BC.
  replace (s' R_S3) with 1 in * by lia.
  hammer.
  psimpl. lia.
Qed.

End TimingProof.

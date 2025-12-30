Require Import Picinae_core Picinae_statics Picinae_theory.
Require Import NArith.

Module Type FaultToleranceConfig (Arch : Architecture)
                                 (IL : PICINAE_IL).
    Import IL.

    Parameter w : N.
    Parameter w_nontrivial : 1 < 2^w.

    Parameter fault_counter : var.
    Parameter fault_counter_typed :
        archtyps fault_counter = Some w.

    Parameter mem : var.
    Parameter mem_typed :
        archtyps mem = Some (8 * 2^w).
End FaultToleranceConfig.

Module FaultTolerance (Arch : Architecture)
                      (IL : PICINAE_IL)
                      (FTC : FaultToleranceConfig Arch IL)
                      (TIL : PICINAE_THEORY IL)
                      (SIL : PICINAE_STATICS IL TIL).
Import Arch IL FTC TIL SIL.

Definition inject_skip (p : program) (s : store) (a : addr) :=
  match p s a with
  | None => None
  | Some (sz,q) =>
        Some (sz,
              If (BinOp OP_AND (BinOp OP_LT (Word 0x0 w) (Var fault_counter)) (Unknown 1))
                (Move fault_counter (BinOp OP_MINUS (Var fault_counter) (Word 0x1 w)))
              q)
  end.

(* Only useful for architectures with a Gallina-defined lifter
   accompanied by a well-typedness theorem, eg welltyped_rv2il *)
Lemma inject_skip_welltyped : forall p,
    (forall s a sz instr,
        p s a = Some (sz, instr) ->
        hastyp_stmt archtyps archtyps instr archtyps) ->
    welltyped_prog archtyps (inject_skip p).
Proof.
    intros p WT s a. unfold inject_skip.
    destruct (p s a) eqn:E; [|exact I]. destruct p0 as (sz & instr).
    pose proof fault_counter_typed. pose proof mem_typed.
    pose proof w_nontrivial.
    exists archtyps.
    econstructor.
    change 1 with (widthof_binop OP_AND 1). constructor.
        change 1 with (widthof_binop OP_LT w). constructor.
        constructor. apply mp2_gt_0. constructor. assumption.
        constructor.
    econstructor. right. eassumption.
        change w with (widthof_binop OP_MINUS w) at 2. constructor.
        now constructor.
        now constructor. 
        eapply typchk_stmt_mono with (c := archtyps) (c0 := archtyps)
            (q := Move fault_counter (BinOp OP_MINUS (Var fault_counter) (Word 1 w))).
            simpl. rewrite H. replace (1 <? 2^w) with true. rewrite N.eqb_refl.
            pose proof (iseq_refl w). destruct H2.
                now replace (w == w) with (@left (w=w) (w<>w) x).
            symmetry. now apply N.ltb_lt.
        reflexivity.
    eapply WT, E.
    reflexivity.
Qed.

Definition inject_memory_corruption (p : program) (s : store) (a : addr) :=
  match p s a with
  | None => None
  | Some (sz,q) =>
        match archtyps fault_counter with None => None | Some w =>
        Some (sz,
              If (BinOp OP_AND (BinOp OP_LT (Word 0x0 w) (Var fault_counter)) (Unknown 1))
                (Seq (Move fault_counter (BinOp OP_MINUS (Var fault_counter) (Word 0x1 w)))
                 (Seq q (
                    (Move mem (Unknown (8 * 2^w)))
                 )))
              q)
        end
  end.

(* Only useful for architectures with a Gallina-defined lifter
   accompanied by a well-typedness theorem, eg welltyped_rv2il *)
Lemma inject_memory_corruption_welltyped : forall p,
    (forall s a sz instr,
        p s a = Some (sz, instr) ->
        hastyp_stmt archtyps archtyps instr archtyps) ->
    welltyped_prog archtyps (inject_memory_corruption p).
Proof.
    intros p WT s a. unfold inject_memory_corruption.
    destruct (p s a) eqn:E; [|exact I]. destruct p0 as (sz & instr).
    pose proof fault_counter_typed. pose proof mem_typed.
    pose proof w_nontrivial.
    rewrite H. exists archtyps.
    econstructor.
    change 1 with (widthof_binop OP_AND 1). constructor.
        change 1 with (widthof_binop OP_LT w). constructor.
        constructor. apply mp2_gt_0. constructor. assumption.
        constructor.
    econstructor. econstructor. right. eassumption.
        change w with (widthof_binop OP_MINUS w) at 2. constructor.
        now constructor.
        now constructor.
        eapply typchk_stmt_mono with (c := archtyps) (c0 := archtyps)
            (q := Move fault_counter (BinOp OP_MINUS (Var fault_counter) (Word 1 w))).
            simpl. rewrite H. replace (1 <? 2^w) with true. rewrite N.eqb_refl.
            pose proof (iseq_refl w). destruct H2.
                now replace (w == w) with (@left (w=w) (w<>w) x).
            symmetry. now apply N.ltb_lt.
        reflexivity.
    econstructor.
        eapply WT, E. econstructor.
        right. eassumption.
        constructor.
        eapply typchk_stmt_mono with (c := archtyps) (c0 := archtyps)
            (q := Move mem (Unknown (8 * 2^w))).
            unfold typchk_stmt, typchk_exp. rewrite H0.
            pose proof (iseq_refl (8*2^w)). destruct H2.
                now replace ((8*2^w) == (8*2^w)) with
                    (@left ((8*2^w)=(8*2^w)) ((8*2^w)<>(8*2^w)) x).
                reflexivity. reflexivity. reflexivity.
    eapply WT, E.
    reflexivity.
Qed.

End FaultTolerance.

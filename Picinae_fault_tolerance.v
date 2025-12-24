Require Import Picinae_core Picinae_statics Picinae_theory.
Require Import NArith.

Module Type FaultToleranceConfig (Arch : Architecture)
                                 (IL : PICINAE_IL).
    Import IL.
    Parameter fault_counter : var.
    Parameter fault_counter_typed :
        exists w,
            1 < 2^w /\
            archtyps fault_counter = Some w.
End FaultToleranceConfig.

Module FaultTolerance (Arch : Architecture)
                      (IL : PICINAE_IL)
                      (FTC : FaultToleranceConfig Arch IL)
                      (TIL : PICINAE_THEORY IL)
                      (SIL : PICINAE_STATICS IL TIL).
Import Arch IL FTC TIL SIL.

Definition inject_fault (p : program) (s : store) (a : addr) :=
  match p s a with
  | None => None
  | Some (sz,q) =>
        match archtyps fault_counter with None => None | Some w =>
        Some (sz,
              If (BinOp OP_AND (BinOp OP_LT (Word 0x0 w) (Var fault_counter)) (Unknown 1))
                (Move fault_counter (BinOp OP_MINUS (Var fault_counter) (Word 0x1 w)))
              q)
        end
  end.

Lemma inject_fault_welltyped : forall p,
    (forall s a sz instr,
        p s a = Some (sz, instr) ->
        hastyp_stmt archtyps archtyps instr archtyps) ->
    welltyped_prog archtyps (inject_fault p).
Proof.
    intros p WT s a. unfold inject_fault.
    destruct (p s a) eqn:E; [|exact I]. destruct p0 as (sz & instr).
    destruct fault_counter_typed as (w & BigW & FCW). rewrite FCW.
    exists archtyps.
    econstructor.
    change 1 with (widthof_binop OP_AND 1). constructor.
        change 1 with (widthof_binop OP_LT w). constructor.
        constructor. apply mp2_gt_0. constructor. assumption.
        constructor.
    econstructor. right. eassumption.
        change w with (widthof_binop OP_MINUS w) at 2. constructor.
        now constructor.
        constructor. assumption.
        eapply typchk_stmt_mono with (c := archtyps) (c0 := archtyps)
            (q := Move fault_counter (BinOp OP_MINUS (Var fault_counter) (Word 1 w))).
            simpl. rewrite FCW. replace (1 <? 2^w) with true. rewrite N.eqb_refl.
            pose proof (iseq_refl w). destruct H.
                now replace (w == w) with (@left (w=w) (w<>w) x).
            symmetry. now apply N.ltb_lt.
        reflexivity.
    eapply WT, E.
    reflexivity.
Qed.

End FaultTolerance.

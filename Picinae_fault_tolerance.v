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

    Parameter fault_timer : var.
    Parameter fault_timer_typed :
        archtyps fault_timer = Some w.

    Parameter mem : var.
    Parameter mem_typed :
        archtyps mem = Some (8 * 2^w).
End FaultToleranceConfig.

Module Type FaultModel (Arch : Architecture)
                       (IL : PICINAE_IL)
                       (FTC: FaultToleranceConfig Arch IL).
    Import Arch IL FTC.

    Parameter fault_spacing : N.
    Parameter fault_spacing_small :
        fault_spacing < 2^w.

    Parameter max_faults : N.
End FaultModel.

Module FaultTolerance (Arch : Architecture)
                      (IL : PICINAE_IL)
                      (TIL : PICINAE_THEORY IL)
                      (SIL : PICINAE_STATICS IL TIL)
                      (FTIC : FaultToleranceConfig Arch IL)
                      (FM : FaultModel Arch IL FTIC).
Import Arch IL FTIC FM TIL SIL.

Notation "s1 $; s2" := (Seq s1 s2) (at level 75, right associativity).
Notation "o1 $& o2" := (BinOp OP_AND o1 o2) (at level 75, right associativity).
Definition inject_skip (p : program) (s : store) (a : addr) :=
  match p s a with
  | None => None
  | Some (sz,q) =>
        Some (sz,
              (If (
                (BinOp OP_LE (Word fault_spacing w) (Var fault_timer)) $&
                   (BinOp OP_LT (Word 0x0 w) (Var fault_counter)) $&
                   (Unknown 1))
                (Move fault_counter (BinOp OP_MINUS (Var fault_counter) (Word 0x1 w))
                 $; Move fault_timer (Word 0x0 w)
                 )
                (Move fault_timer (BinOp OP_PLUS (Var fault_timer) (Word 0x1 w)) $;
                 q)
                )
        )
  end.

Lemma pfsub_update_same : forall (s : typctx) k w,
    s k = Some w ->
    s ⊆ s[k := Some w].
Proof.
    intros.
    eapply typchk_stmt_mono with (c := s) (c0 := s)
        (q := Move k (Var k));
        [|reflexivity].
    simpl. rewrite H.
    pose proof (iseq_refl w0). destruct H0.
    now replace (w0 == w0) with (@left (w0=w0) (w0<>w0) x).
Qed.

(* Only useful for architectures with a Gallina-defined lifter
   accompanied by a well-typedness theorem, eg welltyped_rv2il *)
Lemma inject_skip_welltyped : forall p,
    (forall s a sz instr,
        p s a = Some (sz, instr) ->
        hastyp_stmt archtyps archtyps instr archtyps) ->
    welltyped_prog archtyps (inject_skip p).
Proof.
Admitted.
    (* intros p WT s a. unfold inject_skip.
    destruct (p s a) eqn:E; [|exact I]. destruct p0 as (sz & instr).
    pose proof fault_counter_typed. pose proof mem_typed.
    pose proof fault_timer_typed. pose proof fault_spacing_small.
    pose proof w_nontrivial.
    exists archtyps.
    econstructor. econstructor.
    change 1 with (widthof_binop OP_AND 1). constructor.
        change 1 with (widthof_binop OP_LE w). econstructor.
        now constructor. now constructor.
    change 1 with (widthof_binop OP_AND 1). econstructor.
        change 1 with (widthof_binop OP_LT w). econstructor.
        constructor. apply mp2_gt_0. now constructor.
    constructor.
    econstructor. econstructor. right. eassumption.
        change w with (widthof_binop OP_MINUS w) at 2. constructor.
        now constructor.
        now constructor.
        now apply pfsub_update_same.
    econstructor. right. eassumption. constructor. apply mp2_gt_0.
    now apply pfsub_update_same.
    reflexivity.
    eapply WT, E.
    reflexivity.
    econstructor. right. eassumption.
    change w with (widthof_binop OP_PLUS w).
        econstructor. now constructor.
        now constructor.
    now apply pfsub_update_same.
    reflexivity.
Qed. *)

Definition fault_assumptions (s : store) : Prop :=
    s fault_counter = max_faults /\
    s fault_timer = 0.

Definition fault_invs (s : store) : Prop :=
    s fault_counter <= max_faults.

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

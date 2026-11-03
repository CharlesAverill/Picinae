(* Example-local total-execution support for the i386 string routines.
   Keep intermediate witness values shared and infer Load/Store widths from
   their addresses first.  The core API remains unchanged. *)
From Stdlib Require Import Utf8 NArith List.
Require Export Picinae_i386.
Open Scope N.

Lemma i386_eventually_context:
  forall p xp entry t,
    eventually p (fun t' => xp t' = true) t ->
    execution_context p xp entry t ->
    eventually p (fun t' => xp t' = true /\ execution_context p xp entry t') t.
Proof.
  intros p xp entry t EV. induction EV; intros CTX.
  - apply EventuallyHere. split; assumption.
  - destruct (xp (xs::t)) eqn:EX.
    + apply EventuallyHere. split; assumption.
    + destruct CTX as [XP [ORIGIN UT]].
      eapply EventuallyStep. exact ENABLED.
      intros xs' CS. apply H; [exact CS|].
      split. apply exec_prog_step; assumption.
      split. rewrite ostartof_step. exact ORIGIN.
      apply unterminated_cons; assumption.
Qed.

(* Resolve the address width before the memory width.  x86 writes the
   latter as 8*2^32, whereas ELoad/EStore use 2^w*8. *)
Ltac total_eval ::= first [apply EVar; reflexivity | apply EWord |
  lazymatch goal with |- eval_exp _ _ (BinOp ?op _ _) _ _ =>
    eapply EBinOp with (bop:=op); total_eval end |
  eapply EUnOp; total_eval | eapply ECast; total_eval |
  eapply EExtract; total_eval | eapply EConcat; total_eval |
  eapply ELet; [total_eval | total_eval] |
  eapply EIte; [total_eval | total_eval | total_eval] |
  eapply ELoad; [idtac | total_eval | total_memory]; total_eval |
  eapply EStore; [idtac | total_eval | total_eval | total_memory]; total_eval |
  eapply EUnknown with (n:=0); apply N.neq_0_lt_0, pow2_nonzero].

Ltac total_exec c s q k ::=
  let q' := eval hnf in q in
  lazymatch q' with
  | Nop => k c s constr:(@None exit) constr:(XNop c s)
  | Exn ?i => k c s constr:(Some (Raise i)) constr:(XExn c s i)
  | Move ?v ?e =>
    let E := constr:(ltac:(total_eval) : eval_exp c s e _ _) in
    let EE := fresh "EE" in pose proof E as EE;
    lazymatch type of EE with eval_exp _ _ _ ?n ?w =>
      let nv := fresh "nv" in pose (nv:=n);
      let cv := fresh "cv" in pose (cv:=update c v (Some w));
      let sv := fresh "sv" in pose (sv:=update s v nv);
      k cv sv constr:(@None exit) constr:(XMove c s v e nv w EE) end
  | Jmp ?e =>
    let E := constr:(ltac:(total_eval) : eval_exp c s e _ _) in
    lazymatch type of E with eval_exp _ _ _ ?n ?w =>
      k c s constr:(Some (Addr n)) constr:(XJmp c s e n w E) end
  | Seq ?q1 ?q2 =>
    total_exec c s q1 ltac:(fun c2 s2 x2 XS1 =>
      lazymatch x2 with
      | None => total_exec c2 s2 q2 ltac:(fun c3 s3 x3 XS2 =>
          k c3 s3 x3 constr:(XSeq2 c s q1 q2 c2 s2 c3 s3 x3 XS1 XS2))
      | Some ?x => k c2 s2 x2 constr:(XSeq1 c s q1 q2 c2 s2 x XS1)
      end)
  | If ?e ?q1 ?q2 =>
    let EE := constr:(ltac:(total_eval) : eval_exp c s e _ 1) in
    let E := fresh "E" in pose proof EE as E;
    lazymatch type of E with eval_exp _ _ _ ?n _ =>
      let BC := fresh "BC" in destruct n eqn:BC;
      [ total_exec c s q2 ltac:(fun c' s' x XS =>
          k c' s' x constr:(XIf c s e q1 q2 0 c' s' x E XS))
      | match type of E with eval_exp _ _ _ ?b _ =>
          total_exec c s q1 ltac:(fun c' s' x XS =>
            k c' s' x constr:(XIf c s e q1 q2 b c' s' x E XS)) end ] end
  end.

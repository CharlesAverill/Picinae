(* GrokStep: stepping helpers (Grok Bot / coqettu).

   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)

From Stdlib Require Import Utf8 NArith.
Require Import Picinae_armv8.
Import ARM8Notations.
Open Scope N.

(* arm8_step variant that also splits an `if` nested deeper inside the
   statement sequence of one instruction (e.g. ccmp, lifted with an internal
   conditional jump), which ISA_symbolic_interp leaves unevaluated. *)
Ltac grok_symbolic_interp :=
  let c := fresh "c" in let s := fresh "s" in let x := fresh "x" in let XS := fresh "XS" in
  intros c s x XS;
  ISA_step_and_simplify XS;
  repeat lazymatch type of XS with
         | reset_temps _ s = _ /\ x = _ =>
             try clear c; destruct XS as [XS ?]; subst x;
             try (let rt := fresh in set (rt := reset_temps _ _) at 1;
                  psimpl_hyp rt; subst rt;
                  rewrite XS; clear XS; try clear s)
         | exec_stmt _ _ (if ?c then _ else _) _ _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ISA_step_and_simplify XS
         | exec_stmt _ _ (Seq (if ?c then _ else _) _) _ _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ISA_step_and_simplify XS
         | exec_stmt _ _ (Seq (Seq (if ?c then _ else _) _) _) _ _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ISA_step_and_simplify XS
         | exec_stmt _ _ (N.iter _ _ _) _ _ _ => fail
         | _ => ISA_step_and_simplify XS
         end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  repeat match goal with [ x:N |- _ ] => clear x end;
  try first [ rewrite exitof_none | rewrite exitof_some ].
Ltac grok_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ eapply NIStep; [reflexivity|reflexivity|]; grok_symbolic_interp; try ISA_invhere | ISA_invhere ].

Ltac splits := repeat match goal with |- _ /\ _ => split end.


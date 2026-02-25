Require Import Picinae_theory.
Require Import arm7_collatz_smc.
Require Import Picinae_armv7.
Require Import -(notations) Picinae_armv7_lifter.
Require Import NArith.
Require Import Lia ZifyN ZifyBool.
Require Import Picinae_numbers.
Open Scope N.

Import ARM7Notations.

Definition collatz_start : N :=  0x100.
Definition collatz_end   : N :=  0x100 + 4 * 7.

Section Invariants.
  Variable  base: addr.
  Variable  inp : N.
  Variable  s0 : store.

  Definition postcondition (s:store) :=
    s R_R0 = if N.even inp then inp >> 1 else (1 ⊕ inp >> 1) ⊕ inp  .
  Definition mem_unchanged (s:store) := s V_MEM32 = s0 V_MEM32.
  Definition invs (t:trace) : option Prop:=
    match t with (Addr a, s) :: _ =>
    if a =? base then
      Some (mem_unchanged s /\ s R_R0 = inp /\ s R_T = 0 /\ s R_JF = 0 /\ s R_E = 0)
    else if a =? base + 0x1c then
      Some (postcondition s)
    else None
    | _ => None end.
End Invariants.

Definition collatz_exit (base:addr) (t:trace) :=
  match t with (Addr a,_)::_ => a =? base+0x1c | _ => false end.

Theorem collatz_correctness:
  forall s t s' x' inp base
         (ENTRY: startof t (x',s') = (Addr base,s))
         (MDL: models arm7typctx s)
         (RT: s R_T = 0)
         (JF: s R_JF = 0)
         (RE: s R_E = 0)
         (INP: s R_R0 = inp)
         (BASE: base < 2^32 - 32)
         (BASEM: base mod 4 = 0)
         (MEM: collatz_arm7 base s)
,
(* We define our program as p32_prog, a function that looks into
   a given store's memory and page-execute permissions to determine
   what the next instruction is.
   Above we specified that the memory of the initial store is exactly
   our program, which is held in bytes 0-12 with all other bytes 0.
*)
  satisfies_all arm_prog (invs base inp s) (collatz_exit base) ((x',s')::t).
Proof.
  Local Ltac step := time (ISA_step).
intros. apply prove_invs.
  (* Base case: *)
  simpl. rewrite ENTRY.
  step. repeat (split; try assumption).

  (* Inductive cases *)
  intros.
  (* somehow `startof_prefix` is bound to the wrong theorem here...
     In the strspn example the theorem is preferentially bound to
     Picinae.Picinae_armv8.Theory_arm8.startof_prefix
     rather than the alternative Picinae.Picinae_theory.startof_prefix.
     Here it is the opposite, so we must specify the arch-specific version*)
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try (eassumption || apply welltyped_arm_prog).
  clear MDL; intros MDL.
  clear - PRE MDL MEM BASE BASEM. rename s into s0, t1 into t, s1 into s.

  destruct (N.eq_dec a1 base); try subst a1.
  2: {
    unfold get_precondition, collatz_exit, invs in PRE.
    destruct (a1 =? base + 28). contradiction.
    rewrite <-N.eqb_neq in n; rewrite n in PRE. contradiction.
  }

  prep_precondition PRE.
  destruct PRE as (MEMSAME & INP & RT & JF & RE).
  unfold collatz_arm7 in MEM.
  rewrite <-MEMSAME in *. clear MEMSAME.
  (*
  eapply NIStep.
    effinv_none_hook. reflexivity.
    effinv_none_hook.
    unfold arm2il. rewrite (N.mod_small base) by lia. cbn -[N.add]. reflexivity.
    Print Ltac ISA_step.

(* Simplify arm memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H ::=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.


   (let c := fresh "c" in
    let s := fresh "s" in
    let x := fresh "x" in
    let XS := fresh "XS" in
    intros c s x XS; ISA_step_and_simplify XS;
     repeat
      lazymatch type of XS with
      | reset_temps _ s = _ /\ x = _ =>
          try clear c; destruct XS as [XS ?]; subst x;
           try
            (let rt := fresh in
             set (rt := reset_temps _ _)  at 1; psimpl_hyp rt; subst rt;
              rewrite XS; clear XS; try clear s)
      | exec_stmt _ _ (if ?c then _ else _) _ _ _ =>
          let BC := fresh "BC" in
          destruct c eqn:BC; ISA_step_and_simplify XS
      | exec_stmt _ _ (N.iter _ _ _) _ _ _ => fail
      | _ => ISA_step_and_simplify XS
      end;
     try
      lazymatch goal with
      | |- context [ exitof (?m + ?n) ] => simpl (m + n)
      end;
     repeat match goal with
            | x:N |- _ => clear x
            end;
     try (first [ rewrite exitof_none | rewrite exitof_some ])).
     *)

  step. (*  3.0s; old: 2.6s *)
  step. (*  2.5; old: 2.4s *)
  step. (*  3.0; old: 3.4s *)
  step. (*  4.0; old: 20 s *)
  step. (* 16.3; old: 50 s *)
  step. (* 14.7s; old: 50 s *)

  assert (inp mod 2 < 2) by lia.
  destruct (inp mod 2) as [|p] eqn:EQ; try destruct p; try lia.

  step.
  Set Printing Parentheses.
  (* The goal now is just a typical Rocq goal. It is true because inp is even,
     so we must show (1+inp)>>1 = inp>>1, which is true because the increment
     is forgotten after shifting right. *)
  rewrite mod2_0_even in EQ; rewrite EQ.
  destruct inp;[reflexivity|].
  destruct p; reflexivity || discriminate || idtac. cbn. rewrite N.mod_small;[reflexivity|].
  pose proof (models_var R_R0 MDL). cbn in H0. lia.

  step.
  rewrite mod2_1_neven in EQ; rewrite EQ. reflexivity.
Time Qed.

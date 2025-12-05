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
    s R_R0 = if N.even inp then inp >> 1 else inp ⊕ (1 ⊕ inp >> 1).
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
  step. (* 2.6s *)
  step. (* 2.4s *)
  step. (* 3.4s *)
  step. (* 20 s *)
  step. (* 50 s *)
  step. (* 50 s *)

  assert (inp mod 2 < 2) by lia.
  destruct (inp mod 2) as [|p] eqn:EQ; try destruct p; try lia.

  step. (* 7.6s *)
  assert (H0:N.even inp = true).
  rewrite <-testbit0_even, Bool.negb_true_iff, N.bit0_eqb, EQ. easy. rewrite H0.
  apply N.bits_inj; intro.
  rewrite !N.shiftr_spec; try lia.
  assert (forall w a b, a mod 2^w = 0 -> b < 2^w -> forall i, i >= w -> N.testbit a i = N.testbit (a+b) i).
  clear - s0. induction w using N.peano_ind; clear s0; intros.
    destruct b; try lia. rewrite N.add_0_r; reflexivity.
    rewrite mp2_mod_divides in H. destruct H as [m EQ].
    destruct (N.zero_or_succ i); try lia. destruct H as [i' Eq]; subst i.
    assert (H2: i' >= w) by lia; clear H1.
    Search (N.testbit _ (N.succ _)). rewrite <-!N.div2_bits.
    assert (H:(a+b)/2 = a/2 + b/2) by admit. (* maybe use mp2_div_add here *)
    rewrite H.
    apply IHw; try lia. admit. admit.
  specialize (H1 1 inp 1). psimpl in H1. assert (HELP: n+1>=1) by lia.
  specialize (H1 EQ (eq_refl _) (n+1) HELP); clear HELP.
  rewrite H1.
  admit.

  step. (* 8.7s *)
  assert (H0: N.even inp = false).
  rewrite <-testbit0_even, Bool.negb_false_iff, N.bit0_eqb, EQ. easy. rewrite H0.
  lia.
Time Qed.

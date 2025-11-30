Require Import Picinae_theory.
Require Import riscv_collatz_smc.
Require Import Picinae_riscv.
Require Import NArith.
Require Import Lia ZifyN ZifyBool.

Import RISCVNotations.

Definition collatz_start : N :=  0x100.
Definition collatz_end   : N :=  0x100 + 4 * 10.

Section Invariants.
  Variables inp : N.
  Variable  s0 : store.

  Definition postcondition (s:store) :=
    s R_A0 = if N.even inp then inp >> 1 else inp ⊕ (1 ⊕ inp >> 1).
  Definition mem_unchanged (s:store) := s0 V_MEM32 = s V_MEM32 /\ s0 A_EXEC = s A_EXEC.
  Definition invs (t:trace) : option Prop:=
    match t with (Addr a, s) :: _ => match a with
      | 0x100 => Some (mem_unchanged s /\ s R_A0 = inp)
      | 0x124 => Some (postcondition s)
      | _ => None end
    | _ => None end.
End Invariants.

Definition collatz_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x124 => true
  | _ => false
  end | _ => false end.

(* Overwrite the psa_some hook to use `cbv` rather than `cbv -[N.add]`.
   The RISCV program definition needs to reduce addition, whereasthe `-[N.add]`
   modifier was added to prevent aggressive reduction of `variable+offset`
   addresses in variably-placed ARMv7 code. *)
Ltac psa_some_hook ::=
  effinv_none_hook;
  cbv;
  match goal with |- ?G => idtac G end.

Theorem collatz_correctness:
  forall s t s' x' inp
         (ENTRY: startof t (x',s') = (Addr 0x100,s))
         (MDL: models rvtypctx s)
         (INP: s R_A0 = inp)
         (MEM: collatz_riscv s)
         (EXEC: collatz_riscv_aexec (s A_EXEC))
,
(* We define our program as rv_prog, a function that looks into
   a given store's memory and page-execute permissions to determine
   what the next instruction is.
   Above we specified that the memory of the initial store is exactly
   our program, which is held in bytes 0-12 with all other bytes 0.
*)
  satisfies_all rv_prog (invs inp s) collatz_exit ((x',s')::t).
Proof.
Local Ltac step := time ISA_step.
intros. unfold satisfies_all.
  apply prove_invs.
  (* Base case: *)
  simpl. rewrite ENTRY.
  step. repeat (split; try assumption).

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try (eassumption || apply welltyped_rvprog).
  clear MDL; intros MDL.
  clear - PRE MDL MEM EXEC. rename s into s0, t1 into t, s1 into s.

  destruct_inv 32 PRE.
  destruct PRE as ((MEMSAME & EXECSAME) & INP).
  unfold collatz_riscv, collatz_riscv_aexec in *; rewrite MEMSAME, EXECSAME in *.
  clear MEMSAME EXECSAME.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.

  assert (inp mod 2 < 2) by lia.
  destruct (inp mod 2) as [|p] eqn:EQ; try destruct p; try lia.

  step.
  admit.

  step.
  admit.
Admitted.

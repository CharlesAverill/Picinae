Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Picinae_armv8_pcode.
Require Import nops_o_branch_nop_armv8.
Require Import nops_o_call_test_armv8.
Require Import nops_o_clobber_ret_armv8.
Require Import nops_o_faith_ret_armv8.
Require Import nops_o_loop_nop_armv8.
Require Import nops_o_rec_nop_armv8.
Require Import nops_o_short_nop_armv8.
Require Import nops_o_tail_nop_armv8.
Require Import nops_o_tiny_nop_armv8.


Import ARM8Notations.
Open Scope N.

Definition funcs := [branch_nop;
call_test;
clobber_ret;
faith_ret;
loop_nop;
rec_nop;
short_nop;
tail_nop;
tiny_nop].


(* I'd like to use Picinae_theory.updateall to combine the programs,
   but update all is expecting functions like 'A -> option B' whereas
   programs are 'store -> addr -> option B'. 
   Not sure what the cleanest way to do this is. *)
Definition unstored_funcs := funcs.

Definition call_test_combined :=
  List.fold_left (updateall) funcs (fun _ => None).
Definition call_test_exit (t:trace) :=
  match t with (Addr a, _)::_ => match a with
  | 0x001000cc => true
  | _ => false end | _ => false end.
  
Definition call_test_invs (s0:store) (t:trace) :=
  match t with (Addr a, s)::_ => match a with
  | 0x00100084 => Some (arm8equiv s s0)
  | 0x001000cc => Some (arm8equiv_or s s0 (fun v => match v with | R_X0 | R_X30 => true | _ => false end))
  | _ => None end | _ => None end.
  
Theorem call_test_pc :
  forall s t x' s'
     (ENTRY: startof t (x',s') = (Addr 0x00100084,s))
     (MDL: models arm8typctx s),
     satisfies_all call_test (call_test_invs s) call_test_exit ((x',s')::t).
Proof.
  Local Ltac step := time arm8_step.
  intros. 
  (* Base case *)
  apply prove_invs. simpl. rewrite ENTRY. step. 
  unfold arm8equiv_or; intros. unfold arm8equiv; reflexivity.
  (* Inductive step *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply calltest_welltyped).
  clear - PRE MDL. rename t1 into t. rename s into s0; rename s1 into s.
  destruct_inv 64 PRE.
  rename PRE into S0.
  step. step. step.
  repeat step.
  
  repeat step; unfold arm8equiv in *; intros v SIG; specialize (S0 v SIG).
    destruct v; match goal with
    | [ |- context[or (eq true true) _] ] => now left
    | _ => repeat (rewrite update_updated || rewrite update_frame); try easy
    end.
    now rewrite <-S0.
Qed.
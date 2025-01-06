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
Require Import branch_nop_proofs.
Require Import clobber_ret_proofs.
Require Import faith_ret_proofs.
Require Import loop_nop_proofs.
Require Import short_nop_proofs.
Require Import tail_nop_proofs.
Require Import tiny_nop_proofs.



Import ARM8Notations.
Open Scope N.

Definition funcs := [
    tiny_nop;
    short_nop;
    branch_nop;
    loop_nop;
    rec_nop;
    tail_nop;
    clobber_ret;
    faith_ret;
    call_test
    ].

Fixpoint combine_programs (ps: list program) s a : option (N*stmt) :=
 match ps with
 | nil => None
 | p::ps => match p s a with
            | Some x => Some x
            | None => combine_programs ps s a
            end
  end.

Definition whole_binary := combine_programs funcs.
Theorem whole_binary_welltyped: welltyped_prog arm8typctx whole_binary. Proof. Picinae_typecheck. Qed.

Theorem funcs_pfsub:
  forall s f (F: In f funcs), f s ⊆ whole_binary s.
Proof.
  intro s. rewrite <-Forall_forall.
  (* Trouble automating this part - `intros x y` yields "No product even after head reduction." *)
  (*
  apply Forall_cons;
    unfold tiny_nop, whole_binary, combine_programs, funcs, pfsub;
    unfold tiny_nop, short_nop, branch_nop, loop_nop, rec_nop, tail_nop, clobber_ret, faith_ret, call_test;
    intros x y; destruct x;[discriminate|repeat (discriminate || assumption || destruct p as [p|p|])].
  *)
  Ltac unfold_all :=
    unfold whole_binary, combine_programs, funcs, pfsub,
           tiny_nop, short_nop, branch_nop, loop_nop, 
           rec_nop, tail_nop, clobber_ret, faith_ret, call_test.
  Ltac prove_pfsub x :=
    destruct x as [|p]; [
        discriminate
      | repeat (discriminate || assumption || destruct p as [p|p|])].
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_cons; unfold_all. intros x y a. prove_pfsub x.
  apply Forall_nil. 

Qed.

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
     satisfies_all whole_binary (call_test_invs s) call_test_exit ((x',s')::t).
Proof.
  Local Ltac step := time arm8_step.
  intros. 
  (* Base case *)
  apply prove_invs. simpl. rewrite ENTRY. step. 
  unfold arm8equiv_or; intros. unfold arm8equiv; reflexivity.
  (* Inductive step *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply whole_binary_welltyped).
  clear - PRE MDL. rename t1 into t. rename s into s0; rename s1 into s.
  
  Search trueinv_None.
  destruct_inv 64 PRE.
  rename PRE into S0.
  step. step.
  (* We are at the entry of tiny_nop (0x00100000), so apply perform_call *)
  remember (update (update s R_X0 (VaN n 64)) R_X30 (VaN 1048716 64)) as current_s.

  (* TODO: update the invariants, exit, and proof to use the new perform_call
           machinery.
  *)
  
  
  (* Old code *)
  apply perform_call with (Invs2:=tiny_nop_invs current_s) (xp2:=tiny_nop_exit); try reflexivity.
    (* CALLEE *)
    intros. apply satall_pmono with (p1:=tiny_nop).
      intro s1. apply (funcs_pfsub s1 tiny_nop). apply in_eq.
      admit. (* Don't have enough to prove `exec_prog tiny_nop (xs'::t0) *)
      destruct xs' as [x' s']. apply tiny_nop_pc.
        assumption.
        admit. (* Punting on proving store's typesafety *)
    (* INVXP2 *)
    intros. unfold whole_binary, tiny_nop_exit; destruct t0 as [|[[[|p]|i] s1] t0]; try easy.
        time repeat (reflexivity || contradiction || destruct p as [p|p|]).
    (* IMP *)
    intro t'. unfold effinv_impl,effinv. rewrite Bool.orb_true_l, Bool.orb_true_l.
      unfold tiny_nop_invs, tiny_nop_exit, call_test_invs, call_test_exit.
      destruct t' as [|x_s t'];[easy|destruct x_s as [x s']]. destruct x; try easy.
      destruct a eqn:EQa; try easy. repeat (easy || destruct p as [p|p|]).
      (* Here we are asked to prove the invariants for call_test entry and exit
         without any information.
         The goal in focus is the call-test postcondition.
         We're being asked to prove that the current store, s', of an arbitrary
         trace matches our original store with some exceptions.
         This seems impossible...
       *) admit. admit.
    (* CI *)
    intros; split; reflexivity.
  (* Great! We're ready to keep going assuming all of our admits,
     ~~ including the impossible looking ones ~~
     are provable.
  *)
  intros.
  (* `destruct_inv 64 PRE` hangs... *)
  destruct_inv 64 PRE. step.
Qed.
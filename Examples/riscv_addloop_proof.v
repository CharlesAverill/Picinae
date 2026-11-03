Require Import Picinae_riscv.
Import RISCVNotations.
Require Import NArith.
Require Import List.
Require Import Lia.

Import ListNotations.
Open Scope N_scope.

(* 
    To create this function, I:
    - Wrote some assembly

        start:
            ori t2, zero, 1
            andi t3, t3, 0
        add:
            beq t0, t3, end
            addi t1, t1, 1
            sub t0, t0, t2
            beq t3, t3, add
        end:

    - Assembled it using a RISC-V cross-assembler
        https://github.com/riscv-collab/riscv-gnu-toolchain
        https://github.com/xpack-dev-tools/riscv-none-elf-gcc-xpack
      Command:
        $ riscv32-none-elf-as addloop.s -o addloop.o

    - Dumped the assembled code
      Command:
        $ riscv32-none-elf-objdump addloop.o -D
      This prints out a bunch of text:

        addloop.o:     file format elf32-littleriscv


        Disassembly of section .text:

        00000000 <start-0x8>:
        0:	00506293          	ori	t0,zero,5
        4:	00906313          	ori	t1,zero,9

        00000008 <start>:
        8:	00106393          	ori	t2,zero,1
        c:	000e7e13          	andi	t3,t3,0

        00000010 <add>:
        10:	01c28863          	beq	t0,t3,20 <end>
        14:	00130313          	addi	t1,t1,1
        18:	407282b3          	sub	t0,t0,t2
        1c:	ffce0ae3          	beq	t3,t3,10 <add>

    Used the riscv_lifter.sh script to generate the definition below
*)
Definition add_loop_riscv (a : addr) : N :=
    match a with
    | 0x8  => 0x00106393 (* ori     t2,zero,1 *)
    | 0xc  => 0x000e7e13 (* andi	t3,t3,0 *)
    | 0x10 => 0x01c28863 (* beq	t0,t3,20 <end> *)
    | 0x14 => 0x00130313 (* addi	t1,t1,1 *)
    | 0x18 => 0x407282b3 (* sub	t0,t0,t2 *)
    | 0x1c => 0xffce0ae3 (* beq	t3,t3,10 <add> *)
    | _ => 0 
    end.

(*
    Now to define correctness. Let's ignore most of the machinery and just look
    at what the invariants say:

    We have some input numbers x and y. These aren't machine numbers, but Rocq
    binary numbers. The insight here is that the semantics of the addloop code
    should implement the functional behavior of some ideal addition function.
    This gives us our postcondition, which calls Rocq's N.add function (wrapped
    in a 'mod 2^32', hence the circle plus).
*)
Definition postcondition (s : store) (x y : N) :=
    s R_T1 = x ⊕ y.

(*
    We really only have one invariant here (because we only have one loop in the
    code), and that's at address 0x10. It says:
        'given that registers T0 and T1 contain some numbers t0 and t1, and
         that registers T2 and T3 contain 1 and 0 respectively, the modular
         sum of t0 and t1 equals the modular sum of x and y'
    Why did I choose this invariant? What is an invariant?

    TLDR: an invariant is a statement that is true throughout each iteration of
    a loop. Invariants carry important information throughout the proof that
    would otherwise be lost as the interpreter leaves a loop. So if the loop
    does anything that impacts the correctness of the function (hint: they
    usually do), then that loop's invariant needs to encode that information.

    I chose the invariant that t0 + t1 = x + y because it's a direct generalization
    of the postcondition. We know that t0 is repeatedly subtracted from until it
    hits 0, leaving the sum in t1. So t0 + t1 eventually becomes 0 + (x + y).
*)
Definition addloop_correctness_invs (p : addr) (x y : N) (t:trace) :=
    match t with (Addr a, s) :: _ => match a with
        | 0x8  => Some (s R_T0 = x /\ s R_T1 = y)
        | 0x10 => Some (s R_T2 = 1 /\ s R_T3 = 0 /\ 
                s R_T0 ⊕ s R_T1 = x ⊕ y)
        | 0x20 => Some (postcondition s x y)
        | _ => None end
    | _ => None
    end.

(* Let's also define the exit point of addloop *)
Definition addloop_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x20 => true
  | _ => false
  end | _ => false end.

(* This function _lifts_ the binary code embedded in add_loop_riscv
   into an intermediate language (IL) called PicinaeIL. Proofs of
   correctness will (generally) operate only on the IL *)
Definition lifted_addloop := lift_riscv add_loop_riscv.

(* And now for the proof!

   Our partial correctness proof (partial because it assumes termination) 
*)
Theorem addloop_partial_correctness:
  forall s p t s' x' x y
         (ENTRY: startof t (x',s') = (Addr 0x8,s))  (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (T0: s R_T0 = x)                           (* Tie the contents of T0 to a *)
         (T1: s R_T1 = y),                          (* Tie the contents of T1 to b *)
  satisfies_all 
    lifted_addloop                                  (* Provide lifted code *)
    (addloop_correctness_invs p x y)                (* Provide invariant set *)
    addloop_exit                                    (* Provide exit point *)
  ((x',s')::t).
Proof.
    Local Ltac step := time r5_step.

    intros.
    apply prove_invs.

    (* Base case *)
    simpl. rewrite ENTRY. step. split.
        assumption.
        assumption.

    (* Inductive step setup *)
    intros. apply exec_prog_nextinv. intro XP.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* Starting from our entrypoint at address 6, we'll do some setup and then
       step to the next invariant *)
    destruct PRE as (T0 & T1). step. step.
    (* This goal is the invariant at 0x10 and has taken us to the case in which
       the loop has just started *)
    repeat split. subst. reflexivity.

    (* We now have to deal with the cases where the loop terminates and where it
       loops around. Notice we get our invariant as an assumption! *)
    destruct PRE as (T2 & T3 & Eq).
    (* Termination case - time to prove the postcondition *)
    step.
        rewrite N.eqb_eq in BC. rewrite BC in Eq.
        psimpl in Eq. assumption.
    (* Loop case - prove the invariant again *)
    step. step. step.
        repeat split. assumption.
Qed.

(* Total correctness uses a phase for the entry sequence and the remaining
   unsigned counter for the loop. No additional input restriction is needed. *)
Definition addloop_total_invs x y (t:trace) : option Prop :=
  match t with (Addr a,s)::_ => Some
    ((a = 0x8 /\ s R_T0 = x /\ s R_T1 = y /\ s R_T1 < 2^32) \/
     (a = 0x10 /\ s R_T2 = 1 /\ s R_T3 = 0 /\
       s R_T0 ⊕ s R_T1 = x ⊕ y /\ s R_T1 < 2^32) \/
     (a = 0x20 /\ postcondition s x y))
  | _ => None end.

Definition addloop_rank (t:trace) : N :=
  match t with (Addr a,s)::_ =>
    if a =? 0x8 then N.succ (s R_T0) else s R_T0
  | _ => 0 end.

Lemma addloop_decreases:
  forall n, n <> 0 -> n ⊖ 1 < n.
Proof.
  intros n NZ. destruct (N.lt_ge_cases n (2^32)) as [LT|GE].
    rewrite msub_nowrap.
      rewrite (N.mod_small n _ LT). cbn. lia.
      rewrite (N.mod_small n _ LT). cbn. lia.
    eapply N.lt_le_trans. apply msub_lt. exact GE.
Qed.

Theorem addloop_total_invariants:
  forall s x y (MDL: models rvtypctx s)
    (T0: s R_T0 = x) (T1: s R_T1 = y),
  satisfies_total lifted_addloop (addloop_total_invs x y) addloop_exit
    ((Addr 0x8,s)::nil).
Proof.
  intros. pose proof (models_var R_T1 MDL) as T1B.
  change (s R_T1 < 2^32) in T1B.
  eapply prove_total_invs with (rank:=addloop_rank) (R:=N.lt).
    exact N.lt_wf_0.
    total_here; cbn [addloop_total_invs true_inv]; psimpl. left. repeat split; assumption.
    intros t0 PRE. destruct t0 as [|[[a|i] s0] hist]; try contradiction.
    cbn [addloop_total_invs true_inv] in PRE.
    destruct PRE as [[A [T0' [T1' BOUND]]] | [[A [T2 [T3 [EQ BOUND]]]] | [A POST]]]; subst a.
      do 2 ISA_total_step. total_here; cbn [addloop_total_invs true_inv]; psimpl. right. split.
        right. left. repeat split; try reflexivity; try assumption; congruence.
        cbn [addloop_rank]; psimpl. apply N.lt_succ_diag_r.
      ISA_total_step.
        total_here; cbn [addloop_total_invs true_inv]; psimpl. left. split. reflexivity.
        right. right. split. reflexivity.
        unfold postcondition. rewrite N.eqb_eq in BC. rewrite BC in EQ.
        psimpl in EQ. psimpl. rewrite N.mod_small in EQ by exact BOUND. exact EQ.
      do 3 ISA_total_step. total_here; cbn [addloop_total_invs true_inv]; psimpl. right. split.
        right. left. repeat split; try assumption. apply mp2_mod_lt.
        cbn [addloop_rank]; psimpl. apply addloop_decreases. apply N.eqb_neq, BC.
      total_here; cbn [addloop_total_invs true_inv]; psimpl. left. split. reflexivity. right. right. split; [reflexivity|assumption].
Qed.

(* The public result uses precisely the invariant set of the partial proof. *)
Theorem addloop_total_correctness:
  forall s p x y (MDL: models rvtypctx s)
    (T0: s R_T0 = x) (T1: s R_T1 = y),
  satisfies_total lifted_addloop (addloop_correctness_invs p x y) addloop_exit
    ((Addr 0x8,s)::nil).
Proof.
  intros. unfold satisfies_total. eapply eventually_bind.
    exact (addloop_total_invariants s x y MDL T0 T1).
    intros t' [EX INV]. destruct t' as [|[[a|i] s0] hist]; try discriminate.
    cbn [addloop_total_invs true_inv] in INV.
    destruct INV as [[A _] | [[A _] | [A POST]]]; subst a; try discriminate.
    total_here. split; assumption.
Qed.

Corollary addloop_terminates:
  forall s p x y (MDL: models rvtypctx s)
    (T0: s R_T0 = x) (T1: s R_T1 = y),
  exists prefix, exec_prog lifted_addloop (prefix++(Addr 0x8,s)::nil) /\
    exit_post (addloop_correctness_invs p x y) addloop_exit
      (prefix++(Addr 0x8,s)::nil).
Proof.
  intros. apply eventually_reaches.
    apply addloop_total_correctness; assumption.
    apply exec_prog_none.
Qed.

Print Assumptions addloop_total_correctness.
Print Assumptions addloop_terminates.

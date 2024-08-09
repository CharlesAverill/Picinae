Require Import Picinae_riscv.
Require Import riscvTiming.
Import RISCVNotations.
Require Import NArith.
Require Import List.

Import ListNotations.
Open Scope N_scope.

(* 
    To create this function, I:
    - Wrote some assembly

            andi t0, t0, 5
            andi t1, t1, 9
        start:
            andi t2, t2, 1
            andi t3, t3, 0
        add:
            beq t0, t3, end
            addi t1, t1, 1
            sub t0, t0, t2
            beq t3, t3, add
        end:

    - Assembled it using a RISC-V cross-assembler
        https://github.com/riscv-collab/riscv-gnu-toolchain
        You can probably do this with clang instead of building a GCC (takes a long time)
      Command:
        charles@derelict:~/riscv-gnu-toolchain$ /usr/bin/riscv64-unknown-linux-gnu/bin/as addloop.s -o addloop.o

    - Dumped the assembled code
      Command:
        charles@derelict:~/riscv-gnu-toolchain$ /usr/bin/riscv64-unknown-linux-gnu/bin/objdump addloop.o -D
      This prints out a bunch of text:

        addloop.o:     file format elf64-littleriscv


        Disassembly of section .text:

        0000000000000000 <start-0x8>:
        0:	00506293          	ori	t0,zero,5
        4:	00906313          	ori	t1,zero,9

        0000000000000008 <start>:
        8:	00106393          	ori	t2,zero,1
        c:	000e7e13          	andi	t3,t3,0

        0000000000000010 <add>:
        10:	01c28863          	beq	t0,t3,20 <end>
        14:	00130313          	addi	t1,t1,1
        18:	407282b3          	sub	t0,t0,t2
        1c:	ffce0ae3          	beq	t3,t3,10 <add>

    - Manually copied the addresses and hex-encoded instructions to the function below
      I ignored the <start-0x8> section because it's just a test case and not a part of the program logic
*)
Definition add_loop_riscv (_ : store) (a : addr) : N :=
    match a with
    | 0x8  => 0x00106393 (* ori     t2,zero,1 *)
    | 0xc  => 0x000e7e13 (* andi	t3,t3,0 *)
    | 0x10 => 0x01c28863 (* beq	t0,t3,20 <end> *)
    | 0x14 => 0x00130313 (* addi	t1,t1,1 *)
    | 0x18 => 0x407282b3 (* sub	t0,t0,t2 *)
    | 0x1c => 0xffce0ae3 (* beq	t3,t3,10 <add> *)
    | _ => 0 
    end.
Definition add_loop_start : N := 0x8.
Definition add_loop_end   : N := 0x1c.

(*
    Now to define correctness. Let's ignore most of the machinery and just look
    at what the invariants say:

    We have some input numbers x and y. These aren't machine numbers, but Coq
    binary numbers. The insight here is that the semantics of the addloop code
    should implement the functional behavior of some ideal addition function.
    This gives us our postcondition, which calls coq's N.add function (wrapped
    in a 'mod 2^32', hence the circle plus).
*)
Definition postcondition (s : store) (x y : N) :=
    s R_T1 = Ⓓ(x ⊕ y).

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

    TODO : Hamlen should check explanation after this point
    We place an invariant at the entrance to the function just for setup, and
    we place our postcondition at the exit point of the function.
*)
Definition addloop_correctness_invs (_ : store) (p : addr) (x y : N) (t:trace) :=
    match t with (Addr a, s) :: _ => match a with
        | 0x8  => Some (s R_T0 = VaN x 32 /\ s R_T1 = VaN y 32)
        | 0x10 => Some (exists t0 t1, 
            s R_T0 = Ⓓt0 /\ s R_T1 = Ⓓt1 /\ s R_T2 = Ⓓ1 /\ s R_T3 = Ⓓ0 /\ 
                t0 ⊕ t1 = x ⊕ y)
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

(*
    TODO : FIX JANK
    This is all machinery I use to lift code. I converted the above function into a list,
    transformed it into Picinae IL. There should be a much easier way to just map IL onto
    the function above instead of all of this. Or maybe not. Hamlen question.
*)
Definition lifted_addloop := lift_via_list add_loop_riscv add_loop_start add_loop_end.

(*
    And now for the proofs:
*)

(* Well-typedness of the lifted code, automatic *)
Theorem addloop_welltyped: welltyped_prog rvtypctx lifted_addloop.
Proof. Picinae_typecheck. Qed.

(* Our partial correctness proof (partial because it assumes termination) *)
Theorem addloop_partial_correctness:
  forall s p t s' x' a b
         (ENTRY: startof t (x',s') = (Addr 0x8,s)) (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (T0: s R_T0 = VaN a 32)                   (* Tie the contents of T0 to a *)
         (T1: s R_T1 = VaN b 32),                  (* Tie the contents of T1 to b *)
  satisfies_all 
    lifted_addloop                                 (* Provide lifted code *)
    (addloop_correctness_invs s p a b)             (* Provide invariant set *)
    addloop_exit                                   (* Provide exit point *)
  ((x',s')::t).
Proof.
    Local Ltac step := time rv_step.

    intros.
    apply prove_invs.

    (* Base case *)
    simpl. rewrite ENTRY. step. split.
        assumption.
        assumption.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply addloop_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* Starting from our entrypoint at address 6, we'll do some setup and then
       step to the next invariant *)
    destruct PRE as [T0 T1]. step. step.
    (* This goal is the invariant at 0x10 and has taken us to the case in which
       the loop has just started *)
    (* A big mess, but most of this is solvable with reflexivity *)
    exists a, b. repeat split.
        assumption.
        assumption.

    (* We now have to deal with the cases where the loop terminates and where it
       loops around. Notice we get our invariant as an assumption! *)
    destruct PRE as [t0 [t1 [T0 [T1 [T2 [T3 Eq]]]]]].
    (* Termination case - time to prove the postcondition *)
    step.
        rewrite N.eqb_eq in BC. subst. psimpl in Eq.
        unfold postcondition. psimpl. rewrite <- Eq. assumption.
    (* Loop case - prove the invariant again *)
    step. step. step.
        rewrite N.eqb_neq in BC. exists (t0 ⊖ 1), (1 ⊕ t1). repeat split.
        psimpl. assumption.
Qed.

(* Timing proof - lots of machinery here has yet to be modularized *)
Variable ML : N.
Variable ML_pos : 1 <= ML.

Module riscv_toa.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound ML s (add_loop_riscv s a) with
        | Some x => x | _ => 0 end.
End riscv_toa.

Module riscvT := MakeTimingContents riscvTiming riscv_toa.
Export riscvT.

Definition cycle_count_of_trace := cycle_count_of_trace time_of_addr.

Arguments N.add _ _ : simpl nomatch.

Definition addloop_timing_invs (_ : store) (p : addr) (x y : N) (t:trace) :=
match t with (Addr a, s) :: t' => match a with
    | 0xc  => Some (s R_T0 = Ⓓx /\ s R_T2 = Ⓓ1 /\ cycle_count_of_trace t = 2 + 2)
    | 0x10 => Some (exists t0, s R_T0 = Ⓓt0 /\ s R_T2 = Ⓓ1 /\ s R_T3 = Ⓓ0 /\ t0 <= x /\
        cycle_count_of_trace t' = 4 + (x - t0) * (12 + (ML - 1)))
        (* 2 + 2 + (x - t0) * (3 + 2 + 2 + (5 + (ML - 1)) *)
    | 0x20 => Some (cycle_count_of_trace t' = 9 + (ML - 1) + x * (12 + (ML - 1)))
        (* 2 + 2 + (5 + (ML - 1)) + x * (3 + 2 + 2 + (5 + (ML - 1))) *)
    | _ => None end
| _ => None
end.

Ltac unfold_decompose :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype decompose_Stype decompose_Utype mask_bit_section];
        simpl (_ .& _).
Tactic Notation "unfold_decompose" "in" hyp(H) :=
    cbv [decompose_Btype decompose_Itype decompose_Jtype decompose_Rtype decompose_Stype decompose_Utype mask_bit_section] in H;
        simpl (_ .& _) in H.

Ltac unfold_time_of_addr :=
    cbv [time_of_addr neorv32_cycles_upper_bound]; simpl.
Tactic Notation "unfold_time_of_addr" "in" hyp(H) :=
    cbv [time_of_addr neorv32_cycles_upper_bound] in H; simpl in H.

Ltac unfold_cycle_count_list :=
    unfold cycle_count_of_trace; repeat rewrite cycle_count_of_trace_cons, cycle_count_of_trace_single; fold cycle_count_of_trace.

Theorem addloop_timing:
  forall s p t s' x' a b
         (ENTRY: startof t (x',s') = (Addr 0x8,s)) (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (T0: s R_T0 = VaN a 32)                   (* Tie the contents of T0 to a *)
         (T1: s R_T1 = VaN b 32),                  (* Tie the contents of T1 to b *)
  satisfies_all 
    lifted_addloop                                 (* Provide lifted code *)
    (addloop_timing_invs s p a b)                  (* Provide invariant set *)
    addloop_exit                                   (* Provide exit point *)
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    (* Base case *)
    simpl. rewrite ENTRY. step. now repeat split.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply addloop_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* Addr 0xc *)
    destruct PRE as [T0 [T2 Cycles]].
    step. exists a. repeat split; try assumption. lia. 
    psimpl. now rewrite Cycles.

    (* Addr 0x10 *)
    destruct PRE as [t0 [T0 [T2 [T3 [T0_A Cycles_t]]]]].
    step.
    - (* t0 = 0 -> postcondition *)
        rewrite N.eqb_eq in BC; subst. unfold_cycle_count_list.
        unfold_time_of_addr. rewrite T0, T3, Cycles_t. now psimpl.
    - (* t0 <> 0 -> loop again *)
        step. step. step. exists (t0 ⊖ 1). assert (1 <= t0) by (apply N.eqb_neq in BC; lia). repeat split.
            rewrite msub_nowrap; psimpl; lia.
        unfold_cycle_count_list.
        repeat (let Y := fresh "H" in (remember ((time_of_addr _) _) eqn:Y; unfold_time_of_addr in Y; subst)).
        rewrite T0, T3, BC, Cycles_t, N.add_sub_assoc, msub_nowrap, N_sub_distr.
        psimpl. rewrite N.mul_add_distr_r. psimpl.
        rewrite (N.add_sub_assoc 16).

        all: psimpl; (assumption || lia || apply ML_pos).
Qed.

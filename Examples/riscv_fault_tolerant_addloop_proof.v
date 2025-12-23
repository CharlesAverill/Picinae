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
            li t2, 1
            li t2, 1
        add:
            beqz t0, end
            beqz t0, end
            addi t4, t1, 1
            addi t4, t1, 1
            sub t5, t0, t2
            sub t5, t0, t2
            mv t1, t4
            mv t1, t4
            mv t0, t5
            mv t0, t5
            j add
            j add
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

            Disassembly of section .text:

            00000000 <start>:
            0:   00100393                addi    t2,zero,1
            4:   00100393                addi    t2,zero,1

            00000008 <add>:
            8:   02028863                beq     t0,zero,38 <end>
            c:   02028663                beq     t0,zero,38 <end>
            10:   00130e93                addi    t4,t1,1
            14:   00130e93                addi    t4,t1,1
            18:   40728f33                sub     t5,t0,t2
            1c:   40728f33                sub     t5,t0,t2
            20:   000e8313                addi    t1,t4,0
            24:   000e8313                addi    t1,t4,0
            28:   000f0293                addi    t0,t5,0
            2c:   000f0293                addi    t0,t5,0
            30:   fd9ff06f                jal     zero,8 <add>
            34:   fd5ff06f                jal     zero,8 <add>

    Used the riscv_lifter.sh script to generate the definition below
*)
Definition add_loop_riscv_ft (a : addr) : N :=
    match a with
    (* <start> *)
    | 0x0 => 0x00100393 (* addi t2,zero,1  *)
    | 0x4 => 0x00100393 (* addi t2,zero,1  *)
    (* <add> *)
    | 0x8 => 0x02028863 (* beq t0,zero,38 <end>  *)
    | 0xc => 0x02028663 (* beq t0,zero,38 <end>  *)
    | 0x10 => 0x00130e93 (* addi t4,t1,1  *)
    | 0x14 => 0x00130e93 (* addi t4,t1,1  *)
    | 0x18 => 0x40728f33 (* sub t5,t0,t2  *)
    | 0x1c => 0x40728f33 (* sub t5,t0,t2  *)
    | 0x20 => 0x000e8313 (* addi t1,t4,0  *)
    | 0x24 => 0x000e8313 (* addi t1,t4,0  *)
    | 0x28 => 0x000f0293 (* addi t0,t5,0  *)
    | 0x2c => 0x000f0293 (* addi t0,t5,0  *)
    | 0x30 => 0xfd9ff06f (* jal zero,8 <add>  *)
    | 0x34 => 0xfd5ff06f (* jal zero,8 <add>  *)
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
        | 0x0 => Some (s R_T0 = x /\ s R_T1 = y /\ s V_FC = 1)
        | 0x8 => Some (s R_T2 = 1 /\ s V_FC <= 1 /\
                        s R_T0 ⊕ s R_T1 = x ⊕ y)
        | 0x38 => Some (postcondition s x y)
        | _ => None end
    | _ => None
    end.

(* Let's also define the exit point of addloop *)
Definition addloop_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x38 => true
  | _ => false
  end | _ => false end.

(* This function _lifts_ the binary code embedded in add_loop_riscv_ft
   into an intermediate language (IL) called PicinaeIL. Proofs of
   correctness will (generally) operate only on the IL *)
Definition lifted_addloop := lift_riscv add_loop_riscv_ft.

(* This function wraps our lifted program in a block of Picinae IL that
   simulates fault injection attacks. At each `step`, we will have to reason
   about the possibility that that step was the victim instruction, and did not occur *)
Definition inject_fault (p : program) (s : store) (a : addr) :=
  match p s a with
  | None => None
  | Some (sz,q) => Some (sz,
    If (BinOp OP_AND (BinOp OP_LT (Word 0x0 32) (Var V_FC)) (Unknown 1))
      (Move V_FC (BinOp OP_MINUS (Var V_FC) (Word 0x1 32)))
      q)
  end.
Definition wrapped_addloop := inject_fault lifted_addloop.

Lemma inject_fault_lift_riscv_welltyped : forall p,
    welltyped_prog rvtypctx (inject_fault (lift_riscv p)).
Proof.
    intros p s a. unfold inject_fault, lift_riscv.
    exists rvtypctx.
    econstructor.
    change 1 with (widthof_binop OP_AND 1). constructor.
        change 1 with (widthof_binop OP_LT 32). constructor.
        constructor. lia. constructor. reflexivity.
        constructor.
    econstructor. now right.
        change 32 with (widthof_binop OP_MINUS 32). constructor.
        now constructor.
        constructor. lia.
        eapply typchk_stmt_mono with (c := rvtypctx) (c0 := rvtypctx)
            (q := Move V_FC (BinOp OP_MINUS (Var V_FC) (Word 1 32))).
        reflexivity. reflexivity.
    apply welltyped_rv2il.
    reflexivity.
Qed.

(* And now for the proof!

   Our partial correctness proof (partial because it assumes termination) 
*)
Theorem addloop_partial_correctness:
  forall s p t s' x' x y
         (ENTRY: startof t (x',s') = (Addr 0x0,s))  (* Define the entry point of the function *)
         (MDL: models rvtypctx s)
         (T0: s R_T0 = x)                           (* Tie the contents of T0 to a *)
         (T1: s R_T1 = y)                           (* Tie the contents of T1 to b *)
         (FC: s V_FC = 1),                          (* We will reason about this program when 1 fault can occur *)
  satisfies_all 
    wrapped_addloop                                 (* Provide lifted code *)
    (addloop_correctness_invs p x y)                (* Provide invariant set *)
    addloop_exit                                    (* Provide exit point *)
  ((x',s')::t).
Proof.
    Local Ltac step := 
        match goal with
        | [s' : store, FC : ?s' V_FC <= 1 |- _] =>
            let H := fresh "H" in
            assert (s' V_FC = 0 \/ s' V_FC = 1) as H by lia;
            clear FC; destruct H
        | _ => idtac
        end;
        time r5_step;
        repeat match goal with
        | [n : N, BC : ?n mod 2 = _ |- _] => clear BC n
        | [s' : store, n : N, 
            BC : (if 0 <? ?s' V_FC then ?n mod 2 else 0) = _ |- _] => clear BC n
        | [H: ?x = ?x |- _] => clear H
        end;
        try discriminate.

    intros.
    apply prove_invs.

    (* Base case *)
    simpl. rewrite ENTRY. step. auto.

    (* Inductive step setup *)
    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply inject_fault_lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s1 into s'.

    (* Meat of proof starts here *)
    destruct_inv 32 PRE.

    (* Starting from our entrypoint at address 6, we'll do some setup and then
       step to the next invariant *)
    destruct PRE as (T0 & T1 & FC).
    step.
    (* Fault has not occurred *)
        step.
        (* Fault has not occurred *)
        repeat split; auto. lia.
            now rewrite T0, T1.
        (* Fault has occurred, prove loop invariant *)
        repeat split; auto. lia. now rewrite T0, T1.
    (* Fault has occurred *)
    (* We are now in a branch where a fault can no longer occur *)
        repeat step; repeat split. lia. now rewrite T0, T1.

    destruct PRE as (T2 & FC & Eq).
    Ltac solve_inv := repeat split; psimpl; try lia.
    Ltac solve_post :=
        match goal with
        | [s' : store, Eq : ?s' R_T0 ⊕ ?s' R_T1 = ?x ⊕ ?y,
                BC: (?s' R_T0 =? 0) = true |- _] =>
            apply N.eqb_eq in BC; rewrite BC in *; now psimpl in Eq
        end.
    step; try solve_post.
    1,3: repeat step; solve_inv; solve_post.
    repeat (step; [| repeat step; solve_inv]); solve_inv.
    Unshelve. exact (fun _ => 0).
Admitted.

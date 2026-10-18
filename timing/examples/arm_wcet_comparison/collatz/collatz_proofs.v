From Picinae.timing.examples.arm_wcet_comparison.collatz Require Import collatz.
Require Import ARMv6MTiming.
Import ARMv6MNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : ARMv6MCPUTimingBehavior).
Import cpu.

Module Program_collatz <: ProgramInformation.
    Definition entry_addr : N := 0x8000000.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        (* return *)
        | 0x800002a => true
        | _ => false
    end | _ => false end.

    Definition binary := collatz_collatz_armv6m.
End Program_collatz.

Module ARMv6MTiming := ARMv6MTiming cpu Program_collatz.
Module collatzAuto := ARMv6MTimingAutomation ARMv6MTiming.
Import Program_collatz collatzAuto.

(* Times of the pieces of the loop *)
(* test if n is odd, even: tst, beq (taken) *)
Definition t_even := ttst + tb_taken.
(* test if n is odd, odd: tst, beq, lsls, adds, adds, adds, uxth, cmp (then beq) *)
Definition t_odd := ttst + tb_not_taken + tlsls_imm + tadds_3reg + tadds_imm8 +
                    tadds_imm8 + tuxth + tcmp_reg.
(* halve n, which reaches 1: lsrs, cmp, bne, pop (the return) *)
Definition t_half_ret := tlsrs_imm + tcmp_imm + tb_not_taken + (tpop_pc_base + 2).
(* halve n, which doesn't reach 1: lsrs, cmp, bne (taken) *)
Definition t_half_loop := tlsrs_imm + tcmp_imm + tb_taken.
(* the counter reached 55000 without n reaching 1: movs, b, pop (return 0).
   The slow path in the source doesn't change the result, so GCC removes it. *)
Definition t_ret0 := tmovs_imm + tb + (tpop_pc_base + 2).
(* increment and overflow check, which overflows: adds, cmp, beq, then return 0 *)
Definition t_head_exit := tadds_imm8 + tcmp_reg + tb_taken + t_ret0.
(* increment and overflow check, which doesn't overflow: adds, cmp, beq *)
Definition t_head_cont := tadds_imm8 + tcmp_reg + tb_not_taken.

(* The time from the odd/even test with value n until the return, when the
   counter may be incremented k more times before reaching 55000. *)
Fixpoint collatz_from (k : nat) (n : N) : N :=
    match k with
    | O => 0
    | S k' =>
        if n mod 2 =? 0 then
            t_even +
            if N.div2 n =? 1 then t_half_ret
            else t_half_loop +
                match k' with
                | O => t_head_exit
                | S _ => t_head_cont + collatz_from k' (N.div2 n)
                end
        else
            t_odd +
            match k' with
            | O => tb_taken + t_ret0
            | S k'' => tb_not_taken +
                if N.div2 ((1 + n + (n << 1)) mod 65536) =? 1 then t_half_ret
                else t_half_loop +
                    match k'' with
                    | O => t_head_exit
                    | S _ => t_head_cont + collatz_from k'' (N.div2 ((1 + n + (n << 1)) mod 65536))
                    end
            end
    end.

(* The time from the counter increment at the top of the loop, with counter i
   and value n, until the return *)
Definition head_rest (i n : N) : N :=
    if 1 + i =? 55000 then t_head_exit
    else t_head_cont + collatz_from (N.to_nat (55000 - (1 + i))) n.

(* Unfold one test of collatz_from, at counter i *)
Lemma collatz_from_unfold :
    forall i n, i < 55000 ->
    collatz_from (N.to_nat (55000 - i)) n =
        if n mod 2 =? 0 then
                t_even + (if N.div2 n =? 1 then t_half_ret else t_half_loop + head_rest i (N.div2 n))
        else
                t_odd + (if 1 + i =? 55000 then tb_taken + t_ret0 else tb_not_taken +
                        if N.div2 ((1 + n + (n << 1)) mod 65536) =? 1 then t_half_ret
                        else t_half_loop + head_rest (1 + i) (N.div2 ((1 + n + (n << 1)) mod 65536))).
Proof.
    intros i n I. unfold head_rest.
    replace (N.to_nat (55000 - i)) with (S (N.to_nat (55000 - (1 + i)))) by lia.
    cbn [collatz_from].
    destruct (N.eqb_spec (1 + i) 55000) as [E1|E1].
    - rewrite E1. reflexivity.
    - replace (N.to_nat (55000 - (1 + i))) with (S (N.to_nat (55000 - (1 + (1 + i))))) by lia.
        cbv iota beta.
        destruct (N.eqb_spec (1 + (1 + i)) 55000) as [E2|E2].
        + rewrite E2. reflexivity.
        + destruct (N.to_nat (55000 - (1 + (1 + i)))) eqn:E3; [ lia | reflexivity ].
Qed.

Definition collatz_cycles (n : N) : N :=
    (* setup *)
    tmovs_reg + (tpush_base + 1 + 1) + tmovs_imm + tmovs_imm + tldr_pc + tb +
    collatz_from (N.to_nat 55000) n.

Definition time_of_collatz (n : N) (t : trace) :=
    cycle_count_of_trace t = collatz_cycles n.

Definition collatz_timing_invs (n : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000000 => Some (
    s R_R0 = n /\ 1 <= n < 65536 /\
    cycle_count_of_trace t' = 0
  )
| 0x800000c => Some (
    1 <= n < 65536 /\
    s R_R3 < 65536 /\ s R_R4 = 1 /\ s R_R2 = 55000 /\
    s R_R0 < 55000 /\
    (* the time so far is the total less the time remaining *)
    head_rest (s R_R0) (s R_R3) <= collatz_cycles n /\
    cycle_count_of_trace t' = collatz_cycles n - head_rest (s R_R0) (s R_R3)
  )
| 0x800002a => Some (time_of_collatz n t)
| _ => None end | _ => None end.

(* Branch conditions as facts, halving and shifts as division and multiplication *)
Ltac normalize :=
    repeat match goal with
    | [ H: (_ =? _) = true |- _ ] => apply N.eqb_eq in H
    | [ H: (_ =? _) = false |- _ ] => apply N.eqb_neq in H
    end;
    rewrite ?N.div2_div, ?N.shiftr_div_pow2, ?N.shiftl_mul_pow2, ?N.add_0_r in *;
    change (2^1) with 2 in *; change (2^16) with 65536 in *;
    unfold t_even, t_odd, t_half_ret, t_half_loop, t_head_exit, t_head_cont, t_ret0 in *.

(* Decide the remaining conditionals, and solve each case *)
Ltac decide_ifs :=
    repeat match goal with
    | [ |- context [ if (?x =? ?y) then _ else _ ] ] => destruct (N.eqb_spec x y); try lia
    | [ H: context [ if (?x =? ?y) then _ else _ ] |- _ ] => destruct (N.eqb_spec x y); try lia
    end;
    try lia.

Ltac finish_entry :=
    unfold collatz_cycles;
    change (N.to_nat 55000) with (N.to_nat (55000 - 0));
    rewrite (collatz_from_unfold 0) by lia;
    normalize; decide_ifs.

Ltac finish_loop C :=
    match type of C with context [ head_rest ?i ?m ] =>
        let R := fresh "R" in let ER := fresh "ER" in
        remember (head_rest i m) as R eqn:ER;
        unfold head_rest in ER;
        repeat match goal with |- context [ (?a mod 4294967296) ] =>
            rewrite (N.mod_small a) by lia
        end;
        destruct (N.eqb_spec (1 + i) 55000);
        [ normalize; decide_ifs
        | rewrite collatz_from_unfold in ER by lia;
          replace (1 + (1 + i)) with (2 + i) in ER by lia;
          normalize; decide_ifs ]
    end.

Theorem collatz_timing:
  forall s t s' x' n
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models armv6mtypctx s)
         (* bindings *)
         (R0: s R_R0 = n)
         (SIZE: 1 <= n < 65536),
  satisfies_all
    lifted_prog
    (collatz_timing_invs n)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep armv6m_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto; lia.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped_lift_armv6m].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.
    - destruct PRE as (R0 & Bounds & Cycles).
        repeat step.
        all: hammer.
        (* hammer leaves halving as a shift and 2^32 unevaluated *)
        all: rewrite <- ?N.div2_spec in *; try change (2^32) with 4294967296 in *.
        all: repeat split; try lia.
        all: finish_entry.
    - destruct PRE as (NBounds & R3B & R4 & R2 & R0B & Rest & Cycles).
        repeat step.
        all: hammer.
        (* hammer leaves halving as a shift and 2^32 unevaluated *)
        all: rewrite <- ?N.div2_spec in *; try change (2^32) with 4294967296 in *.
        all: repeat split; try lia.
        all: finish_loop Rest.
Qed.

End TimingProof.

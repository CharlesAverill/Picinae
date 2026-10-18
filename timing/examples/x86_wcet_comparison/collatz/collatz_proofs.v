From Picinae.timing.examples.x86_wcet_comparison.collatz Require Import collatz.
Require Import AMD64Timing.
Import X64Notations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : amd64CPUTimingBehavior).
Import cpu.

Module Program_collatz <: ProgramInformation.
    Definition entry_addr : N := 0x0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x33 | 0x34 | 0x35 => true
        | _ => false
    end | _ => false end.

    Definition time_of_addr (s : store) (a : addr) : N :=
        match a with
        (* 0x00101160: XOR EAX,EAX *)
        | 0x0 => xor_r32_r32
        (* 0x00101162: JMP 0x00101174 *)
        | 0x2 => jmp_addr
        (* 0x00101168: ADD RAX,0x1 *)
        | 0x8 => add_r64_i
        (* 0x0010116c: CMP RAX,0xd6d8 *)
        | 0xc => cmp_r64_i
        (* 0x00101172: JZ 0x00101194 *)
        | 0x12 => jz_addr
        (* 0x00101174: TEST DIL,0x1 *)
        | 0x14 => test_r8_i
        (* 0x00101178: JZ 0x0010118a *)
        | 0x18 => jz_addr
        (* 0x0010117a: ADD RAX,0x1 *)
        | 0x1a => add_r64_i
        (* 0x0010117b: LEA EDI,[RDI + RDI*0x2 + 0x1] *)
        | 0x1e => lea_r64_addr
        (* 0x00101182: CMP RAX,0xd6d8 *)
        | 0x22 => cmp_r64_i
        (* 0x00101188: JZ 0x00101195 *)
        | 0x28 => jz_addr
        (* 0x0010118a: SHR DI,0x1 *)
        | 0x2a => shr_r16_i
        (* 0x0010118d: CMP DI,0x1 *)
        | 0x2d => cmp_r16_i
        (* 0x00101191: JNZ 0x00101168 *)
        | 0x31 => jnz_addr
        (* 0x00101193: RET *)
        | 0x33 => ret
        (* 0x00101194: RET *)
        | 0x34 => ret
        (* 0x00101195: RET *)
        | 0x35 => ret
        | _ => time_inf
        end.

    Definition lifted_prog := collatz_collatz_amd64.
End Program_collatz.

Module AMD64Timing := AMD64Timing cpu Program_collatz.
Module collatzAuto := AMD64TimingAutomation AMD64Timing.
Import Program_collatz collatzAuto.

(* Times of the pieces of the loop *)
(* test if n is odd, even: test, jz *)
Definition t_even := test_r8_i + jz_addr.
(* test if n is odd, odd: test, jz, add, lea, cmp (then jz) *)
Definition t_odd := test_r8_i + jz_addr + add_r64_i + lea_r64_addr + cmp_r64_i + jz_addr.
(* halve n, which reaches 1: shr, cmp, jnz, ret *)
Definition t_half_ret := shr_r16_i + cmp_r16_i + jnz_addr + ret.
(* halve n, which doesn't reach 1: shr, cmp, jnz *)
Definition t_half_loop := shr_r16_i + cmp_r16_i + jnz_addr.
(* increment and overflow check, which overflows: add, cmp, jz, ret *)
Definition t_head_exit := add_r64_i + cmp_r64_i + jz_addr + ret.
(* increment and overflow check, which doesn't overflow: add, cmp, jz *)
Definition t_head_cont := add_r64_i + cmp_r64_i + jz_addr.

(* The value of DI after an odd step (3n+1, truncated to 16 bits) and the
   halving which follows it *)
Definition odd_next (n : N) : N := N.div2 ((1 + n + n * 2) mod 65536).

(* The time from the odd/even test with value n until a return, when the
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
            | O => ret
            | S k'' =>
                if odd_next n =? 1 then t_half_ret
                else t_half_loop +
                    match k'' with
                    | O => t_head_exit
                    | S _ => t_head_cont + collatz_from k'' (odd_next n)
                    end
            end
    end.

(* The time from the counter increment at the top of the loop, with counter i
   and value n, until a return *)
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
                t_odd + (if 1 + i =? 55000 then ret else
                        if odd_next n =? 1 then t_half_ret
                        else t_half_loop + head_rest (1 + i) (odd_next n)).
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
    xor_r32_r32 + jmp_addr +
    collatz_from (N.to_nat 55000) n.

Definition time_of_collatz (n : N) (t : trace) :=
    cycle_count_of_trace t <= collatz_cycles n.

Definition collatz_timing_invs (n : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x0 => Some (
    s R_RDI = n /\ 1 <= n < 65536 /\
    cycle_count_of_trace t' = 0
  )
| 0x8 => Some (
    1 <= n < 65536 /\
    s R_RDI < 32768 /\
    s R_RAX < 55000 /\
    (* the time so far is the total less the time remaining *)
    head_rest (s R_RAX) (s R_RDI) <= collatz_cycles n /\
    cycle_count_of_trace t' = collatz_cycles n - head_rest (s R_RAX) (s R_RDI)
  )
| 0x33 | 0x34 | 0x35 => Some (time_of_collatz n t)
| _ => None end | _ => None end.

(* SHR DI sign-extends its 16-bit result, which is always nonnegative *)
Lemma scast_16_64_small :
    forall x, x < 32768 -> scast 16 64 x = x.
Proof.
    intros. unfold scast.
    rewrite (proj1 (toZ_nonneg 16 x)); rewrite (N.mod_small x) by lia.
        rewrite ofZ_N2Z. apply N.mod_small. lia.
        cbn. lia.
Qed.

Lemma div2_small :
    forall x, x < 65536 -> N.div2 x < 2^15.
Proof. intros. rewrite N.div2_div. change (2^15) with 32768. lia. Qed.

Lemma odd_next_small :
    forall x, odd_next x < 2^15.
Proof. intros. unfold odd_next. apply div2_small, N.mod_lt. discriminate. Qed.

Lemma scast_16_64_div2 :
    forall x, scast 16 64 (N.div2 (x mod 65536)) = N.div2 (x mod 65536).
Proof.
    intros. apply scast_16_64_small, div2_small, N.mod_lt. discriminate.
Qed.

Lemma scast_16_64_div2_mod :
    forall x, scast 16 64 (N.div2 (x mod 65536)) mod 65536 = N.div2 (x mod 65536).
Proof.
    intros. rewrite scast_16_64_div2. apply N.mod_small.
    eapply N.lt_trans. apply div2_small, N.mod_lt. discriminate. reflexivity.
Qed.

(* Branch conditions as facts, the counter and DI as their values *)
Ltac normalize :=
    repeat match goal with
    | [ H: (_ =? _) = true |- _ ] => apply N.eqb_eq in H
    | [ H: (_ =? _) = false |- _ ] => apply N.eqb_neq in H
    end;
    rewrite ?N.lxor_nilpotent, ?N.shiftr_0_r, <- ?N.div2_spec in *;
    try change (scast 32 64 0) with 0 in *;
    try change (2^16) with 65536 in *;
    rewrite ?scast_16_64_div2_mod, ?scast_16_64_div2 in *;
    repeat match goal with
    | [ |- context [ ?a mod ?m ] ] => rewrite (N.mod_small a m) by lia
    | [ H: context [ ?a mod ?m ] |- _ ] => rewrite (N.mod_small a m) in H by lia
    end;
    try change (N.div2 ((1 + ?x + ?x * 2) mod 65536)) with (odd_next x) in *;
    rewrite ?N.add_0_r in *;
    unfold t_even, t_odd, t_half_ret, t_half_loop, t_head_exit, t_head_cont in *.

(* Decide the remaining conditionals, and solve each case *)
Ltac decide_ifs :=
    repeat match goal with
    | [ |- context [ if (?x =? ?y) then _ else _ ] ] => destruct (N.eqb_spec x y); try lia
    | [ H: context [ if (?x =? ?y) then _ else _ ] |- _ ] => destruct (N.eqb_spec x y); try lia
    end;
    try lia.

(* The new value of DI fits in 15 bits *)
Ltac di_bound :=
    first [ apply odd_next_small | apply div2_small; lia ].

Ltac finish_entry :=
    unfold collatz_cycles;
    change (N.to_nat 55000) with (N.to_nat (55000 - 0));
    rewrite (collatz_from_unfold 0) by lia;
    normalize; decide_ifs.

Ltac finish_loop :=
    match goal with [ Rest: head_rest ?i ?m <= _ |- _ ] =>
        let R := fresh "R" in let ER := fresh "ER" in
        remember (head_rest i m) as R eqn:ER;
        unfold head_rest in ER;
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
         (MDL: models x64typctx s)
         (* bindings *)
         (RDI: s R_RDI = n)
         (SIZE: 1 <= n < 65536),
  satisfies_all
    lifted_prog
    (collatz_timing_invs n)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep x64_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; auto; lia.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 64 PRE.
    - destruct PRE as (RDI & Bounds & Cycles).
        repeat step.
        all: hammer.
        all: repeat split; try lia.
        all: normalize.
        all: try lia.
        all: try di_bound.
        all: finish_entry.
    - destruct PRE as (NBounds & RDIB & RAXB & Rest & Cycles).
        repeat step.
        all: hammer.
        all: repeat split; try lia.
        all: normalize.
        all: try di_bound.
        all: finish_loop.
Qed.

End TimingProof.

Require Import i5_7300u.
Module i5_7300u_collatz := TimingProof i5_7300u.

(* n = 27 reaches 1 *)
Goal i5_7300u_collatz.collatz_cycles 27 = 3657.
    vm_compute. reflexivity.
Qed.

(* n = 21845 has 3n+1 = 65536, which truncates to 0 in DI, so the loop runs
   until the counter reaches 55000. Evaluating collatz_cycles on every n in
   [1, 65536) shows this is the largest. *)
Goal i5_7300u_collatz.collatz_cycles 21845 = 2145020.
    vm_compute. reflexivity.
Qed.

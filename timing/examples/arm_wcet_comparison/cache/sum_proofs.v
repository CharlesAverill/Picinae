Require Import sum_lifted.
Require Import AMD64Timing.
Import X64Notations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu : amd64CPUTimingBehavior).
Import cpu.

Module Program_sum <: ProgramInformation.
    Definition entry_addr : N := 0x0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x22 | 0x1b => true
        | _ => false
    end | _ => false end.

    Definition time_of_addr (s : store) (a : addr) : N :=
        match a with
        (* 0x0: TEST RSI,RSI *)
        | 0x0  => test_r64_r64
        (* 0x3: JZ 0x001012b0 *)
        | 0x3  => jz_addr
        (* 0x5: LEA RDX,[RDI + RSI*0x4] *)
        | 0x5  => lea_r64_addr
        (* 0x9: XOR EAX,EAX *)
        | 0x9  => xor_r32_r32
        (* 0xb: NOP dword ptr [RAX + RAX*0x1] *)
        | 0xb  => nop
        (* 0x10: ADD EAX,dword ptr [RDI] *)
        | 0x10 => add_r32_m32
        (* 0x12: ADD RDI,0x4 *)
        | 0x12 => add_r64_i
        (* 0x16: CMP RDI,RDX *)
        | 0x16 => cmp_r64_r64
        (* 0x19: JNZ 0x001012a0 *)
        | 0x19 => jnz_addr
        (* 0x1b: RET *)
        | 0x1b => ret
        (* 0x20: XOR EAX,EAX *)
        | 0x20 => xor_r32_r32
        (* 0x22: RET *)
        | 0x22 => ret
        | _ => time_inf
        end.

    Definition lifted_prog := cache_sum_amd64.
End Program_sum.

Module AMD64Timing := AMD64Timing cpu Program_sum.
Module sumAuto := AMD64TimingAutomation AMD64Timing.
Import Program_sum sumAuto.

Definition time_of_sum (size : N) (t : trace) :=
  cycle_count_of_trace t <=
    test_r64_r64 + jz_addr +
    if size =? 0 then (
        xor_r32_r32 + ret
    ) else (
        lea_r64_addr + xor_r32_r32 + nop +
        size * (
            add_r32_m32 + add_r64_i + cmp_r64_r64 + jnz_addr
        ) + ret
    ).

Definition sum_timing_invs (arr : addr) (size : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x0 => Some (
    s R_RDI = arr /\ s R_RSI = size /\ 0 <= size < 1000 /\
    cycle_count_of_trace t' = 0
  )
| 0x10 => Some (exists i,
    s R_RDI = arr ⊕ 4 * i /\ s R_RDX = arr ⊕ 4 * size /\
    size =? 0 = false /\
    i < size < 1000 /\
    cycle_count_of_trace t' <=
        test_r64_r64 + jz_addr + lea_r64_addr + xor_r32_r32 + nop +
        i * (
            add_r32_m32 + add_r64_i + cmp_r64_r64 + jnz_addr
        )
  )
| 0x22 | 0x1b => Some (time_of_sum size t)
| _ => None end | _ => None end.

Theorem sum_timing:
  forall s t s' x' arr size
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models x64typctx s)
         (* bindings *)
         (RDI: s R_RDI = arr)
         (RSI: s R_RSI = size)
         (SIZE: 0 <= size < 1000),
  satisfies_all
    lifted_prog
    (sum_timing_invs arr size)
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

    - destruct PRE as (RDI & RSI & (BoundL & BoundH) & Cycles).
        repeat step.
            hammer.
        exists 0. repeat split; psimpl; try lia.
        hammer.
    - destruct PRE as (i & RDI & RDX & Path & ISize & Cycles).
        repeat step. hammer.
            replace size with (i + 1) in * by lia.
            lia.
        exists (1 + i). split.
            rewrite N.mul_add_distr_l. psimpl. reflexivity.
        split. reflexivity. split. assumption. split. lia.
        hammer.
Qed.

End TimingProof.

Require Import i5_7300u.
Module i5_7300u_sum := TimingProof i5_7300u.

Goal forall (size : N) (t : trace),
    i5_7300u_sum.time_of_sum size t =
    (i5_7300u_sum.sumAuto.cycle_count_of_trace t <=
        (if size =? 0 then 38 else 50 + size * 18)).
    intros.
    unfold i5_7300u_sum.time_of_sum. simpl.
    unfold i5_7300u.ret.
    psimpl. reflexivity.
Qed.

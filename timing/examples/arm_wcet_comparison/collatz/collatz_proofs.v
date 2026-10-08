Require Import collatz.
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
        (* 0x00101162: JMP 0x00101172 *)
        | 0x2 => jmp_addr
        (* 0x00101168: ADD RAX,0x1 *)
        | 0x8 => add_r64_i
        (* 0x0010116b: CMP $AX,0xd6d8 *)
        | 0xc => cmp_r64_i
        (* 0x00101170: JZ 0x00101190 *)
        | 0x12 => jz_addr
        (* 0x00101172: TEST DIL,0x1 *)
        | 0x14 => test_r8_i
        (* 0x00101176: JZ 0x00101186 *)
        | 0x18 => jz_addr
        (* 0x00101178: ADD $AX,0x1 *)
        | 0x1a => add_r64_i
        (* 0x0010117b: LEA EDI,[RDI + RDI*0x2 + 0x1] *)
        | 0x1e => lea_r64_addr
        (* 0x0010117f: CMP RAX,0xd6d8 *)
        | 0x22 => cmp_r64_i
        (* 0x00101184: JZ 0x00101191 *)
        | 0x28 => jz_addr
        (* 0x00101186: SHR DI,0x1 *)
        | 0x2a => shr_r16_i
        (* 0x00101189: CMP DI,0x1 *)
        | 0x2d => cmp_r16_i
        (* 0x0010118d: JNZ 0x00101168 *)
        | 0x31 => jnz_addr
        (* 0x0010118f: RET *)
        | 0x33 => ret
        (* 0x00101190: RET *)
        | 0x34 => ret
        (* 0x00101191: RET *)
        | 0x35 => ret
        | _ => time_inf
        end.

    Definition lifted_prog := collatz_collatz_amd64.
End Program_collatz.

Module AMD64Timing := AMD64Timing cpu Program_collatz.
Module collatzAuto := AMD64TimingAutomation AMD64Timing.
Import Program_collatz collatzAuto.

Definition time_of_collatz (t : trace) :=
  (* Total cycle count constraint *)
  cycle_count_of_trace t <=
    (* setup *)
    xor_r32_r32 + jmp_addr +

    (* increment and overflow check *)
      add_r64_i + cmp_r64_i + jz_addr +

      (* test if n is odd *)
      test_r8_i + jz_addr +

      (* odd branch: add, lea, cmp, jz *)
      (add_r64_i + lea_r64_addr + cmp_r64_i + jz_addr) +

      (* even branch: shr, cmp, jnz *)
      (shr_r16_i + cmp_r16_i + jnz_addr) +

    (* each iteration up to iters steps *)
    55000 * (
      (* increment and overflow check *)
      add_r64_i + cmp_r64_i + jz_addr +

      (* test if n is odd *)
      test_r8_i + jz_addr +

      (* odd branch: add, lea, cmp, jz *)
      (add_r64_i + lea_r64_addr + cmp_r64_i + jz_addr) +

      (* even branch: shr, cmp, jnz *)
      (shr_r16_i + cmp_r16_i + jnz_addr)
    ) +

    (* final return *)
    ret.

Definition collatz_timing_invs (n : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x0 => Some (
    s R_RDI = n /\ 1 <= n < 65536 /\
    cycle_count_of_trace t' = 0
  )
| 0x8 => Some (
    1 <= n < 65536 /\
    0 <= s R_RAX < 55000 /\
    cycle_count_of_trace t' <=
        xor_r32_r32 + jmp_addr +

        (* increment and overflow check *)
            add_r64_i + cmp_r64_i + jz_addr +

            (* test if n is odd *)
            test_r8_i + jz_addr +

            (* odd branch: add, lea, cmp, jz *)
            (add_r64_i + lea_r64_addr + cmp_r64_i + jz_addr) +

            (* even branch: shr, cmp, jnz *)
            (shr_r16_i + cmp_r16_i + jnz_addr) +

        (* each iteration up to iters steps *)
        (s R_RAX) * (
            (* increment and overflow check *)
            add_r64_i + cmp_r64_i + jz_addr +

            (* test if n is odd *)
            test_r8_i + jz_addr +

            (* odd branch: add, lea, cmp, jz *)
            (add_r64_i + lea_r64_addr + cmp_r64_i + jz_addr) +

            (* even branch: shr, cmp, jnz *)
            (shr_r16_i + cmp_r16_i + jnz_addr)
            )
  )
| 0x33 | 0x34 | 0x35 => Some (time_of_collatz t)
| _ => None end | _ => None end.

Definition f x :=
    scast 16 64 (x >> 1) mod 2 ^ 16 =? 1.

Fixpoint test x :=
    let c x := if f (N.of_nat x) then [x] else [] in
    match x with
    | O => c O
    | S x' => c x' ++ test x'
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
        repeat step. hammer.
        split. assumption.  split. split. lia.
            rewrite N.lxor_nilpotent. lia.
        hammer. hammer. hammer. split. assumption. split. split. lia.
            rewrite N.lxor_nilpotent. lia.
        hammer.
    - destruct PRE as (Bounds & RBounds & Cycles).
        repeat step.
        1,2,4,5,6: hammer.
        etransitivity.
            apply N.add_le_mono_l. apply Cycles.
            etransitivity. apply N.add_le_mono_l.
            apply N.add_le_mono_l.
            apply N.mul_le_mono_r.
            assert (s' R_RAX <= 54998). lia.
            apply H. lia.
        etransitivity.
            apply N.add_le_mono_l. apply Cycles.
            etransitivity. apply N.add_le_mono_l.
            apply N.add_le_mono_l.
            apply N.mul_le_mono_r.
            assert (s' R_RAX <= 54998). lia.
            apply H. lia.
        -- split. assumption. split. lia.
            rewrite N.mod_small by lia. lia.
        -- split. assumption. split. lia.
            hammer. rewrite N.mod_small by lia. lia.
Qed.

End TimingProof.

Require Import i5_7300u.
Module i5_7300u_collatz := TimingProof i5_7300u.

Goal forall (size : N) (t : trace),
    i5_7300u_collatz.time_of_collatz t =
    (i5_7300u_collatz.collatzAuto.cycle_count_of_trace t <= 3355098).
    intros.
    unfold i5_7300u_collatz.time_of_collatz. simpl.
    reflexivity.
Qed.

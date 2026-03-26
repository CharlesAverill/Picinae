Require Import NArith.
Require Import Picinae_armv7.
Require Import -(notations) Picinae_armv7_lifter.
Require Import ZArith.
Require Import Lia.
Open Scope N.
Import ARM7Notations.

(*
    _abort:
        eor r0, r0, r0
        add r0, r0, #1
  bx lr
        // r0 - code patch pointer
        // r1 - function-to-be-patched pointer
        // r2 - length in terms of 4-byte instructions
        // r3 - instruction to copy
        // r4 - iterator
        // r5 - scratch
 cmp r2, #64
        bgt _abort
        cmp r2, #0
        beq _abort
        // Check first instruction is nop
        ldr r4, [r1]
        movw r5, #0xf000
        movt r5, #0xe320
        cmp r4, r5
        bne _abort
        eor r4, r4, r4
        sub r1, r1, r2, LSL #2

        _loop:
    cmp r4, r2
        bge _done
      ldr r3, [r0, r4, LSL #2]
        str r3, [r1, r4, LSL #2]
        add r4, r4, #1
        b _loop

        _done:
      add r1, r1, r2, LSL #2  // r1 := initial r1
        eor r0, r0, r0      // r0 := 0
        sub r4, r0, r2     // r4 := 0 - length
      add r4, r4, #1
      movw r3, #0x0000
        movt r3, #0x1500      // get ready to clear the op-bits
        bic r4, r3        // See encoding A1 on page A8-340 of ARMv7-A and ARMv7-R reference manual
        str r4, [r1]      // write the branch-to-patch instruction as first instruction in function
      bx lr         // return with r0 = 0
 *)

Definition hot_patcher a := match a with
| 0x00 => Some (4, 0xe0200000)
| 0x04 => Some (4, 0xe2800001)
| 0x08 => Some (4, 0xe12fff1e)
| 0x0c => Some (4, 0xe3520040)
| 0x10 => Some (4, 0xcafffffa)
| 0x14 => Some (4, 0xe3520000)
| 0x18 => Some (4, 0x0afffff8)
| 0x1c => Some (4, 0xe5914000)
| 0x20 => Some (4, 0xe30f5000)
| 0x24 => Some (4, 0xe34e5320)
| 0x28 => Some (4, 0xe1540005)
| 0x2c => Some (4, 0x1afffff3)
| 0x30 => Some (4, 0xe0244004)
| 0x34 => Some (4, 0xe0411102)
| 0x38 => Some (4, 0xe1540002)
| 0x3c => Some (4, 0xaa000003)
| 0x40 => Some (4, 0xe7903104)
| 0x44 => Some (4, 0xe7813104)
| 0x48 => Some (4, 0xe2844001)
| 0x4c => Some (4, 0xeafffff9)
| 0x50 => Some (4, 0xe0811102)
| 0x54 => Some (4, 0xe3000000) (* movw r0, #0 *)
| 0x58 => Some (4, 0xe2822002) (* add r2, r2, #3 *)
| 0x5c => Some (4, 0xe0404002) (* sub r4, r0, r2 *)
| 0x60 => Some (4, 0xe3003000) (* add r4, r4, r1 *)
| 0x64 => Some (4, 0xe3413500)
| 0x68 => Some (4, 0xe1c44003)
| 0x6c => Some (4, 0xe5814000)
| 0x70 => Some (4, 0xe12fff1e)
| _ => None
end.

Theorem addr_oob:
  forall a, 0x74 <= a -> None = hot_patcher a.
Proof.
  destruct a as [|p]; repeat (lia || reflexivity || destruct p as [|p|p]).
Qed.

(* Combine Harvard and von Neumann models assuming the addresses for Harvard are all unwriteable. *)
Definition cprog s a :=
  match hot_patcher a with
  | Some (sz, q) => Some (sz, arm2il a (arm_decode (Z.of_N q)))
  | None => arm_prog s a
  end.

Theorem welltyped_cprog:
  welltyped_prog arm7typctx cprog.
Proof.
  intros s a.
  unfold cprog.
  destruct (hot_patcher _) as [[sz q]|].
  eexists; eapply welltyped_arm2il.
  eapply welltyped_arm_prog.
Qed.

Local Ltac effinv_none_hook ::=
  (*match goal with
  | |- context[?xs::?t0++]*)
  match goal with
  | H : _ -> effinv _ _ _ _ _ = None |- _ => eapply H; clear H
  end.
Local Ltac psa_some_hook ::= idtac.
Theorem big_step_50_70 :
  forall invs exits s t
  (RE: s R_E = 0)
  (I1: forall t', effinv false cprog invs exits ((Addr 0x50, s) :: t') = None)
  (I2: forall t', effinv true cprog invs exits ((Addr 0x54, s[R_PC := 80][R_R1 := s R_R1 ⊕ (s R_R2 << 2)]) :: t') = None)
  (I3: forall t', effinv true cprog invs exits ((Addr 0x58, s[R_R1 := s R_R1 ⊕ (s R_R2 << 2)][R_PC := 84] [R_R0 := 0]) :: t') = None)
  (I4: forall t', effinv true cprog invs exits ((Addr 0x5c, s[R_R1 := s R_R1 ⊕ (s R_R2 << 2)] [R_R0 := 0][R_PC := 88] [R_R4 := 1 ⊕ N.lnot (s R_R2) 32]) :: t') = None)
  (I4: forall t', effinv true cprog invs exits ((Addr 92, s[R_R1 := s R_R1 ⊕ (s R_R2 << 2)][R_R0 := 0][R_PC := 88] [R_R2 := 2 ⊕ s R_R2]) :: t') = None)
  (I5: forall t', effinv true cprog invs exits ((Addr 96, s[R_R1 := s R_R1 ⊕ (s R_R2 << 2)][R_R0 := 0][R_R2 := 2 ⊕ s R_R2][R_PC := 92][R_R4 := 1 ⊕ N.lnot (2 + s R_R2) 32]) :: t') = None)
  (I6: forall t', effinv true cprog invs exits ((Addr 100, s[R_R1 := s R_R1 ⊕ (s R_R2 << 2)][R_R0 := 0] [R_R2 := 2 ⊕ s R_R2][R_R4 := 1 ⊕ N.lnot (2 + s R_R2) 32][R_PC := 96] [R_R3 := 0]) :: t') = None)
  (I7: forall t', effinv true cprog invs exits ((Addr 104, s[R_R1 := s R_R1 ⊕ (s R_R2 << 2)][R_R0 := 0] [R_R2 := 2 ⊕ s R_R2][R_R4 := 1 ⊕ N.lnot (2 + s R_R2) 32][R_PC := 100] [R_R3 := 352321536]) :: t') = None)
  (I8: forall t', effinv true cprog invs exits ((Addr 108, s[R_R1 := s R_R1 ⊕ (s R_R2 << 2)][R_R0 := 0] [R_R2 := 2 ⊕ s R_R2][R_R3 := 352321536][R_PC := 104] [R_R4 := 1 + N.lnot (2 + s R_R2) 32 .& 3942645759]) :: t') = None)
  (NI: forall t', nextinv cprog invs exits true
    ((Addr 112, s[R_E := 0][R_R1 := s R_R1 ⊕ (s R_R2 << 2)][R_R0 := 0]
      [R_R2 := 2 ⊕ s R_R2][R_R3 := 352321536]
      [R_R4 := 1 + N.lnot (2 + s R_R2) 32 .& 3942645759][R_PC := 108]
      [V_MEM32 := s V_MEM32 [Ⓓs R_R1 + (s R_R2 << 2)
                  := 1 + N.lnot (2 + s R_R2) 32 .& 3942645759 ]])
    :: t'))
, nextinv cprog invs exits false ((Addr 80, s) :: t).
Proof.
  intros.
  Time repeat ISA_step.
  eapply NI.
Time Qed.

















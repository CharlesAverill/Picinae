(* seed48 -- reseed the 48-bit linear congruential generator

   SEMANTICS
   ---------
   seed48(seed16v) is a NON-LEAF function: it calls seed48_r(seed16v,
   &__libc_drand48_data) and returns a pointer to the old_x field of that global
   buffer.  seed48_r saves the current 48-bit state Xi into old_x, stores the
   three 16-bit words of seed16v as the new Xi, and resets the LCG parameters to
   the standard a = 0x5DEECE66D and c = 0xB (it also sets the buffer's __init
   flag).  The buffer is glibc's struct drand48_data:
     { unsigned short __x[3];      offset 0   (Xi)
       unsigned short __old_x[3];  offset 6
       unsigned short __c;         offset 12
       unsigned short __init;      offset 14
       unsigned long long __a; }   offset 16
   Both subroutines are lifted into one program (seed48_amd64.v, global
   addresses).  seed48_r is proved first (subroutine id 0), and seed48
   (id 1) uses that proof at its call site through Picinae's perform_call,
   following the pattern of ../arm8_strcasecmp_proof.v.

   SPECIFICATION (man 3 drand48, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <stdlib.h>
            unsigned short *seed48(unsigned short seed16v[3]);

     DESCRIPTION
            All the functions work by generating a sequence of 48-bit integers, Xi,
            according to the linear congruential formula:

                Xn+1 = (aXn + c) mod m, where n >= 0

            The  parameter  m = 2^48, hence 48-bit integer arithmetic is performed.
            Unless lcong48() is called, a and c are given by:

                a = 0x5DEECE66D
                c = 0xB

            The initializer function seed48() sets the value of Xi  to  the  48-bit
            value  specified  in the array argument seed16v.  The previous value of
            Xi is copied into an internal buffer and a pointer to  this  buffer  is
            returned by seed48().
            [...]
            After lcong48() has been called, a subsequent call  to  either  srand48()
            or seed48() will restore the standard values of a and c.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol seed48 at 0x1469c0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see seed48_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = seed16v; m = memory on entry; RSP = sp (pointing at the
            caller's return address).  D = 0x31c750 is the address of
            __libc_drand48_data.  As with other rip-relative references, Ghidra
            resolved it for libc loaded at its image base 0x100000.
   Precondition:  the 24-byte buffer D does not overlap the stack slot
            [sp-16, sp-8) where seed48's call pushes its return address
            (seed48 first moves RSP down by 8 to align the stack).
   Output:  On return, RAX = D + 6 (the old_x buffer), RSP = sp, and memory is
            exactly seed48r_mem (m[sp-16 := return address]) seed16v D: the pushed
            return address stays in the dead stack slot, and the seed48_r
            updates are applied on top.
   Frame:   No callee-saved register (RBX, RBP, R12-R15) is modified by either
            subroutine.
 *)

Require Import Picinae_amd64.
Require Import seed48_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem seed48_nwc: forall s2 s1, seed48_amd64 s1 = seed48_amd64 s2.
Proof. reflexivity. Qed.

Theorem seed48_welltyped: welltyped_prog x64typctx seed48_amd64.
Proof. Picinae_typecheck. Qed.

Theorem seed48_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates seed48_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition D := 0x31c750.

(* The exact effect of seed48_r(s, b) on memory, following its store order. *)
Definition seed48r_mem (m:memory) (s b:N) :=
  let m1 := m [Ⓓ b ⊕ 6 := m Ⓓ[b]] in
  let m2 := m1 [Ⓦ b ⊕ 10 := m Ⓦ[b ⊕ 4]] in
  let m3 := m2 [Ⓦ b ⊕ 4 := m2 Ⓦ[s ⊕ 4]] in
  let m4 := m3 [Ⓦ b ⊕ 2 := m3 Ⓦ[s ⊕ 2]] in
  let x0 := m4 Ⓦ[s] in
  m4 [Ⓓ b ⊕ 12 := 0x1000b] [Ⓦ b := x0] [Ⓠ b ⊕ 16 := 0x5deece66d].

Section Invariants.
  Variable sp : N.
  Variable mem : memory.
  Variable seed buf : N.

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* seed48 entry and return *)
    | 1337792 => Inv 1 (s R_RSP = sp /\ s V_MEM64 = mem /\ s R_RDI = seed)
    | 1337823 => Post 1 (s R_RAX = D ⊕ 6 /\ s R_RSP = sp /\
                         s V_MEM64 = seed48r_mem (mem [Ⓠ sp ⊖ 16 := 1337812]) seed D)
    (* seed48_r entry and return *)
    | 1338224 => Inv 0 (s R_RSP = sp /\ s V_MEM64 = mem /\ s R_RDI = seed /\ s R_RSI = buf)
    | 1338286 => Post 0 (s R_RAX = 0 /\ s R_RSP = sp /\ s V_MEM64 = seed48r_mem mem seed buf)
    | _ => NoInv
    end.

  Definition exits0 := make_exits 0 seed48_amd64 invs.
  Definition invs0 := make_invs 0 seed48_amd64 invs.
  Definition exits1 := make_exits 1 seed48_amd64 invs.
  Definition invs1 := make_invs 1 seed48_amd64 invs.
End Invariants.

(* seed48_r: straight-line stores into the buffer. *)
Theorem seed48_r_correct:
  forall s t xs' sp mem seed buf
         (ENTRY: startof t xs' = (Addr 1338224, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem) (RDI: s R_RDI = seed) (RSI: s R_RSI = buf),
  satisfies_all seed48_amd64 (invs0 sp mem seed buf) (exits0 sp mem seed buf) (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply seed48_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [SP [MEM [RDI RSI]]].
  repeat x64_step.
  split; [reflexivity|]. split; [assumption|].
  unfold seed48r_mem. cbv zeta.
  rewrite !setmem_mod_l, !getmem_mod_l, !(N.add_comm buf), !(N.add_comm seed).
  reflexivity.
Qed.

(* seed48_r only writes inside the 24-byte buffer. *)
Lemma seed48r_frame:
  forall m s b a, ~ overlap 64 b 24 a 8 -> (seed48r_mem m s b) Ⓠ[a] = m Ⓠ[a].
Proof.
  intros m s b a NO. unfold seed48r_mem. cbv zeta.
  repeat rewrite getmem_noverlap by
    (apply noverlap_sym; first [ apply (noverlap_sub _ 24); [exact NO|lia]
                               | apply (noverlap_sub0 _ 24); [exact NO|lia] ]).
  reflexivity.
Qed.

(* seed48: calls seed48_r(seed16v, D) and returns D+6. *)
Theorem seed48_correct:
  forall s t xs' sp mem seed
         (ENTRY: startof t xs' = (Addr 1337792, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem) (RDI: s R_RDI = seed)
         (NO: ~ overlap 64 D 24 (sp ⊖ 16) 8),
  satisfies_all seed48_amd64 (invs1 sp mem seed D) (exits1 sp mem seed D) (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply seed48_welltyped. intro MDL1.
  clear - PRE MDL1 NO. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.

  (* seed48 entry *)
  destruct PRE as [SP [MEM RDI]].
  assert (SPL: sp < 2^64) by (rewrite <- SP; apply (MDL R_RSP 64), eq_refl).
  x64_step. x64_step. x64_step. x64_step.
  (* call seed48_r *)
  set (s1 := update _ _ _).
  eapply models_after_steps. eassumption. apply seed48_welltyped. intro MDL1.
  eapply (perform_call 0). reflexivity.
  intros. eapply seed48_r_correct; (eassumption || reflexivity).
  reflexivity.
  intros. unfold s1 in PRE. psimpl in PRE.
  destruct_inv 64 PRE.
  destruct PRE as [RAX [RSP' MEM']].
  assert (MDL': models x64typctx s').
    eapply preservation_exec_prog; try eassumption. apply seed48_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s1 t'.
  clear - MEM' RSP' MDL' NO SPL.
  x64_step.
  rewrite seed48r_frame, getmem_setmem by (exact NO || discriminate).
  change (1337812 mod 2^(8*8)) with 1337812.
  repeat x64_step.
  repeat split; first [ reflexivity | apply N.mod_small; exact SPL ].
Qed.



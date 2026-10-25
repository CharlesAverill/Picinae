(* srand48_r -- seed the reentrant 48-bit linear congruential generator

   SEMANTICS
   ---------
   srand48_r(seedval, buffer) initializes struct drand48_data
   (unsigned short __x[3] at 0; __old_x[3] at 6; __c at 12; __init at 14;
   unsigned long long __a at 16).  It sets Xi to seedval * 2^16 + 0x330E
   (as a 2-byte store of 0x330E and a 4-byte store of seedval), a to
   0x5DEECE66D, and c = 0xB, init = 1 (one 4-byte store of 0x1000B), then
   returns 0.  __old_x is not written.

   SPECIFICATION (man 3 drand48, Linux man-pages 5.10, Ubuntu 22.04)
   ------------------------------------------------------------------

     int srand48_r(long int seedval, struct drand48_data *buffer);

     The initializer function srand48() sets the high order 32-bits of Xi to
     the argument seedval.  The low order 16-bits are set to the arbitrary
     value 0x330E.
     ...
     Unless lcong48() is called, a and c are given by:
         a = 0x5DEECE66D
         c = 0xB

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol srand48_r at 0x146b40 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see srand48_r_amd64.v (offsets relative to
            the entry).
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = seedval, RSI = buffer, memory m.
   Output:  RAX = 0, RSP unchanged, and memory is m after exactly these
            stores: [buffer+2, 4 bytes] := seedval, [buffer, 2] := 0x330E,
            [buffer+16, 8] := 0x5DEECE66D, [buffer+12, 4] := 0x1000B.
            srand48_r_fields: afterwards Xi (6 bytes at buffer) =
            (seedval mod 2^32) * 2^16 + 0x330E, a = 0x5DEECE66D, c = 0xB,
            and the 4-byte word at buffer+12 is 0x1000B (c = 0xB, init = 1).
 *)

Require Import Picinae_amd64.
Require Import srand48_r_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem srand48_r_nwc: forall s2 s1, srand48_r_amd64 s1 = srand48_r_amd64 s2.
Proof. reflexivity. Qed.

Theorem srand48_r_welltyped: welltyped_prog x64typctx srand48_r_amd64.
Proof. Picinae_typecheck. Qed.

Theorem srand48_r_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates srand48_r_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition srand48_r_mem (m:memory) (seed b:N) :=
  m [Ⓓ 2 + b := seed] [Ⓦ b := 0x330e] [Ⓠ 16 + b := 0x5deece66d] [Ⓓ 12 + b := 0x1000b].

Definition srand48_r_exit (t:trace) := match t with (Addr 38,_)::_ => true | _ => false end.

Definition srand48_r_invs (m:memory) (seed b rsp:N) (t:trace) :=
  match t with (Addr x,s)::_ => match x with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = seed /\ s R_RSI = b /\ s R_RSP = rsp)
  | 38 => Some (s R_RAX = 0 /\ s R_RSP = rsp /\ s V_MEM64 = srand48_r_mem m seed b)
  | _ => None end | _ => None end.

Theorem srand48_r_correct:
  forall s t s' x' m seed b rsp
         (ENTRY: startof t (x',s') = (Addr 0,s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (A: s R_RDI = seed) (B: s R_RSI = b) (RSP: s R_RSP = rsp),
  satisfies_all srand48_r_amd64 (srand48_r_invs m seed b rsp) srand48_r_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply srand48_r_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [A [B RSP]]].
  repeat x64_step.
  repeat split; first [reflexivity | assumption].
Qed.

Ltac off_nov := intros [i [j [I [J E]]]]; unfold msub in *;
  change (2^64) with 18446744073709551616 in *; lia.

(* The struct fields after srand48_r: Xi (6 bytes), a, and the 4-byte word
   holding c (low half) and init (high half). *)
Theorem srand48_r_fields:
  forall (m:memory) seed b, let M := srand48_r_mem m seed b in
  getmem 64 LittleE 6 M b = (seed mod 2^32) * 2^16 + 0x330e /\
  M Ⓠ[16 + b] = 0x5deece66d /\ M Ⓦ[12 + b] = 0xb /\ M Ⓓ[12 + b] = 0x1000b.
Proof.
  intros m seed b M. unfold M, srand48_r_mem. split; [|split; [|split]].
  - rewrite getmem_noverlap by off_nov. rewrite getmem_noverlap by off_nov.
    change 6 with (2 + 4). rewrite getmem_split. unfold cbits.
    rewrite getmem_setmem by discriminate. rewrite getmem_noverlap by off_nov.
    rewrite (N.add_comm b 2), getmem_setmem by discriminate.
    change (4*8) with 32. change (2*8) with 16. rewrite (N.mod_small 13070) by (change (2^16) with 65536; lia).
    rewrite lor_plus. rewrite N.shiftl_mul_pow2. reflexivity.
    apply N.bits_inj. intro i. rewrite N.land_spec, N.bits_0.
    destruct (N.ltb_spec i 16).
    + rewrite N.shiftl_spec_low by lia. reflexivity.
    + replace (N.testbit 13070 i) with false. apply Bool.andb_false_r.
      symmetry. apply N.bits_above_log2. change (N.log2 13070) with 13. lia.
  - rewrite getmem_noverlap by off_nov. rewrite getmem_setmem by discriminate. reflexivity.
  - match goal with |- getmem 64 LittleE 2 ?X ?a = _ =>
      replace (getmem 64 LittleE 2 X a) with ((getmem 64 LittleE 4 X a) mod 2^(2*8)) by (rewrite getmem_mod; reflexivity) end.
    rewrite getmem_setmem by discriminate. reflexivity.
  - rewrite getmem_setmem by discriminate. reflexivity.
Qed.

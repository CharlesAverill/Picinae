(* lcong48_r -- set the state and parameters of the reentrant 48-bit LCG

   SEMANTICS
   ---------
   lcong48_r(param, buffer) copies param[0..2] into Xi (__x, 6 bytes at
   buffer), sets a = param[3] + param[4]*2^16 + param[5]*2^32 (__a at
   buffer+16), c = param[6] (__c at buffer+12), sets __init = 1 (buffer+14),
   and returns 0.  param is an array of seven unsigned shorts.  glibc
   interleaves loads from param with stores to buffer, so the theorem
   assumes the two do not overlap.

   SPECIFICATION (man 3 drand48, Linux man-pages 5.10, Ubuntu 22.04)
   ------------------------------------------------------------------

     int lcong48_r(unsigned short param[7], struct drand48_data *buffer);

     The initialization function lcong48() allows the user to specify
     initial values for Xi, a, and c.  Array argument elements param[0-2]
     specify Xi, param[3-5] specify a, and param[6] specifies c.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol lcong48_r at 0x146bb0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see lcong48_r_amd64.v (offsets relative
            to the entry).
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = param, RSI = buffer, memory m; param[0..14) and
            buffer[0..24) do not overlap (as bytes mod 2^64).
   Output:  RAX = 0, RSP unchanged, and memory is m after exactly these
            stores, all of values read from m:
              [buffer, 4]    := param[0..4)
              [buffer+4, 2]  := param[2]
              [buffer+16, 8] := param[5] << 32 | param[3] | param[4] << 16
              [buffer+12, 2] := param[6]
              [buffer+14, 2] := 1
 *)

Require Import Picinae_amd64.
Require Import lcong48_r_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem lcong48_r_nwc: forall s2 s1, lcong48_r_amd64 s1 = lcong48_r_amd64 s2.
Proof. reflexivity. Qed.

Theorem lcong48_r_welltyped: welltyped_prog x64typctx lcong48_r_amd64.
Proof. Picinae_typecheck. Qed.

Theorem lcong48_r_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates lcong48_r_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.


Definition lcong48_r_mem (m:memory) (p b:N) :=
  m [Ⓓ b := m Ⓓ[p]] [Ⓦ 4 + b := m Ⓦ[4 + p]]
    [Ⓠ 16 + b := m Ⓦ[10 + p] << 32 .| m Ⓦ[6 + p] .| m Ⓦ[8 + p] << 16]
    [Ⓦ 12 + b := m Ⓦ[12 + p]] [Ⓦ 14 + b := 1].

Definition lcong48_r_exit (t:trace) := match t with (Addr 64,_)::_ => true | _ => false end.

Definition lcong48_r_invs (m:memory) (p b rsp:N) (t:trace) :=
  match t with (Addr x,s)::_ => match x with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = b /\ s R_RSP = rsp)
  | 64 => Some (s R_RAX = 0 /\ s R_RSP = rsp /\ s V_MEM64 = lcong48_r_mem m p b)
  | _ => None end | _ => None end.

(* A read of param at offset c1 (+i) never hits a store to buffer at offset c2 (+j). *)
Lemma lc_nov:
  forall p b c1 c2 i j, (forall x y, x < 14 -> y < 24 -> (p + x) mod 2^64 <> (b + y) mod 2^64) ->
  c1 + i < 14 -> c2 + j < 24 -> (c1 + p + i) mod 2^64 <> (c2 + b + j) mod 2^64.
Proof.
  intros p b c1 c2 i j NOV I J. replace (c1 + p + i) with (p + (c1 + i)) by lia.
  replace (c2 + b + j) with (b + (c2 + j)) by lia. apply NOV; assumption.
Qed.

Ltac lc_tac NOV :=
  intros [i [j [I [J E]]]];
  repeat match type of E with context [(?p + i) mod _] =>
    match p with _ + _ => fail 1 | _ => replace (p + i) with (0 + p + i) in E by lia end end;
  repeat match type of E with context [(?b + j) mod _] =>
    match b with _ + _ => fail 1 | _ => replace (b + j) with (0 + b + j) in E by lia end end;
  revert E; apply lc_nov; [exact NOV | lia | lia].

Theorem lcong48_r_correct:
  forall s t s' x' m p b rsp
         (ENTRY: startof t (x',s') = (Addr 0,s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (A: s R_RDI = p) (B: s R_RSI = b) (RSP: s R_RSP = rsp)
         (NOV: forall x y, x < 14 -> y < 24 -> (p + x) mod 2^64 <> (b + y) mod 2^64),
  satisfies_all lcong48_r_amd64 (lcong48_r_invs m p b rsp) lcong48_r_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply lcong48_r_welltyped. intro MDL1.
  clear - PRE MDL1 NOV. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [A [B RSP]]].
  repeat x64_step.
  split; [reflexivity|]. split; [assumption|].
  unfold lcong48_r_mem.
  repeat rewrite (getmem_noverlap _ _ _ _ _ _ _ _ _) by lc_tac NOV.
  reflexivity.
Qed.

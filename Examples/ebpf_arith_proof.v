(* Test ebpf proof

   Copyright (c) 2023 Kevin W. Hamlen
   Computer Science Department
   The University of Texas at Dallas

   Any use, commercial or otherwise, requires the express permission of
   the author.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_ebpf_pcode.
Require Import ebpf_arith.

Import EBPFNotations.
Open Scope N.

(* Example #1: Type safety
   We first prove that the program is well-typed (automated by the Picinae_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem arith_welltyped: welltyped_prog ebpftypctx arith_bpf.
Proof.
  Picinae_typecheck.
Qed.

Definition arith_exit (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 88 => true
  | _ => false
  end | _ => false end.

Definition r10_invs (r10:N) (t:trace) :=
  match t with (Addr _,s)::_ =>
    Some (s R_R10 = Ⓠ r10)
  | _ => None end.

Theorem arith_test_step:
  forall s r10 t s' x'
         (ENTRY: startof t (x',s') = (Addr 0, s))
         (MDL: models ebpftypctx s)
         (R10: s R_R10 = Ⓠ r10),
  satisfies_all arith_bpf (r10_invs r10) arith_exit ((x',s')::t).
Proof.
  intros.
  apply prove_invs.
  simpl. rewrite ENTRY. ebpf_step. exact R10.

  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply arith_welltyped).
  clear - PRE MDL. rename t1 into t. rename s1 into s.

  destruct_inv 32 PRE.

  all: ebpf_step.

  all: solve [ reflexivity | assumption ].
Qed.

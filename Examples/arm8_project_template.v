(* Proofs using Picinae for ARM8 Architecture

   Picinae System:
     Copyright (c) 2024 Kevin W. Hamlen
     Computer Science Department
     The University of Texas at Dallas

   These proofs written by:

   Any use, commercial or otherwise, requires the express permission of
   the author.

   To run this module, first load and compile:
   * Picinae_core
   * Picinae_theory
   * Picinae_finterp
   * Picinae_statics
   * Picinae_armv8_pcode
   * program_arm8
   (in that order) and then compile this module using menu option
   Compile->Compile buffer.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8_pcode.
Require Import Lia.
Require Import Bool.

Require Import Picinae_numbers.
Import ARM8Notations.
Open Scope N.

(** 1: replace `program_definition` with the name of the file that defines
   the program. *)
Require Import program_definition.

(* 2: Define post-condition points: *)
Definition program_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | ??? => true
  | _ => false
  end | _ => false end.

(** 3: Verify that the lifted IL is type-safe. Replace program_name with the
    name of the program as it is defined in the program_definition file. *)
Theorem program_welltyped: welltyped_prog arm8typctx program_name.
Proof.
  Picinae_typecheck.
Qed.



(** 4: Define the invariants. *)
Section Invariants.

  (** Example invariant function set up. *)
  Definition program_invs (t:trace) := match t with (Addr a,s)::_ => match a with
  (* 0x00100000: Entry Invariant *)
  |  0x00100000 => Some ( _ )

  |  0x0010001c => Some ( _ )

  |  0x00100054 => Some( _ )

  |  0x0010002c =>  Some( _ )

  |  0x00100094 => Some( _ )

  |  0x00100078 => Some( _ )

  |  0x00100068 => Some( _ )
  | _ => None
  end | _ => None end.
End Invariants.

(** * * * * * * * *         ~~ ~~~~~~~~ ~~        * * * * * * * * * *)
(** 5: begin the proof *)
Theorem program_partial_correctness:
  ∀ s m x' s' t
         (ENTRY: startof t (x',s') = (Addr 0x00100000,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM64 = m)
,
  satisfies_all program2 (program_invs m) program_exit ((x',s')::t).
Proof.
Local Ltac step := time arm8_step.
intros.

Qed.

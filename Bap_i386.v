(* Instantiation of CoqBAP for Intel x86 Architecture
 *
 * Copyright (c) 2018 Kevin W. Hamlen
 * Computer Science Department
 * The University of Texas at Dallas
 *
 * Any use, commercial or otherwise, requires the express permission of
 * the author.
 *
 * To run this module, first load the BapSyntax, BapInterp, and BapStatics
 * modules, and compile them (in that order) using menu option Compile->
 * Compile buffer.
 *)

Require Import BapStatics.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.

(* Instantiation of BAP for the x86 architectures *)

(* Variables found in IL code lifted from x86 native code: *)
Inductive x86var :=
  (* Main memory: MemT 32 *)
  | V_MEM32
  (* Flags (1-bit registers): *)
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF (* NumT 1 *)
  (* Segment selectors (16-bit registers): *)
  | R_CS | R_DS | R_ES | R_FS | R_GS | R_SS (* NumT 16 *)
  (* Floating point control register (16-bit): *)
  | R_FPU_CTRL (* NumT 16 *)
  (* Floating point registers (80-bit): *)
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7 (* NumT 80 *)
  (* General-purpose registers (32-bit): *)
  | R_EAX | R_EBX | R_ECX | R_EDX | R_EDI | R_ESI (* NumT 32 *)
  (* Stack pointer and base pointer (32-bit): *)
  | R_ESP | R_EBP (* NumT 32 *)
  (* Modifiable segment base registers (32-bit): *)
  | R_FSBASE | R_GSBASE (* NumT 32 *)
  (* Descriptor table registers (32-bit): *)
  | R_LDTR | R_GDTR (* NumT 32 *)
  (* SSE control register (32-bit): *)
  | R_MXCSR (* NumT 32 *)
  (* MMX and SSE registers (256-bit): *)
  | R_YMM0 | R_YMM1 | R_YMM2  | R_YMM3  | R_YMM4  | R_YMM5  | R_YMM6  | R_YMM7
  | R_YMM8 | R_YMM9 | R_YMM10 | R_YMM11 | R_YMM12 | R_YMM13 | R_YMM14 | R_YMM15
  (* Temporaries introduced by the BIL lifter: *)
  | V_TEMP (n:N).

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the BapInterp module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniX86VarEq <: MiniDecidableType.
  Definition t := x86var.
  Definition eq_dec (v1 v2:x86var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Qed.
End MiniX86VarEq.

Module X86Arch <: Architecture.
  Module Var := Make_UDT MiniX86VarEq.
  Definition Mb := 8%N.
  Theorem Mb_nonzero: Mb <> 0%N.
  Proof. discriminate 1. Qed.
End X86Arch.

(* Instantiate the BAP semantics modules with the x86 identifiers above. *)

Module BAPx86 := BAPStatics X86Arch.
Import BAPx86.

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition x86typctx (id:varid) : option typ :=
  match id with
  | V_MEM32 => Some (MemT 32)
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF => Some (NumT 1)
  | R_CS | R_DS | R_ES | R_FS | R_GS | R_SS => Some (NumT 16)
  | R_FPU_CTRL => Some (NumT 16)
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7 => Some (NumT 80)
  | R_EAX | R_EBX | R_ECX | R_EDX | R_EDI | R_ESI => Some (NumT 32)
  | R_ESP | R_EBP => Some (NumT 32)
  | R_FSBASE | R_GSBASE => Some (NumT 32)
  | R_LDTR | R_GDTR => Some (NumT 32)
  | R_MXCSR => Some (NumT 32)
  | R_YMM0 | R_YMM1 | R_YMM2  | R_YMM3  | R_YMM4  | R_YMM5  | R_YMM6  | R_YMM7
  | R_YMM8 | R_YMM9 | R_YMM10 | R_YMM11 | R_YMM12 | R_YMM13 | R_YMM14 | R_YMM15 => Some (NumT 256)
  | V_TEMP _ => None
  end.

Definition x86_wtm {s v mem mw} := @models_wtm x86typctx s v mem mw.
Definition x86_regsize {s v u w} := @models_regsize x86typctx s v u w.


Module X86Notations.

Notation "Ⓜ m" := (Some (VaM m 32)) (at level 20).
Notation "ⓑ u" := (Some (VaN (u,1))) (at level 20).
Notation "Ⓑ u" := (Some (VaN (u,8))) (at level 20).
Notation "Ⓦ u" := (Some (VaN (u,16))) (at level 20).
Notation "Ⓓ u" := (Some (VaN (u,32))) (at level 20).
Notation "Ⓠ u" := (Some (VaN (u,64))) (at level 20).
Notation "Ⓧ u" := (Some (VaN (u,128))) (at level 20).
Notation "Ⓨ u" := (Some (VaN (u,256))) (at level 20).
Notation "m [ a : w ]" := (getmem LittleE w m a) (at level 10).
Notation "m [ a : w := v ]" := (setmem LittleE w m a v) (at level 10).
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity).
Notation "x ⊖ y" := ((x-y) mod 2^32) (at level 50, left associativity).
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity).
Notation "x << y" := (N.shiftl x y) (at level 40, left associativity).
Notation "x >> y" := (N.shiftr x y) (at level 40, left associativity).
Notation "x >>> y" := (ashiftr 32 x y) (at level 40, left associativity).
Notation "x .& y" := (N.land x y) (at level 55, left associativity).
Notation "x .| y" := (N.lor x y) (at level 55, left associativity).
Notation "x .^ y" := (N.lxor x y) (at level 55, left associativity).

End X86Notations.

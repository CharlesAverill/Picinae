(* Companion AMD64 state for the exact Ubuntu glibc wide-vector campaign.
   e15: representation only. Existing Picinae_amd64 and its theorems are
   unchanged; there is no semantic transfer theorem between the two ISAs.
   See notes/e15-x86-vector-state/README.md for provenance and e17 boundaries.
   Scalar declarations and functor setup adapted from Picinae_amd64.v,
   pinned origin 49956416928e5b6bb3928b54ae33e3b81091f006. *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_auto.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Export Picinae_ISA.
From Stdlib Require Import NArith.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Structures.Equalities.
Open Scope N.

Module AMD64_AVX512.

(* Canonical physical vector and opmask slots; no independently stored aliases. *)
Inductive vector_slot :=
  | Z0 | Z1 | Z2 | Z3 | Z4 | Z5 | Z6 | Z7
  | Z8 | Z9 | Z10 | Z11 | Z12 | Z13 | Z14 | Z15
  | Z16 | Z17 | Z18 | Z19 | Z20 | Z21 | Z22 | Z23
  | Z24 | Z25 | Z26 | Z27 | Z28 | Z29 | Z30 | Z31.
Inductive mask_slot := K0 | K1 | K2 | K3 | K4 | K5 | K6 | K7.

(* Scalar slots mirror the old architecture; these are separate IL types. *)
Inductive avx512var :=
  (* Main memory: *)
  | V_MEM64
  (* Instruction Pointer Register, read and written by Ghidra, but does not
     represent the location of the current instruction.  We model it to
     reduce our TCB in that we don't handle its translation specially in
     the lifter. *)
  | R_RIP
  (* Flags (1-bit registers): *)
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF
  (* Segment selectors (16-bit registers): *)
  | R_CS | R_DS | R_ES | R_FS | R_GS | R_SS
  (* Floating point control register (16-bit): *)
  | R_FPU_CONTROL
  (* Floating point registers (80-bit): *)
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7
  (* General-purpose registers (64-bit): *)
  | R_RAX | R_RBX | R_RCX | R_RDX | R_RDI | R_RSI
  (* Stack pointer and base pointer (64-bit): *)
  | R_RSP | R_RBP
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12 | R_R13 | R_R14 | R_R15
  (* Modifiable segment base registers (64-bit): *)
  | R_FS_BASE | R_GS_BASE
  (* Descriptor table registers (64-bit): *)
  | R_LDTR | R_GDTR
  (* SSE control register (64-bit): *)
  | R_MXCSR
  | R_ZMM (r:vector_slot)
  | R_K (r:mask_slot)
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE
  (* Temporaries introduced by the lifter: *)
  | V_TEMP (n:N).

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition avx512typctx v :=
  match v with
  | V_MEM64 => Some (8*2^64)
  | R_RIP => Some 64
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF => Some 1
  | R_CS | R_DS | R_ES | R_FS | R_GS | R_SS => Some 16
  | R_FPU_CONTROL => Some 16
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7 => Some 80
  | R_RAX | R_RBX | R_RCX | R_RDX | R_RDI | R_RSI => Some 64
  | R_RSP | R_RBP => Some 64
  | R_R8 | R_R9 | R_R10 | R_R11 | R_R12 | R_R13 | R_R14 | R_R15 => Some 64
  | R_FS_BASE | R_GS_BASE => Some 64
  | R_LDTR | R_GDTR => Some 64
  | R_MXCSR => Some 64
  | R_ZMM _ => Some 512
  | R_K _ => Some 64
  | A_READ | A_WRITE => Some (2^64)
  | V_TEMP _ => None
  end.

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniAVX512VarEq <: MiniDecidableType.
  Definition t := avx512var.
  Definition eq_dec (v1 v2:avx512var) : {v1=v2}+{v1<>v2}.
    decide equality; try apply N.eq_dec; decide equality.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniAVX512VarEq.

Module AVX512Arch <: Architecture.
  Module Var := Make_UDT MiniAVX512VarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := avx512typctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End AVX512Arch.

(* Instantiate the Picinae modules with the x64 identifiers above. *)
Module IL_amd64_avx512 := PicinaeIL AVX512Arch.
Export IL_amd64_avx512.
Module Theory_amd64_avx512 := PicinaeTheory IL_amd64_avx512.
Export Theory_amd64_avx512.
Module Statics_amd64_avx512 := PicinaeStatics IL_amd64_avx512 Theory_amd64_avx512.
Export Statics_amd64_avx512.
Module Auto_amd64_avx512 := PicinaeAuto IL_amd64_avx512 Theory_amd64_avx512 Statics_amd64_avx512.
Export Auto_amd64_avx512.
Module FInterp_amd64_avx512 := PicinaeFInterp IL_amd64_avx512 Theory_amd64_avx512 Statics_amd64_avx512.
Export FInterp_amd64_avx512.
Module PSimpl_amd64_avx512 := Picinae_Simplifier_Base IL_amd64_avx512.
Export PSimpl_amd64_avx512.
Module PSimpl_amd64_avx512_v1_1 := Picinae_Simplifier_v1_1 IL_amd64_avx512 Theory_amd64_avx512 Statics_amd64_avx512 FInterp_amd64_avx512.
Ltac PSimplifier ::= PSimpl_amd64_avx512_v1_1.PSimplifier.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_amd64_avx512_v1_0 := Picinae_Simplifier_v1_0 IL_amd64_avx512 Theory_amd64_avx512 Statics_amd64_avx512 FInterp_amd64_avx512.
Ltac PSimplifier ::= PSimpl_amd64_avx512_v1_0.PSimplifier.
*)

Module ISA_amd64_avx512 := Picinae_ISA IL_amd64_avx512 PSimpl_amd64_avx512 Theory_amd64_avx512 Statics_amd64_avx512 FInterp_amd64_avx512.
Export ISA_amd64_avx512.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "avx512_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "avx512_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "avx512_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "avx512_psimpl" := psimpl_goal.
Ltac avx512_step := ISA_step.

(* Views are expressions over one 512-bit cell. The width of rhs must match
   the selected view; Concat deliberately lets the typechecker reject a bad
   width instead of silently truncating it. These are register-update builders,
   not an instruction decoder or a claim about all legacy/VEX/EVEX instructions. *)
Inductive vector_width := W128 | W256 | W512.
Definition vector_bits w : N :=
  match w with W128 => 128 | W256 => 256 | W512 => 512 end.
Definition vector_read w r : exp :=
  Extract (N.pred (vector_bits w)) 0 (Var (R_ZMM r)).
Definition vector_zero_upper w rhs : exp :=
  match w with
  | W128 => Concat (Word 0 384) rhs
  | W256 => Concat (Word 0 256) rhs
  | W512 => rhs
  end.
Definition vector_write_zero_upper w r rhs : stmt :=
  Move (R_ZMM r) (vector_zero_upper w rhs).
Definition xmm_write_preserve r rhs : stmt :=
  Move (R_ZMM r) (Concat (Extract 511 128 (Var (R_ZMM r))) rhs).

(* K0 is a real data register. EVEX.aaa=0 denotes NO writemask, not K0 data.
   Keep that encoding distinction in metadata; a lowerer must reject illegal
   zeroing/store forms and mask/element shapes before building IL. *)
Definition evex_writemask r : option mask_slot :=
  match r with K0 => None | _ => Some r end.
Inductive mask_width := M8 | M16 | M32 | M64.
Definition mask_bits w : N :=
  match w with M8 => 8 | M16 => 16 | M32 => 32 | M64 => 64 end.
Definition mask_read w r : exp :=
  Extract (N.pred (mask_bits w)) 0 (Var (R_K r)).
Definition mask_write_zero_upper w r rhs : stmt :=
  Move (R_K r)
    (match w with M8 => Concat (Word 0 56) rhs
                | M16 => Concat (Word 0 48) rhs
                | M32 => Concat (Word 0 32) rhs
                | M64 => rhs end).

End AMD64_AVX512.

(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2024 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Instantiation of Picinae for Intel x86 ISA.         MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   * Picinae_statics                                        MMMMMMMMMMM7..ZNOOMZ
   * Picinae_finterp                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_simplifier_*                                     MDMMMMMMMO.7MDM7M+
   * Picinae_ISA                                               ZMMMMMMMM.$MM8$MN
   Then compile this module with menu option                   $ZMMMMMMZ..MMMOMZ
   Compile->Compile_buffer.                                     ?MMMMMM7..MNN7$M
                                                                 ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Export Picinae_core.
Require Export Picinae_theory.
Require Export Picinae_statics.
Require Export Picinae_finterp.
Require Export Picinae_simplifier_v1_1.
Require Export Picinae_ISA.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from x86 native code: *)
Inductive x86var :=
  (* Main memory: *)
  | V_MEM32
  (* Flags (1-bit registers): *)
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF
  (* Segment selectors (16-bit registers): *)
  | R_CS | R_DS | R_ES | R_FS | R_GS | R_SS
  (* Floating point control register (16-bit): *)
  | R_FPU_CONTROL
  (* Floating point registers (80-bit): *)
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7
  (* General-purpose registers (32-bit): *)
  | R_EAX | R_EBX | R_ECX | R_EDX | R_EDI | R_ESI
  (* Stack pointer and base pointer (32-bit): *)
  | R_ESP | R_EBP
  (* Modifiable segment base registers (32-bit): *)
  | R_FS_BASE | R_GS_BASE
  (* Descriptor table registers (32-bit): *)
  | R_LDTR | R_GDTR
  (* SSE control register (32-bit): *)
  | R_MXCSR
  (* MMX and SSE registers (256-bit): *)
  | R_YMM0 | R_YMM1 | R_YMM2  | R_YMM3  | R_YMM4  | R_YMM5  | R_YMM6  | R_YMM7
  | R_YMM8 | R_YMM9 | R_YMM10 | R_YMM11 | R_YMM12 | R_YMM13 | R_YMM14 | R_YMM15
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE
  (* Temporaries introduced by the lifter: *)
  | V_TEMP (n:N).

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition x86typctx v :=
  match v with
  | V_MEM32 => Some (8*2^32)
  | R_AF | R_CF | R_DF | R_OF | R_PF | R_SF | R_ZF => Some 1
  | R_CS | R_DS | R_ES | R_FS | R_GS | R_SS => Some 16
  | R_FPU_CONTROL => Some 16
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7 => Some 80
  | R_EAX | R_EBX | R_ECX | R_EDX | R_EDI | R_ESI => Some 32
  | R_ESP | R_EBP => Some 32
  | R_FS_BASE | R_GS_BASE => Some 32
  | R_LDTR | R_GDTR => Some 32
  | R_MXCSR => Some 32
  | R_YMM0 | R_YMM1 | R_YMM2  | R_YMM3  | R_YMM4  | R_YMM5  | R_YMM6  | R_YMM7
  | R_YMM8 | R_YMM9 | R_YMM10 | R_YMM11 | R_YMM12 | R_YMM13 | R_YMM14 | R_YMM15 => Some 256
  | A_READ | A_WRITE => Some (2^32)
  | V_TEMP _ => None
  end.

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniX86VarEq <: MiniDecidableType.
  Definition t := x86var.
  Definition eq_dec (v1 v2:x86var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniX86VarEq.

Module X86Arch <: Architecture.
  Module Var := Make_UDT MiniX86VarEq.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := x86typctx.

  Definition mem_readable s a := N.testbit (s A_READ) a = true.
  Definition mem_writable s a := N.testbit (s A_WRITE) a = true.
End X86Arch.

(* Instantiate the Picinae modules with the x86 identifiers above. *)
Module IL_i386 := PicinaeIL X86Arch.
Export IL_i386.
Module Theory_i386 := PicinaeTheory IL_i386.
Export Theory_i386.
Module Statics_i386 := PicinaeStatics IL_i386 Theory_i386.
Export Statics_i386.
Module FInterp_i386 := PicinaeFInterp IL_i386 Theory_i386 Statics_i386.
Export FInterp_i386.
Module PSimpl_i386 := Picinae_Simplifier_Base IL_i386.
Export PSimpl_i386.
Module PSimpl_i386_v1_1 := Picinae_Simplifier_v1_1 IL_i386 Theory_i386 Statics_i386 FInterp_i386.
Ltac PSimplifier ::= PSimpl_i386_v1_1.PSimplifier.

(* To use a different simplifier version (e.g., v1_0) put the following atop your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_i386_v1_0 := Picinae_Simplifier_v1_0 IL_i386 Theory_i386 Statics_i386 FInterp_i386.
Ltac PSimplifier ::= PSimpl_i386_v1_0.PSimplifier.
*)

Module ISA_i386 := Picinae_ISA IL_i386 PSimpl_i386 Theory_i386 Statics_i386 FInterp_i386.
Export ISA_i386.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "i386_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "i386_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "i386_psimpl" "in" hyp(H) := psimpl_hyp H.
Tactic Notation "i386_psimpl" := psimpl_goal.
Ltac x86_step := ISA_step.


(* Simplify memory access propositions by observing that on x86, the only part
   of the store that affects memory accessibility are the page-access bits
   (A_READ and A_WRITE). *)

Lemma memacc_read_frame:
  forall s v u (NE: v <> A_READ),
  MemAcc mem_readable (update s v u) = MemAcc mem_readable s.
Proof.
  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_write_frame:
  forall s v u (NE: v <> A_WRITE),
  MemAcc mem_writable (update s v u) = MemAcc mem_writable s.
Proof.
  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_read_updated:
  forall s v u1 u2,
  MemAcc mem_readable (update (update s v u2) A_READ u1) =
  MemAcc mem_readable (update s A_READ u1).
Proof.
  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.
Qed.

Lemma memacc_write_updated:
  forall s v u1 u2,
  MemAcc mem_writable (update (update s v u2) A_WRITE u1) =
  MemAcc mem_writable (update s A_WRITE u1).
Proof.
  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.
Qed.

(* Simplify x86 memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H ::=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

(* Define ISA-specific notations: *)

Declare Scope i386_scope.
Delimit Scope i386_scope with i386.
Bind Scope i386_scope with stmt exp trace.
Open Scope i386_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : i386_scope.

Module X86Notations.

Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : i386_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : i386_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : i386_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem 32 LittleE 8 m a) (at level 30) : i386_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem 32 LittleE 16 m a) (at level 30) : i386_scope. (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem 32 LittleE 32 m a) (at level 30) : i386_scope. (* read ymm from memory *)
Notation "m [Ⓑ a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : i386_scope. (* write byte to memory *)
Notation "m [Ⓦ a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : i386_scope. (* write word to memory *)
Notation "m [Ⓓ a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : i386_scope. (* write dword to memory *)
Notation "m [Ⓠ a := v  ]" := (setmem 32 LittleE 8 m a v) (at level 50, left associativity) : i386_scope. (* write quad word to memory *)
Notation "m [Ⓧ a := v  ]" := (setmem 32 LittleE 16 m a v) (at level 50, left associativity) : i386_scope. (* write xmm to memory *)
Notation "m [Ⓨ a := v  ]" := (setmem 32 LittleE 32 m a v) (at level 50, left associativity) : i386_scope. (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End X86Notations.

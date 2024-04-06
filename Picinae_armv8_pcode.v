(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2023 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
   Instantiation of Picinae for ARM ISA.               MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   * Picinae_finterp                                        MMMMMMMMMMM7..ZNOOMZ
   * Picinae_statics                                         MMMMMMMMMM$.$MOMO=7
                                                              MDMMMMMMMO.7MDM7M+
   Then compile this module with menu option                   ZMMMMMMMM.$MM8$MN
   Compile->Compile_buffer.                                    $ZMMMMMMZ..MMMOMZ
                                                                ?MMMMMM7..MNN7$M
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
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in IL code lifted from ARM native code: *)
Inductive arm8var :=
  (* Main memory: swap between 32 bit(ARMv1-v8) mode and 64 bit(ARMv8) *)
  | V_MEM32 | V_MEM64
  (* X0-30 = 64bit registers. No need to explicitly define W0-30 since lifted code will address the lower 32 bits when using W registers *)
  | R_X0 | R_X1 | R_X2 | R_X3 | R_X4 | R_X5 | R_X6 | R_X7 | R_X8 | R_X9 | R_X10
  | R_X11 | R_X12 | R_X13 | R_X14 | R_X15 | R_X16 | R_X17 | R_X18 | R_X19 | R_X20
  | R_X21 | R_X22 | R_X23 | R_X24 | R_X25 | R_X26 | R_X27 | R_X28 | R_X29 | R_X30
  (* SP = stack pointer *)
  | R_SP | R_LR | R_PC
  (* ng = negative, zr = zero reg, cy = carry, ov = overflow ? *)
  | R_NG | R_ZR | R_CY | R_OV
  (* for modeling how the cpu handles flag updates *)
  | R_TMPNG | R_TMPZR | R_TMPCY | R_TMPOV
  (* zero reg *)
  | R_XZR
  (* FP/SIMD registers *)
  | R_Z0 | R_Z1 | R_Z2 | R_Z3 | R_Z4 | R_Z5 | R_Z6 | R_Z7 | R_Z8 | R_Z9 | R_Z10
  | R_Z11 | R_Z12 | R_Z13 | R_Z14 | R_Z15 | R_Z16 | R_Z17 | R_Z18 | R_Z19 | R_Z20
  | R_Z21 | R_Z22 | R_Z23 | R_Z24 | R_Z25 | R_Z26 | R_Z27 | R_Z28 | R_Z29 | R_Z30 | R_Z31
  (* explicit registers for SIMD semantics calculations *)
  | R_TMPZ0 | R_TMPZ1 | R_TMPZ2 | R_TMPZ3 | R_TMPZ4 | R_TMPZ5 | R_TMPZ6
  | R_TMP_LDXN
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE
  | V_TEMP (n:N) (* Temporaries introduced by the lifter: *).

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniARM8VarEq <: MiniDecidableType.
  Definition t := arm8var.
  Definition eq_dec (v1 v2:arm8var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniARM8VarEq.

Module ARM8Arch <: Architecture.
  Module Var := Make_UDT MiniARM8VarEq.
  Definition var := Var.t.
  Definition store := var -> value.

  Definition mem_bits := 8%positive.
  Definition mem_readable s a := exists r, s A_READ = VaM r 64 /\ r a <> 0.
  Definition mem_writable s a := exists w, s A_WRITE = VaM w 64 /\ w a <> 0.
End ARM8Arch.

(* Instantiate the Picinae modules with the arm identifiers above. *)
Module IL_arm8 := PicinaeIL ARM8Arch.
Export IL_arm8.
Module Theory_arm8 := PicinaeTheory IL_arm8.
Export Theory_arm8.
<<<<<<< HEAD
Module Statics_arm8 := PicinaeStatics IL_arm8 Theory_arm8.
Export Statics_arm8.
Module FInterp_arm8 := PicinaeFInterp IL_arm8 Theory_arm8 Statics_arm8.
=======
Module Statics_arm8 := PicinaeStatics IL_arm8.
Export Statics_arm8.
Module FInterp_arm8 := PicinaeFInterp IL_arm8 Statics_arm8.
>>>>>>> a719b71 (Add the incomplete strspn arm8 proof and the armv8_pcode file.)
Export FInterp_arm8.

Module PSimpl_arm8 := Picinae_Simplifier_Base.
Export PSimpl_arm8.
Module PSimpl_arm8_v1_1 := Picinae_Simplifier_v1_1 IL_arm8 Theory_arm8 Statics_arm8 FInterp_arm8.

Ltac PSimpl_arm8.PSimplifier ::= PSimpl_arm8_v1_1.PSimplifier.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "arm8_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "arm8_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "arm8_psimpl" "in" hyp(H) := psimpl_all_hyp H.
Tactic Notation "arm8_psimpl" := psimpl_all_goal.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_arm8_v1_0 := Picinae_Simplifier_v1_0 IL_arm8 Statics_arm8 FInterp_arm8.
Ltac PSimpl_arm8.PSimplifier ::= PSimpl_arm8_v1_0.PSimplifier.
*)

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition arm8typctx (id:var) : option typ :=
  match id with
  | V_MEM32 => Some (MemT 32)
  | V_MEM64 => Some (MemT 64)
  | R_X0 | R_X1 | R_X2 | R_X3 | R_X4 | R_X5 | R_X6 | R_X7 | R_X8 | R_X9 | R_X10 => Some (NumT 64)
  | R_X11 | R_X12 | R_X13 | R_X14 | R_X15 | R_X16 | R_X17 | R_X18 | R_X19 | R_X20 => Some (NumT 64)
  | R_X21 | R_X22 | R_X23 | R_X24 | R_X25 | R_X26 | R_X27 | R_X28 | R_X29 | R_X30 => Some (NumT 64)
  | R_XZR => Some (NumT 64)
  | R_SP | R_LR | R_PC => Some (NumT 64)
  | R_NG | R_ZR | R_CY | R_OV => Some (NumT 8)
  | R_TMPNG | R_TMPZR | R_TMPCY | R_TMPOV => Some (NumT 8)
  | A_READ | A_WRITE => Some (MemT 64)
  | V_TEMP _ => None
  | R_Z0 | R_Z1 | R_Z2 | R_Z3 | R_Z4 | R_Z5 | R_Z6 | R_Z7 | R_Z8 | R_Z9 | R_Z10 => Some (NumT 256)
  | R_Z11 | R_Z12 | R_Z13 | R_Z14 | R_Z15 | R_Z16 | R_Z17 | R_Z18 | R_Z19 | R_Z20 => Some (NumT 256)
  | R_Z21 | R_Z22 | R_Z23 | R_Z24 | R_Z25 | R_Z26 | R_Z27 | R_Z28 | R_Z29 | R_Z30 | R_Z31 => Some (NumT 256)
  | R_TMPZ0 | R_TMPZ1 | R_TMPZ2 | R_TMPZ3 | R_TMPZ4 | R_TMPZ5 | R_TMPZ6 => Some(NumT 256)
  | R_TMP_LDXN => Some(NumT 64)
end.

Definition arm8_wtm {s v m w} := @models_wtm v arm8typctx s m w.
Definition arm8_regsize {s v n w} := @models_regsize v arm8typctx s n w.

(* Simplify memory access propositions by observing that on arm, the only part
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

(* Simplify arm memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H :=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

(* The user can ignore all assigned values to specified variables by
   redefining x86_ignore.  Example:
     Ltac x86_ignore v ::= constr:(match v with R_EAX => true | _ => false end).
 *)
Ltac arm8_ignore v := constr:(false).
Ltac arm8_abstract_vars H :=
  repeat match type of H with context [ update ?s ?v ?u ] =>
    let b := ltac:(arm8_ignore v) in
    lazymatch eval cbv in b with true =>
      lazymatch u with
      | VaN ?n ?w =>
          tryif is_var n then fail else
          let tmp := fresh "n" in
          pose (tmp := n);
          change (update s v (VaN n w)) with (update s v (VaN tmp w)) in H;
          clearbody tmp
      | VaM ?m ?w =>
          tryif is_var m then fail else
          let tmp := fresh "m" in
          pose (tmp := m);
          change (update s v (VaM m w)) with (update s v (VaM tmp w)) in H;
          clearbody tmp
      end
    | _ => fail
    end
  end.

(* Values of IL temp variables are ignored by the arm interpreter once the IL
   block that generated them completes.  We can therefore generalize them
   away at IL block boundaries to simplify the expression. *)
Ltac generalize_temps H :=
  repeat match type of H with context [ update ?s (V_TEMP ?n) ?u ] =>
    tryif is_var u then fail else
    lazymatch type of H with context [ Var (V_TEMP ?n) ] => fail | _ =>
      let tmp := fresh "tmp" in
      pose (tmp := u);
      change (update s (V_TEMP n) u) with (update s (V_TEMP n) tmp) in H;
      clearbody tmp;
      try fold value in tmp
    end
  end.

(* Syntax: generalize_frame m as x
   Result: Find any goal expressions of the form m[a1:=u1]...[an:=un] where
   a1..an are adjacent memory addresses, and compact them to expressions
   of the form m[a:=x], where a=max(a1,...,an) and x is a user-specified name.
   This is useful for abstracting a series of pushes that form a callee's
   local stack frame into a single write of the entire byte array. *)
Ltac generalize_frame_forward bytes w en m len1 a1 u1 len2 a2 u2 :=
  let x := fresh in let H := fresh in let H' := fresh in
  evar (x:N);
  eassert (H: setmem w en len2 (setmem w en len1 m a1 u1) a2 u2 = setmem w en _ m a2 x);
  [ subst x; eenough (H':_);
    [ transitivity (setmem w en len2 (setmem w en len1 m a1 u1) (msub w a1 len2) u2);
      [ apply f_equal2; [ exact H' | reflexivity ]
      | etransitivity;
        [ etransitivity;
          [ apply setmem_merge_rev; reflexivity
          | apply f_equal4; [psimpl|..]; reflexivity ]
        | apply f_equal2; [ symmetry; exact H' | reflexivity ] ] ]
    | psimpl; reflexivity ]
  | rewrite H; clear H; clearbody x; try clear u1; try clear u2;
    rename x into bytes ].
Ltac generalize_frame_backward bytes w en m len1 a1 u1 len2 a2 u2 :=
  let x := fresh in let H := fresh in let H' := fresh in
  evar (x:N);
  eassert (H: setmem w en len2 (setmem w en len1 m a1 u1) a2 u2 = setmem w en _ m a1 x);
  [ subst x; eenough (H':_);
    [ transitivity (setmem w en len2 (setmem w en len1 m a1 u1) ((a1+len1) mod 2^w) u2);
      [ apply f_equal2; [ exact H' | reflexivity ]
      | rewrite setmem_mod_l; etransitivity;
        [ etransitivity;
          [ apply setmem_merge; reflexivity
          | apply f_equal4; [psimpl|..]; reflexivity ]
        | apply f_equal2; reflexivity ] ]
    | psimpl; try reflexivity ]
  | rewrite H; clear H; clearbody x; try clear u1; try clear u2;
    rename x into bytes ].
Ltac generalize_frame m bytes :=
  match goal with |- context [ setmem ?w ?en ?len2 (setmem ?w ?en ?len1 m ?a1 ?u1) ?a2 ?u2 ] =>
    first [ generalize_frame_forward bytes w en m len1 a1 u1 len2 a2 u2
          | generalize_frame_backward bytes w en m len1 a1 u1 len2 a2 u2 ]
  end.
Tactic Notation "generalize_frame" constr(m) "as" ident(bytes) :=
  generalize_frame m bytes; repeat generalize_frame m bytes.

Ltac generalize_trace :=
  lazymatch goal with
  | [ |- nextinv ?p ?Invs ?xp ?b (?xs'::?xs1::?t1++?xs0::?t) ] =>
    change (nextinv p Invs xp b (xs'::(xs1::t1)++(xs0::t)));
    let t' := fresh t1 in generalize (xs1::t1); intro t'; clear t1; rename t' into t1
  | [ |- nextinv ?p ?Invs ?xp ?b (?xs'::?xs1::?xs0::?t) ] =>
    change (nextinv p Invs xp b (xs'::(xs1::nil)++(xs0::t)));
    let t' := fresh "t" in generalize (xs1::nil); intro t'
  end.

(* Symbolically evaluate an arm machine instruction for one step, and simplify
   the resulting Coq expressions. *)
Ltac arm8_step_and_simplify XS :=
  step_stmt XS;
  arm8_abstract_vars XS;
  psimpl_vals_hyp XS;
  simpl_memaccs XS;
  destruct_memaccs XS;
  generalize_temps XS.

(* Introduce automated machinery for verifying an x86 machine code subroutine
   (or collection of subroutines) by (1) defining a set of Floyd-Hoare
   invariants (including pre- and post-conditions) and (2) proving that
   symbolically executing the program starting at any invariant point in a
   state that satisfies the program until the next invariant point always
   yields a state that satisfies the reached invariant.  This proves partial
   correctness of the subroutine.

   In order for this methodology to prove that a post-condition holds at
   subroutine exit, we must attach one of these invariants (the post-condition)
   to the return address of the subroutine.  This is a somewhat delicate
   process, since unlike most other code addresses, the exact value of the
   return address is an unknown (defined by the caller).  We therefore adopt
   the convention that subroutines "exit" whenever control flows to an address
   for which no IL code is defined at that address.  This allows proving
   correctness of a subroutine by lifting only the subroutine to IL code (or
   using the pmono theorems from Picinae_theory to isolate only the subroutine
   from a larger program), leaving the non-subroutine code undefined (None). *)

(* Some versions of Coq check injection-heavy proofs very slowly (at Qed).
   This slow-down can be avoided by sequestering prevalent injections into
   lemmas, as we do here. *)
Remark inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
                      Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

(* Simplify (exitof a x) without expanding a. *)
Remark exitof_none a: exitof a None = Addr a. Proof eq_refl.
Remark exitof_some a x: exitof a (Some x) = x. Proof eq_refl.


(* If asked to step the computation when we're already at an invariant point,
   just make the proof goal be the invariant. *)
Ltac arm8_invhere :=
  eapply nextinv_here; [ reflexivity | hnf; psimpl_vals_goal ].

(* If we're not at an invariant, symbolically interpret the program for one
   machine language instruction.  (The user can use "do" to step through many
   instructions, but often it is wiser to pause and do some manual
   simplification of the state at various points.) *)
Ltac arm8_invseek :=
  (* Updated to be similar to Picinae_armv7.v 
     It was not working on Apr 5 2024, but was working December 2023.
     - ilan
  apply NIStep; [reflexivity|];
  let sz := fresh "sz" in let q := fresh "q" in let s := fresh "s" in let x := fresh "x" in
  let IL := fresh "IL" in let XS := fresh "XS" in
  intros sz q s x IL XS;
  apply inj_prog_stmt in IL; destruct IL; subst sz q; *)
  eapply NIStep; [reflexivity|reflexivity|];
  let s := fresh "s" in let x := fresh "x" in let XS := fresh "XS" in
  intros s x XS;
  arm8_step_and_simplify XS;
  repeat lazymatch type of XS with
         | s=_ /\ x=_ => destruct XS; subst s x
         | exec_stmt _ (if ?c then _ else _) _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             arm8_step_and_simplify XS
         | exec_stmt _ (N.iter _ _ _) _ _ => fail
         | _ => arm8_step_and_simplify XS
         end;
  try generalize_trace;
  repeat match goal with [ u:value |- _ ] => clear u
                       | [ n:N |- _ ] => clear n
                       | [ m:addr->N |- _ ] => clear m end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

(* Clear any stale memory-access hypotheses (arising from previous computation
   steps) and either step to the next machine instruction (if we're not at an
   invariant) or produce an invariant as a proof goal. *)
Ltac arm8_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ arm8_invseek; try arm8_invhere | arm8_invhere ].


Declare Scope arm8_scope.
Delimit Scope arm8_scope with arm8.
Bind Scope arm8_scope with stmt exp typ trace.
Open Scope arm8_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : arm8_scope.

Module ARM8Notations.

Notation "Ⓜ m" := (VaM m 64) (at level 20, format "'Ⓜ' m"). (* memory value *)
Notation "ⓑ u" := (VaN u 1) (at level 20, format "'ⓑ' u"). (* bit value *)
Notation "Ⓑ u" := (VaN u 8) (at level 20, format "'Ⓑ' u"). (* byte value *)
Notation "Ⓦ u" := (VaN u 16) (at level 20, format "'Ⓦ' u"). (* word value *)
Notation "Ⓓ u" := (VaN u 32) (at level 20, format "'Ⓓ' u"). (* dword value *)
Notation "Ⓠ u" := (VaN u 64) (at level 20, format "'Ⓠ' u"). (* quad word value *)
Notation "Ⓧ u" := (VaN u 128) (at level 20, format "'Ⓧ' u"). (* xmm value *)
Notation "Ⓨ u" := (VaN u 256) (at level 20, format "'Ⓨ' u"). (* ymm value *)
Notation "m Ⓑ[ a  ]" := (getmem 64 LittleE 1 m a) (at level 30) : arm8_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 64 LittleE 2 m a) (at level 30) : arm8_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 64 LittleE 4 m a) (at level 30) : arm8_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem 64 LittleE 8 m a) (at level 30) : arm8_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem 64 LittleE 16 m a) (at level 30) : arm8_scope. (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem 64 LittleE 32 m a) (at level 30) : arm8_scope. (* read ymm from memory *)
Notation "m [Ⓑ  a := v  ]" := (setmem 64 LittleE 1 m a v) (at level 50, left associativity) : arm8_scope. (* write byte to memory *)
Notation "m [Ⓦ  a := v  ]" := (setmem 64 LittleE 2 m a v) (at level 50, left associativity) : arm8_scope. (* write word to memory *)
Notation "m [Ⓓ  a := v  ]" := (setmem 64 LittleE 4 m a v) (at level 50, left associativity) : arm8_scope. (* write dword to memory *)
Notation "m [Ⓠ  a := v  ]" := (setmem 64 LittleE 8 m a v) (at level 50, left associativity) : arm8_scope. (* write quad word to memory *)
Notation "m [Ⓧ  a := v  ]" := (setmem 64 LittleE 16 m a v) (at level 50, left associativity) : arm8_scope. (* write xmm to memory *)
Notation "m [Ⓨ  a := v  ]" := (setmem 64 LittleE 32 m a v) (at level 50, left associativity) : arm8_scope. (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^64) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 64 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^64) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 64 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End ARM8Notations.

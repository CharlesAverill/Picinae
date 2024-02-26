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
   Instantiation of Picinae for ebpf ISA.               MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   * Picinae_finterp                                        MMMMMMMMMMM7..ZNOOMZ
   * Picinae_statics                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_slogic                                           MDMMMMMMMO.7MDM7M+
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
(* Require Export Picinae_slogic. *)
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

(* Variables found in pcode lifted from ebpf code: *)
Inductive ebpfvar :=
  (* Main memory: MemT 64 *)
  | V_MEM64
  (* General purpose registers *)
  (* Return register *)
  | R_R0 (* NumT 64 *)
  (* Argument registers 1-5 *)
  (* Initially points to program context *)
  | R_R1 (* NumT 64 *)
  | R_R2 | R_R3 | R_R4 | R_R5
  (* Extra general purpose registers *)
  | R_R6 | R_R7 | R_R8 | R_R9
  (* Read-only Stack pointer and base pointer (64-bit): *)
  | R_R10 (* NumT 64 *)
  (* These meta-variables model page access permissions: *)
  (* might be irrelevant for ebpf *)
  | A_READ | A_WRITE
  (* Temporaries introduced by the Pcode lifter: *)
  | V_TEMP (n:N).

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniEBPFVarEq <: MiniDecidableType.
  Definition t := ebpfvar.
  Definition eq_dec (v1 v2:ebpfvar) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.  (* <-- This must be Defined (not Qed!) for finterp to work! *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniEBPFVarEq.

Module EBPFArch <: Architecture.
  Module Var := Make_UDT MiniEBPFVarEq.
  Definition var := Var.t.
  Definition store := var -> value.

  Definition mem_bits := 8%positive.
  Definition mem_readable s a := exists r, s A_READ = VaM r 32 /\ r a <> 0.
  Definition mem_writable s a := exists w, s A_WRITE = VaM w 32 /\ w a <> 0.
End EBPFArch.

(* Instantiate the Picinae modules with the ebpf identifiers above. *)
Module IL_ebpf := PicinaeIL EBPFArch.
Export IL_ebpf.
Module Theory_ebpf := PicinaeTheory IL_ebpf.
Export Theory_ebpf.
Module Statics_ebpf := PicinaeStatics IL_ebpf.
Export Statics_ebpf.
Module FInterp_ebpf := PicinaeFInterp IL_ebpf Statics_ebpf.
Export FInterp_ebpf.
(* Module SLogic_ebpf := PicinaeSLogic IL_ebpf.
Export SLogic_ebpf. *)

Module PSimpl_ebpf := Picinae_Simplifier_Base.
Export PSimpl_ebpf.
Module PSimpl_ebpf_v1_1 := Picinae_Simplifier_v1_1 IL_ebpf Statics_ebpf FInterp_ebpf.
Ltac PSimplifier ::= PSimpl_ebpf_v1_1.PSimplifier.

(* Introduce unique aliases for tactics in case user loads multiple architectures. *)
Tactic Notation "ebpf_psimpl" uconstr(e) "in" hyp(H) := psimpl_exp_hyp uconstr:(e) H.
Tactic Notation "ebpf_psimpl" uconstr(e) := psimpl_exp_goal uconstr:(e).
Tactic Notation "ebpf_psimpl" "in" hyp(H) := psimpl_all_hyp H.
Tactic Notation "ebpf_psimpl" := psimpl_all_goal.

(* To use a different simplifier version (e.g., v1_0) put the following atop
   your proof .v file:
Require Import Picinae_simplifier_v1_0.
Module PSimpl_ebpf_v1_0 := Picinae_Simplifier_v1_0 IL_ebpf Statics_ebpf FInterp_ebpf.
Ltac PSimplifier ::= PSimpl_ebpf_v1_0.PSimplifier.
*)

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition ebpftypctx v :=
  match v with
  | V_MEM64 => Some (MemT 64)
  | R_R0 | R_R1 | R_R2 | R_R3 | R_R4 | R_R5 | R_R6 | R_R7 | R_R8 | R_R9 | R_R10 => Some (NumT 64)
  | A_READ | A_WRITE => Some (MemT 64)
  | V_TEMP _ => None
  end.

Definition ebpf_wtm {s v m w} := @models_wtm v ebpftypctx s m w.
Definition ebpf_regsize {s v n w} := @models_regsize v ebpftypctx s n w.



(* Create some automated machinery for simplifying symbolic expressions commonly
   arising from ebpf instruction operations.  Mostly this involves simplifying
   (e mod 2^w) whenever e < 2^w. *)

(* Define an abbreviation for ebpf's parity flag computation, which produces
   uncomfortably large symbolic expressions. *)
Definition parity n :=
  N.lnot ((N.lxor
    (N.shiftr (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
                      (N.lxor (N.shiftr n 4) n)) 1)
    (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
            (N.lxor (N.shiftr n 4) n))) mod 2^1) 1.

Lemma fold_parity: forall n,
  N.lnot ((N.lxor
    (N.shiftr (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
                      (N.lxor (N.shiftr n 4) n)) 1)
    (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
            (N.lxor (N.shiftr n 4) n))) mod 2^1) 1
  = parity n.
Proof. intro. reflexivity. Qed.


(* Simplify memory access propositions by observing that on ebpf, the only part
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


(* getmem assembles bytes into words by logical-or'ing them together, but
   sometimes it is easier to reason about them as if they were summed.  The
   following theorem proves that logical-or and addition are the same when
   the operands share no common bits. *)
Theorem lor_plus:
  forall a b (A0: N.land a b = 0), N.lor a b = a + b.
Proof.
  intros. rewrite <- N.lxor_lor, N.add_nocarry_lxor by assumption. reflexivity.
Qed.

(* (a & b) ^ c = (a ^ c) & b whenever b & c = c *)
Lemma lxor_land:
  forall a b c, N.land b c = c -> N.lxor (N.land a b) c = N.land (N.lxor a c) b.
Proof.
 intros. apply N.bits_inj. apply N.bits_inj_iff in H. intro n. specialize (H n).
 do 2 rewrite N.land_spec, N.lxor_spec. rewrite <- H, N.land_spec.
 repeat destruct (N.testbit _ n); reflexivity.
Qed.

(* Simplify ebpf memory access assertions produced by step_stmt. *)
Ltac simpl_memaccs H :=
  try lazymatch type of H with context [ MemAcc mem_writable ] =>
    rewrite ?memacc_write_frame, ?memacc_write_updated in H by discriminate 1
  end;
  try lazymatch type of H with context [ MemAcc mem_readable ] =>
    rewrite ?memacc_read_frame, ?memacc_read_updated in H by discriminate 1
  end.

(* The user can ignore all assigned values to specified variables by
   redefining ebpf_ignore.  Example:
     Ltac ebpf_ignore v ::= constr:(match v with R_EAX => true | _ => false end).
 *)
Ltac ebpf_ignore v := constr:(false).
Ltac ebpf_abstract_vars H :=
  repeat match type of H with context [ update ?s ?v ?u ] =>
    let b := ltac:(ebpf_ignore v) in
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

(* Values of IL temp variables are ignored by the ebpf interpreter once the IL
   block that generated them completes.  We can therefore generalize them
   away at IL block boundaries to simplify the expression. *)
Ltac generalize_temps H :=
  repeat match type of H with context [ update ?s (V_TEMP ?n) ?u ] =>
    tryif is_var u then fail else
    lazymatch type of H with context [ Var (V_TEMP n) ] => fail | _ =>
      let tmp := fresh "tmp" in
      pose (tmp := u);
      change (update s (V_TEMP n) u) with (update s (V_TEMP n) tmp) in H;
      clearbody tmp;
      try fold value in tmp
    end
  end.

(* Symbolically evaluate an ebpf machine instruction for one step, and simplify
   the resulting Coq expressions. *)
Ltac ebpf_step_and_simplify XS :=
  step_stmt XS;
  ebpf_abstract_vars XS;
  psimpl_vals_hyp XS;
  simpl_memaccs XS;
  destruct_memaccs XS;
  generalize_temps XS.

(* Introduce automated machinery for verifying an ebpf machine code subroutine
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
Ltac ebpf_invhere :=
  eapply nextinv_here; [ reflexivity | red; psimpl_vals_goal ].

(* If we're not at an invariant, symbolically interpret the program for one
   machine language instruction.  (The user can use "do" to step through many
   instructions, but often it is wiser to pause and do some manual
   simplification of the state at various points.) *)
Ltac ebpf_invseek :=
  eapply NIStep; [reflexivity|reflexivity|];
  let s := fresh "s" in let x := fresh "x" in let XS := fresh "XS" in
  intros s x XS;
  ebpf_step_and_simplify XS;
  repeat lazymatch type of XS with
         | s=_ /\ x=_ => destruct XS; subst s x
         | exec_stmt _ (if ?c then _ else _) _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ebpf_step_and_simplify XS
         | exec_stmt _ (N.iter _ _ _) _ _ => fail
         | _ => ebpf_step_and_simplify XS
         end;
  try match goal with |- nextinv _ _ _ _ (_ :: ?xs :: ?t) =>
    let t' := fresh t in generalize (xs::t); intro t'; clear t; rename t' into t
  end;
  repeat match goal with [ u:value |- _ ] => clear u
                       | [ n:N |- _ ] => clear n
                       | [ m:addr->N |- _ ] => clear m end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

(* Clear any stale memory-access hypotheses (arising from previous computation
   steps) and either step to the next machine instruction (if we're not at an
   invariant) or produce an invariant as a proof goal. *)
Ltac ebpf_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ ebpf_invseek; try ebpf_invhere | ebpf_invhere ].


Declare Scope ebpf_scope.
Delimit Scope ebpf_scope with ebpf.
Bind Scope ebpf_scope with stmt exp typ trace.
Open Scope ebpf_scope.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : ebpf_scope.

Module EBPFNotations.

Notation "Ⓜ m" := (VaM m 32) (at level 20, format "'Ⓜ' m") : ebpf_scope. (* memory value *)
Notation "ⓑ u" := (VaN u 1) (at level 20, format "'ⓑ' u"). (* bit value *)
Notation "Ⓑ u" := (VaN u 8) (at level 20, format "'Ⓑ' u"). (* byte value *)
Notation "Ⓦ u" := (VaN u 16) (at level 20, format "'Ⓦ' u"). (* word value *)
Notation "Ⓓ u" := (VaN u 32) (at level 20, format "'Ⓓ' u"). (* dword value *)
Notation "Ⓠ u" := (VaN u 64) (at level 20, format "'Ⓠ' u"). (* quad word value *)
Notation "Ⓧ u" := (VaN u 128) (at level 20, format "'Ⓧ' u"). (* xmm value *)
Notation "Ⓨ u" := (VaN u 256) (at level 20, format "'Ⓨ' u"). (* ymm value *)
Notation "m Ⓑ[ a  ]" := (getmem 32 LittleE 1 m a) (at level 30) : ebpf_scope. (* read byte from memory *)
Notation "m Ⓦ[ a  ]" := (getmem 32 LittleE 2 m a) (at level 30) : ebpf_scope. (* read word from memory *)
Notation "m Ⓓ[ a  ]" := (getmem 32 LittleE 4 m a) (at level 30) : ebpf_scope. (* read dword from memory *)
Notation "m Ⓠ[ a  ]" := (getmem 32 LittleE 8 m a) (at level 30) : ebpf_scope. (* read quad word from memory *)
Notation "m Ⓧ[ a  ]" := (getmem 32 LittleE 16 m a) (at level 30) : ebpf_scope. (* read xmm from memory *)
Notation "m Ⓨ[ a  ]" := (getmem 32 LittleE 32 m a) (at level 30) : ebpf_scope. (* read ymm from memory *)
Notation "m [Ⓑ a := v  ]" := (setmem 32 LittleE 1 m a v) (at level 50, left associativity) : ebpf_scope. (* write byte to memory *)
Notation "m [Ⓦ a := v  ]" := (setmem 32 LittleE 2 m a v) (at level 50, left associativity) : ebpf_scope. (* write word to memory *)
Notation "m [Ⓓ a := v  ]" := (setmem 32 LittleE 4 m a v) (at level 50, left associativity) : ebpf_scope. (* write dword to memory *)
Notation "m [Ⓠ a := v  ]" := (setmem 32 LittleE 8 m a v) (at level 50, left associativity) : ebpf_scope. (* write quad word to memory *)
Notation "m [Ⓧ a := v  ]" := (setmem 32 LittleE 16 m a v) (at level 50, left associativity) : ebpf_scope. (* write xmm to memory *)
Notation "m [Ⓨ a := v  ]" := (setmem 32 LittleE 32 m a v) (at level 50, left associativity) : ebpf_scope. (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := (msub 32 x y) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 55, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 55, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 55, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 56, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 57, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 58, left associativity). (* logical or *)

End EBPFNotations.

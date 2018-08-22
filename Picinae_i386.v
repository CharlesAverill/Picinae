(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2018 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
Require Export Picinae_finterp.
Require Export Picinae_statics.
Require Export Picinae_slogic.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Open Scope N.

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
  (* These meta-variables model page access permissions: *)
  | A_READ | A_WRITE
  (* Temporaries introduced by the BIL lifter: *)
  | V_TEMP (n:N).

(* Create a UsualDecidableType module (which is an instance of Typ) to give as
   input to the Architecture module, so that it understands how the variable
   identifiers chosen above are syntactically written and how to decide whether
   any two variable instances refer to the same variable. *)

Module MiniX86VarEq <: MiniDecidableType.
  Definition t := x86var.
  Definition eq_dec (v1 v2:x86var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Qed. (* Some users may want to change this Qed to Defined. *)
End MiniX86VarEq.

Module X86Arch <: Architecture.
  Module Var := Make_UDT MiniX86VarEq.
  Definition var := Var.t.
  Definition store := var -> option value.

  Definition mem_bits := 8%positive.
  Definition mem_readable s a := exists r, s A_READ = Some (VaM r 32) /\ r a <> 0.
  Definition mem_writable s a := exists w, s A_WRITE = Some (VaM w 32) /\ w a <> 0.
  Theorem mem_readable_mono:
    forall s1 s2 a, s1 ⊆ s2 -> mem_readable s1 a -> mem_readable s2 a.
  Proof. intros. destruct H0. eexists. split; [apply H|]; apply H0. Qed.
  Theorem mem_writable_mono:
    forall s1 s2 a, s1 ⊆ s2 -> mem_writable s1 a -> mem_writable s2 a.
  Proof. intros. destruct H0. eexists. split; [apply H|]; apply H0. Qed.
End X86Arch.

(* Instantiate the Picinae modules with the x86 identifiers above. *)
Module IL_i386 := PicinaeIL X86Arch.
Export IL_i386.
Module Theory_i386 := PicinaeTheory IL_i386.
Export Theory_i386.
Module FInterp_i386 := PicinaeFInterp IL_i386.
Export FInterp_i386.
Module Statics_i386 := PicinaeStatics IL_i386.
Export Statics_i386.
Module SLogic_i386 := PicinaeSLogic IL_i386.
Export SLogic_i386.

(* Declare the types (i.e., bitwidths) of all the CPU registers: *)
Definition x86typctx v :=
  match v with
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
  | A_READ | A_WRITE => Some (MemT 32)
  | V_TEMP _ => None
  end.

Definition x86_wtm {s v mem mw} := @models_wtm x86typctx s v mem mw.
Definition x86_regsize {s v u w} := @models_regsize x86typctx s v u w.



(* Create some automated machinery for simplifying symbolic expressions commonly arising
   from x86 instruction operations.  Mostly this involves simplifying e mod 2^w whenever
   e < 2^w. *)

(* Define an abbreviation for x86's parity flag computation, which produces uncomfortably
   large symbolic expressions. *)
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

Lemma memacc_read_frame:
  forall h s v u (NE: v <> A_READ),
  MemAcc mem_readable h (update s v u) = MemAcc mem_readable h s.
Proof.
  intros. unfold MemAcc, mem_readable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_write_frame:
  forall h s v u (NE: v <> A_WRITE),
  MemAcc mem_writable h (update s v u) = MemAcc mem_writable h s.
Proof.
  intros. unfold MemAcc, mem_writable. rewrite update_frame. reflexivity.
  apply not_eq_sym. exact NE.
Qed.

Lemma memacc_read_updated:
  forall h s v u1 u2,
  MemAcc mem_readable h (update (update s v u2) A_READ u1) =
  MemAcc mem_readable h (update s A_READ u1).
Proof.
  intros. unfold MemAcc, mem_readable. rewrite !update_updated. reflexivity.
Qed.

Lemma memacc_write_updated:
  forall h s v u1 u2,
  MemAcc mem_writable h (update (update s v u2) A_WRITE u1) =
  MemAcc mem_writable h (update s A_WRITE u1).
Proof.
  intros. unfold MemAcc, mem_writable. rewrite !update_updated. reflexivity.
Qed.


(* getmem assembles bytes into words by logical-or'ing them together, but sometimes it
   is easier to reason about them as if they were added.  The following theorem proves
   that logical-or and addition are the same when the operands share no common bits. *)
Theorem lor_plus:
  forall a b (A0: N.land a b = 0), N.lor a b = a + b.
Proof.
  intros. rewrite <- N.lxor_lor, N.add_nocarry_lxor by assumption. reflexivity.
Qed.

(* ((width) memory[...]) mod 2^width = (width) memory[...] *)
Lemma memlo: forall len w m a, welltyped_memory m -> Mb*len <= w ->
  (getmem LittleE len m a) mod 2^w = getmem LittleE len m a.
Proof.
  intros. apply N.mod_small. eapply N.lt_le_trans.
    apply getmem_bound. assumption.
    apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

(* (e mod 2^b) mod 2^c = e mod 2^(min b c) *)
Lemma dblmod_l: forall a b c, b <= c -> (a mod 2^b) mod 2^c = a mod 2^b.
Proof.
  intros. repeat rewrite <- N.land_ones.
  rewrite <- N.land_assoc, (N.land_comm (N.ones _)), N.land_ones, N.ones_mod_pow2.
  reflexivity. assumption.
Qed.

Lemma dblmod_r: forall a b c, c <= b -> (a mod 2^b) mod 2^c = a mod 2^c.
Proof.
  intros. repeat rewrite <- N.land_ones.
  rewrite <- N.land_assoc, N.land_ones, N.ones_mod_pow2.
  reflexivity. assumption.
Qed.

(* e & (N.ones w) = e mod 2^w *)
Remark land_mod_r: forall x y z, N.log2 (N.succ y) = N.succ (N.log2 y) -> z = N.log2 (N.succ y) ->
  N.land x y = x mod 2^z.
Proof.
  intros x y z H1 H2. subst z. destruct y.
    rewrite N.mod_1_r. apply N.land_0_r.

    apply N.log2_eq_succ_iff_pow2 in H1; [|reflexivity]. destruct H1 as [b H1].
    rewrite H1, N.log2_pow2 by apply N.le_0_l.
    rewrite <- (N.pred_succ (Npos p)), H1, <- N.ones_equiv.
    apply N.land_ones.
Qed.

(* (a & b) ^ c = (a ^ c) & b whenever b & c = c *)
Lemma lxor_land:
  forall a b c, N.land b c = c -> N.lxor (N.land a b) c = N.land (N.lxor a c) b.
Proof.
 intros. apply N.bits_inj. apply N.bits_inj_iff in H. intro n. specialize (H n).
 do 2 rewrite N.land_spec, N.lxor_spec. rewrite <- H, N.land_spec.
 repeat destruct (N.testbit _ n); reflexivity.
Qed.

Remark land_mod_l: forall x y z, N.log2 (N.succ x) = N.succ (N.log2 x) -> z = N.log2 (N.succ x) ->
  N.land x y = y mod 2^z.
Proof. intros x y. rewrite N.land_comm. apply land_mod_r. Qed.

(* (x*y) mod x = 0 *)
Remark mod_mul_l: forall x y, x<>0 -> (x*y) mod x = 0.
Proof. intros. rewrite N.mul_comm. apply N.mod_mul. assumption. Qed.

(* (x+y) mod x = y mod x *)
Remark mod_add_l: forall x y, x<>0 -> (x+y) mod x = y mod x.
Proof. intros. rewrite <- N.add_mod_idemp_l, N.mod_same, N.add_0_l by assumption. reflexivity. Qed.

(* (y+x) mod x = y mod x *)
Remark mod_add_r: forall x y, y<>0 -> (x+y) mod y = x mod y.
Proof. intros. rewrite <- N.add_mod_idemp_r, N.mod_same, N.add_0_r by assumption. reflexivity. Qed.

(* (x*z + y) mod z = y mod z *)
Remark mod_add_mul_lr: forall x y z, z<>0 -> (x*z + y) mod z = y mod z.
Proof. intros. rewrite <- N.add_mod_idemp_l, N.mod_mul, N.add_0_l by assumption. reflexivity. Qed.

(* (z*x + y) mod z = y mod z *)
Remark mod_add_mul_ll: forall x y z, z<>0 -> (z*x + y) mod z = y mod z.
Proof. intros. rewrite <- N.add_mod_idemp_l, mod_mul_l, N.add_0_l by assumption. reflexivity. Qed.

(* (x + y*z) mod z = x mod z *)
Remark mod_add_mul_rr: forall x y z, z<>0 -> (x + y*z) mod z = x mod z.
Proof. intros. rewrite <- N.add_mod_idemp_r, N.mod_mul, N.add_0_r by assumption. reflexivity. Qed.

(* (x + z*y) mod z = x mod z *)
Remark mod_add_mul_rl: forall x y z, z<>0 -> (x + z*y) mod z = x mod z.
Proof. intros. rewrite <- N.add_mod_idemp_r, mod_mul_l, N.add_0_r by assumption. reflexivity. Qed.

(* (mem a) mod 2^8 = mem a *)
Remark mem_small: forall m a, welltyped_memory m -> (m a) mod 2^Mb = m a.
Proof. intros. apply N.mod_small, H. Qed.

(* e << w = 0 whenever e < 2^w *)
Lemma shiftr_low_pow2: forall a n, a < 2^n -> N.shiftr a n = 0.
Proof.
  intros. destruct a. apply N.shiftr_0_l.
  apply N.shiftr_eq_0. apply N.log2_lt_pow2. reflexivity. assumption.
Qed.


Create HintDb mod_pow2 discriminated.
Global Hint Rewrite N.sub_0_r : mod_pow2.
Global Hint Rewrite N.add_0_l : mod_pow2.
Global Hint Rewrite N.add_0_r : mod_pow2.
Global Hint Rewrite N.mul_0_l : mod_pow2.
Global Hint Rewrite N.mul_0_r : mod_pow2.
Global Hint Rewrite N.land_0_l : mod_pow2.
Global Hint Rewrite N.land_0_r : mod_pow2.
Global Hint Rewrite N.lor_0_l : mod_pow2.
Global Hint Rewrite N.lor_0_r : mod_pow2.
Global Hint Rewrite N.lxor_0_l : mod_pow2.
Global Hint Rewrite N.lxor_0_r : mod_pow2.
Global Hint Rewrite getmem_1 : mod_pow2.
Global Hint Rewrite N.mul_1_l : mod_pow2.
Global Hint Rewrite N.mul_1_r : mod_pow2.
Global Hint Rewrite fold_parity : mod_pow2.
Global Hint Rewrite N.lxor_nilpotent : mod_pow2.
Global Hint Rewrite N.mod_same using discriminate 1 : mod_pow2.
Global Hint Rewrite N.mod_mul using discriminate 1 : mod_pow2.
Global Hint Rewrite lxor_land using reflexivity : mod_pow2.
Global Hint Rewrite dblmod_l using discriminate 1 : mod_pow2.
Global Hint Rewrite dblmod_r using discriminate 1 : mod_pow2.
Global Hint Rewrite mod_mul_l using discriminate 1 : mod_pow2.
Global Hint Rewrite mod_add_l using discriminate 1 : mod_pow2.
Global Hint Rewrite mod_add_r using discriminate 1 : mod_pow2.
Global Hint Rewrite mod_add_mul_lr using discriminate 1 : mod_pow2.
Global Hint Rewrite mod_add_mul_ll using discriminate 1 : mod_pow2.
Global Hint Rewrite mod_add_mul_rr using discriminate 1 : mod_pow2.
Global Hint Rewrite mod_add_mul_rl using discriminate 1 : mod_pow2.
Global Hint Rewrite mem_small using assumption : mod_pow2.
(*
Global Hint Rewrite memlo using solve [ discriminate 1 | assumption ] : mod_pow2.
Global Hint Rewrite shiftr_low_pow2 using solve_lt : mod_pow2.
Global Hint Rewrite N.mod_small using solve_lt : mod_pow2.
*)


(* When reducing modulo operations, try auto-solving inequalities of the form x < 2^w. *)

Ltac solve_lt_prim :=
  reflexivity +
  eassumption +
  (apply N.mod_upper_bound; discriminate 1) +
  lazymatch goal with [ M: models x86typctx ?s, R: ?s ?r = Some (VaN ?x ?w) |- ?x < _ ] => apply (x86_regsize M R)
                    | [ WTM: welltyped_memory ?m |- ?m _ < _ ] => apply WTM end +
  (apply getmem_bound; assumption) +
  (apply lxor_bound; solve_lt) +
  (apply land_bound; solve_lt) +
  (apply lor_bound; solve_lt) +
  (apply lnot_bound; solve_lt) +
  (eapply N.le_lt_trans; [ apply N.le_sub_l | solve_lt ])
with solve_lt :=
  solve_lt_prim +
  (eapply N.lt_le_trans; [ solve_lt_prim | discriminate 1 ]).

(* Try to auto-simplify modular arithmetic expressions within a Coq expression resulting from
   functional interpretation of an x86 IL statement.

   Implementation notes:  Currently I am using a combination of autorewrite and repeated
   context-matching for this, since it's the fastest solution I can find (as of Coq 8.0).
   Using rewrite_strat with topdown strategy is much slower; I'm not sure why. *)

Tactic Notation "simpl_x86" "in" hyp(H) :=
  autorewrite with mod_pow2 in H;
  repeat (match type of H with
  | context [ (getmem LittleE ?len ?m ?a) mod 2^?w ] => rewrite (memlo len w m a) in H; [| assumption | discriminate 1 ]
  | context [ N.shiftr ?X ?Y ] => rewrite (shiftr_low_pow2 X Y) in H by solve_lt
  | context [ ?X mod ?M ] => rewrite (N.mod_small X M) in H by solve_lt
  | context [ N.land ?X ?Y ] => (erewrite (land_mod_r X Y) in H +
                                 erewrite (land_mod_l X Y) in H); [| reflexivity | simpl;reflexivity ]
  end; autorewrite with mod_pow2 in H).

Ltac simpl_x86 :=
  autorewrite with mod_pow2;
  repeat (match goal with
  | |- context [ (getmem LittleE ?len ?m ?a) mod 2^?w ] => rewrite (memlo len w m a); [| assumption | discriminate 1 ]
  | |- context [ N.shiftr ?X ?Y ] => rewrite (shiftr_low_pow2 X Y) by solve_lt
  | |- context [ ?X mod ?M ] => rewrite (N.mod_small X M) by solve_lt
  | |- context [ N.land ?X ?Y ] => (erewrite (land_mod_r X Y) +
                                    erewrite (land_mod_l X Y)); [| reflexivity | simpl;reflexivity ]
  end; autorewrite with mod_pow2).



(* Introduce automated machinery for verifying an x86 machine code subroutine (or collection
   of subroutines) by (1) defining a set of Floyd-Hoare invariants (including pre- and post-
   conditions) and (2) proving that symbolically executing the program starting at any
   invariant point in a state that satisfies the program until the next invariant point always
   yields a state that satisfies the reached invariant.  This proves partial correctness of
   the subroutine.

   In order for this methodology to prove that a post-condition holds at subroutine exit,
   we must attach one of these invariants (the post-condition) to the return address of the
   subroutine.  This is a somewhat delicate process, since unlike most other code addresses,
   the exact value of the return address is defined by the caller.  We therefore adopt the
   following conventions:  Assume that an x86 subroutine begins with a return address located
   at a particular memory address (determined by the subroutine's calling convention).  The
   subroutine "exits" when control flows to that address.  As a precondition of the subroutine,
   we assume that the subroutine program p does not assign an IL block to the return address
   (i.e., p retaddr = None).  If this assumption is violated, it means that the caller is
   part of the callee (i.e., the subroutine recursively called itself), which is not
   really the end of the subroutine's execution. *)


(* A subroutine invariant takes a program p, a set of invariants inv_set assigned to various
   fixed code addresses, a post-condition (postcond), and a return address retaddr (which is
   usually a symbolic Coq expression that extracts the appropriate value from memory), and
   uses those to map each exit condition, store, and step count to a proposition.
   Implementation note: Program p is not actually used in the definition, but including it in
   the parameters helps Coq more easily unify some of the goals in the automated machinery
   that follows. *)

Definition x86_subroutine_inv (_:program) inv_set postcond retaddr x (s:store) (n:nat) : option Prop :=
  match x with
  | Exit a => if N.eq_dec a retaddr then Some (postcond a x s n) else inv_set a x s n
  | _ => Some True
  end.

(* Since we are proving partial correctness, we know that the computation doesn't get aborted
   by a computation limit in the middle (since that violates the termination assumption). *)
Remark not_unfinished:
  forall x (a':addr) h p a s m n s' x',
  match x with
  | Some (Exit a2) => exec_prog h p a2 s m n s' x'
  | None => exec_prog h p a s m n s' x'
  | Some x2 => Exit a' = x2
  end -> x <> Some Unfinished.
Proof. intros. destruct x as [e|]; [destruct e|]; discriminate. Qed.

(* If we reach the return address during symbolic interpretation, stop and request that the
   user prove the post-condition using the current state. *)
Remark x86_returning:
  forall ra s n inv_set (postcond: addr -> exit -> store -> nat -> Prop) h p m n' s' x',
  postcond ra (Exit ra) s n ->
  next_inv_sat (x86_subroutine_inv p inv_set postcond ra)
               match x86_subroutine_inv p inv_set postcond ra (Exit ra) s n with
               | Some _ => true | None => false end
               (Exit ra) h p s m n n' s' x'.
Proof.
  intros. unfold x86_subroutine_inv. destruct (N.eq_dec ra ra) eqn:H'.
    apply NISHere. rewrite H'. assumption.
    exfalso. apply n0. reflexivity.
Qed.

(* If we reach some other address to which an invariant has been assigned, stop and request
   that the user prove the invariant using the current state. *)
Remark x86_not_returning_invhere (P: Prop):
  forall p inv_set postcond ra a s n
         (RET: p ra = match p a with Some _ => None | None => Some (0,Nop) end)
         (IS: inv_set a (Exit a) s n = Some P),
  P ->
  match x86_subroutine_inv p inv_set postcond ra (Exit a) s n with Some P => P | None => False end.
Proof.
  intros. unfold x86_subroutine_inv. destruct (N.eq_dec a ra) as [EQ|NE].
    subst a. destruct (p ra); discriminate RET.
    rewrite IS. assumption.
Qed.

(* If we're at a code address to which no invariant has been assigned, step the
   computation to the next instruction. *)
Remark x86_not_returning_invstep (b:bool):
  forall OP inv_set postcond a ra s n h p m n' s' x'
         (RET: p ra = match p a with Some _ => None | None => Some (0,Nop) end)
         (IS: match inv_set a (Exit a) s n with Some _ => true | None => false end = b),
  next_inv_sat OP b (Exit a) h p s m n n' s' x' ->
  next_inv_sat OP match x86_subroutine_inv p inv_set postcond ra (Exit a) s n with
                  | Some _ => true | None => false end
                  (Exit a) h p s m n n' s' x'.
Proof.
  intros.
  unfold x86_subroutine_inv. destruct (N.eq_dec a _) as [EQ|NE].
    rewrite <- EQ in RET. destruct (p a); discriminate RET.
    rewrite IS. exact H.
Qed.

(* Some versions of Coq check injection-heavy proofs very slowly (at Qed).  This slow-down can
   be avoided by sequestering prevalent injections into lemmas, as we do here. *)
Remark inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
                      Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

(* Simplify x86 memory access permissions between simpl_stmt simplification steps. *)
Ltac simpl_memaccs H :=
  repeat first [ rewrite memacc_read_updated in H
               | rewrite memacc_write_updated in H
               | rewrite memacc_read_frame in H by discriminate 1
               | rewrite memacc_write_frame in H by discriminate 1 ].

Tactic Notation "x86_simpl_stmt" "in" hyp(H) := simpl_stmt using simpl_memaccs in H.
Tactic Notation "x86_bsimpl" "in" hyp(H) := bsimpl using simpl_memaccs in H.

(* Values of IL temp variables are ignored by the x86 interpreter once the IL block that
   generated them completes.  We can therefore generalize them away at IL block boundaries
   to simplify the expression. *)
Ltac generalize_temps :=
  repeat match goal with |- context c [ update ?S (V_TEMP ?N) (Some ?U) ] => lazymatch goal with |- ?G =>
    let u := fresh "tmp" in
      set (u:=Some U) in |- * at 0;
      let c' := context c[update S (V_TEMP N) u] in
        change G with c'; generalize u; clear u; intro
  end end.

(* If asked to step the computation when we're already at an invariant point, just
   make the proof goal be the invariant. *)
Ltac x86_invhere := first
  [ eapply NISHere, x86_not_returning_invhere; [assumption|reflexivity|simpl_stores]
  | apply x86_returning ]; simpl_x86.

(* Symbolically evaluate an x86 machine instruction for one step, and simplify the resulting
   Coq expressions. *)
Ltac x86_step_and_simplify XS XP' :=
  (x86_bsimpl in XS; [|exact XP']);
  revert XS; generalize_temps; intro XS;
  simpl_x86 in XS.

(* If we're not at an invariant, symbolically interpret the program for one machine
   language instruction.  (The user can use "do" to step through many instructions,
   but often it is wiser to pause and do some manual simplification of the state at
   various points.) *)
Ltac x86_invseek :=
  apply NISStep;
  let sz := fresh "sz" in let q := fresh "Q" in let s := fresh "s" in let x := fresh "x" in
  let LT := fresh "LT" in let IL := fresh "IL" in let XS := fresh "XS" in let XP' := fresh "XP'" in
  intros sz q s x LT IL XS XP'; clear LT;
  apply not_unfinished in XP';
  apply inj_prog_stmt in IL; destruct IL; subst sz q;
  lazymatch goal with |- context [ Exit (?x + ?y) ] => simpl (x+y) end;
  x86_step_and_simplify XS XP';
  repeat lazymatch goal with [ ACC: MemAcc _ _ _ _ _ |- _ ] => simpl_x86 ACC; revert ACC end; intros;
  repeat lazymatch type of XS with exec_stmt _ _ (if ?c then _ else _) _ _ _ =>
    let BC := fresh "BC" in
    lazymatch c with (if ?c2 then _ else _) => destruct c2 eqn:BC
                   | N.lnot (if ?c2 then _ else _) 1 => destruct c2 eqn:BC
                   | _ => destruct c eqn:BC end;
    simpl_x86 in BC;
    x86_step_and_simplify XS XP'
  end;
  clear XP'; repeat match goal with [ u:value |- _ ] => clear u
                                  | [ u:option value |- _ ] => clear u end;
  lazymatch type of XS with s=_ /\ x=_ =>
    destruct XS; subst x;
    first [ apply (x86_not_returning_invstep false); [assumption|reflexivity|subst s]
          | apply (x86_not_returning_invstep true); [assumption|reflexivity|subst s]
          | apply x86_returning; subst s ]
  end.

(* Clear any stale memory-access hypotheses (arising from previous computation steps)
   and either step to the next machine instruction (if we're not at an invariant) or
   produce an invariant as a proof goal. *)
Ltac x86_step :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ x86_invseek; try x86_invhere | x86_invhere ].


Module X86Notations.

Notation "Ⓜ m" := (Some (VaM m 32)) (at level 20). (* memory value *)
Notation "ⓑ u" := (Some (VaN u 1)) (at level 20). (* bit value *)
Notation "Ⓑ u" := (Some (VaN u 8)) (at level 20). (* byte value *)
Notation "Ⓦ u" := (Some (VaN u 16)) (at level 20). (* word value *)
Notation "Ⓓ u" := (Some (VaN u 32)) (at level 20). (* dword value *)
Notation "Ⓠ u" := (Some (VaN u 64)) (at level 20). (* quad word value *)
Notation "Ⓧ u" := (Some (VaN u 128)) (at level 20). (* xmm value *)
Notation "Ⓨ u" := (Some (VaN u 256)) (at level 20). (* ymm value *)
Notation "m Ⓑ[ a ]" := (getmem LittleE 1 m a) (at level 10). (* read byte from memory *)
Notation "m Ⓦ[ a ]" := (getmem LittleE 2 m a) (at level 10). (* read word from memory *)
Notation "m Ⓓ[ a ]" := (getmem LittleE 4 m a) (at level 10). (* read dword from memory *)
Notation "m Ⓠ[ a ]" := (getmem LittleE 8 m a) (at level 10). (* read quad word from memory *)
Notation "m Ⓧ[ a ]" := (getmem LittleE 16 m a) (at level 10). (* read xmm from memory *)
Notation "m Ⓨ[ a ]" := (getmem LittleE 32 m a) (at level 10). (* read ymm from memory *)
Notation "m [Ⓑ a := v ]" := (setmem LittleE 1 m a v) (at level 50, left associativity). (* write byte to memory *)
Notation "m [Ⓦ a := v ]" := (setmem LittleE 2 m a v) (at level 50, left associativity). (* write word to memory *)
Notation "m [Ⓓ a := v ]" := (setmem LittleE 4 m a v) (at level 50, left associativity). (* write dword to memory *)
Notation "m [Ⓠ a := v ]" := (setmem LittleE 8 m a v) (at level 50, left associativity). (* write quad word to memory *)
Notation "m [Ⓧ a := v ]" := (setmem LittleE 16 m a v) (at level 50, left associativity). (* write xmm to memory *)
Notation "m [Ⓨ a := v ]" := (setmem LittleE 32 m a v) (at level 50, left associativity). (* write ymm to memory *)
Notation "x ⊕ y" := ((x+y) mod 2^32) (at level 50, left associativity). (* modular addition *)
Notation "x ⊖ y" := ((x-y) mod 2^32) (at level 50, left associativity). (* modular subtraction *)
Notation "x ⊗ y" := ((x*y) mod 2^32) (at level 40, left associativity). (* modular multiplication *)
Notation "x << y" := (N.shiftl x y) (at level 40, left associativity). (* logical shift-left *)
Notation "x >> y" := (N.shiftr x y) (at level 40, left associativity). (* logical shift-right *)
Notation "x >>> y" := (ashiftr 32 x y) (at level 40, left associativity). (* arithmetic shift-right *)
Notation "x .& y" := (N.land x y) (at level 55, left associativity). (* logical and *)
Notation "x .^ y" := (N.lxor x y) (at level 55, left associativity). (* logical xor *)
Notation "x .| y" := (N.lor x y) (at level 55, left associativity). (* logical or *)

End X86Notations.

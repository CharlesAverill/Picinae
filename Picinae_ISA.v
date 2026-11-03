(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2026 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
   Support code for instantiating Picinae to           MMMMMMMMMMMMMMMMM^NZMMN+Z
   various particular Instruction Set Architectures.    MMMMMMMMMMMMMMM/.$MZM8O+
                                                         MMMMMMMMMMMMMM7..$MNDM+
   To compile this module, first load and compile:        MMDMMMMMMMMMZ7..$DM$77
   * Picinae_core                                          MMMMMMM+MMMZ7..7ZM~++
   * Picinae_theory                                         MMMMMMMMMMM7..ZNOOMZ
   * Picinae_statics                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_finterp                                          MDMMMMMMMO.7MDM7M+
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

Require Import Picinae_core.
Require Import Picinae_theory.
Require Import Picinae_statics.
Require Import Picinae_finterp.
Require Import Picinae_simplifier_base.
From Stdlib Require Import NArith.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Structures.Equalities.
Open Scope N.

(* getmem and setmem can potentially explode out of control when Coq checks
   term convertibility, so set them Opaque by default for most proofs. (The
   user can use the Transparent command to undo this, but be cautious!) *)
Global Opaque memsize.
Global Opaque getmem.
Global Opaque setmem.

Module Picinae_ISA
  (IL: PICINAE_IL)
  (PSIMPL: PSIMPL_BASE IL)
  (TIL: PICINAE_THEORY IL)
  (SIL: PICINAE_STATICS IL TIL)
  (FIL: PICINAE_FINTERP IL TIL SIL).

Import IL.
Import PSIMPL.

Import TIL.
Import SIL.
Import FIL.

Ltac simpl_memaccs H := fail "ISA definition failed to supply a simpl_memaccs tactic".

(* The user can ignore all assigned values to specified variables by
   redefining ignore_vars.  Example:
     Ltac ignore_vars v ::= constr:(match v with R_EAX => true | _ => false end).
 *)
Ltac ignore_vars v := constr:(false).
Ltac abstract_ignored_vars H :=
  repeat match type of H with context [ update ?s ?v ?n ] =>
    let b := ltac:(ignore_vars v) in
    lazymatch eval cbv in b with true =>
      tryif is_var n then fail else
      let tmp := fresh "n" in
      pose (tmp := n);
      change (update s v n) with (update s v tmp) in H;
      clearbody tmp
    | _ => fail
    end
  end.

Ltac generalize_trace :=
  lazymatch goal with
  | [ UT: unterminated ?xp (?xs'::?xs1::?t1++?xs0::?t)
      |- nextinv ?p ?Invs ?xp ?b (?xs'::?xs1::?t1++?xs0::?t) ] =>
    revert UT;
    change (unterminated xp (xs'::(xs1::t1)++(xs0::t)) ->
            nextinv p Invs xp b (xs'::(xs1::t1)++(xs0::t)));
    let t' := fresh t1 in generalize (xs1::t1); intros t' UT; clear t1; rename t' into t1
  | [ UT: unterminated ?xp (?xs'::?xs1::?xs0::?t)
      |- nextinv ?p ?Invs ?xp ?b (?xs'::?xs1::?xs0::?t) ] =>
    revert UT;
    change (unterminated xp (xs'::(xs1::nil)++(xs0::t)) ->
            nextinv p Invs xp b (xs'::(xs1::nil)++(xs0::t)));
    let t' := fresh "t" in generalize (xs1::nil); intros t' UT
  | [ |- nextinv ?p ?Invs ?xp ?b (?xs'::?xs1::?t1++?xs0::?t) ] =>
    change (nextinv p Invs xp b (xs'::(xs1::t1)++(xs0::t)));
    let t' := fresh t1 in generalize (xs1::t1); intro t'; clear t1; rename t' into t1
  | [ |- nextinv ?p ?Invs ?xp ?b (?xs'::?xs1::?xs0::?t) ] =>
    change (nextinv p Invs xp b (xs'::(xs1::nil)++(xs0::t)));
    let t' := fresh "t" in generalize (xs1::nil); intro t'
  end.

(* Syntax: generalize_frame m as x
   Result: Find any goal expressions of the form m[a1:=u1]...[an:=un] where
   a1..an are adjacent memory addresses, and compact them to expressions
   of the form m[a:=x], where a=min(a1,...,an) and x is a fresh proof variable.
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

(* Symbolically evaluate one machine instruction for one step, and simplify
   the resulting Coq expressions. *)
Ltac ISA_step_and_simplify_ltac1 XS :=
  step_stmt XS;
  abstract_ignored_vars XS;
  psimpl_hyp_ltac1 XS;
  simpl_memaccs XS;
  destruct_memaccs XS;
  try generalize_trace.

(* Introduce automated machinery for verifying a machine code subroutine
   (or collection of subroutines) by (1) defining a set of Floyd-Hoare
   invariants (including pre- and post-conditions) and (2) proving that
   symbolically executing the program starting at any invariant point in a
   state that satisfies the program until the next invariant point always
   yields a state that satisfies the reached invariant.  This proves partial
   correctness of the subroutine. *)

(* Some versions of Coq check injection-heavy proofs very slowly (at Qed).
   This slow-down can be avoided by sequestering prevalent injections into
   lemmas, as we do here. *)
Remark inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
                      Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

(* Simplify (exitof a x) without expanding a. *)
Remark exitof_none a: exitof a None = Addr a. Proof. exact eq_refl. Qed.
Remark exitof_some a x: exitof a (Some x) = x. Proof. exact eq_refl. Qed.

(* If asked to step the computation when we're already at an invariant point,
   just make the proof goal be the invariant. *)
Ltac ISA_invhere_ltac1 :=
  eapply nextinv_here; [ reflexivity | hnf; psimpl_goal_ltac1 ].

(* If we're not at an invariant, symbolically interpret the program for one
   machine language instruction.  (The user can use "do" or "repeat" tactics
   to step through many instructions, but often it is wiser to pause and do
   some manual simplification of the state at various points.) *)
Ltac ISA_invseek_ltac1 :=
  eapply NIStep; [reflexivity|reflexivity|];
  let c := fresh "c" in let s := fresh "s" in let x := fresh "x" in let XS := fresh "XS" in
  intros c s x XS;
  ISA_step_and_simplify_ltac1 XS;
  repeat lazymatch type of XS with
         | reset_temps _ s = _ /\ x = _ =>
             try clear c; destruct XS as [XS ?]; subst x;
             try (let rt := fresh in set (rt := reset_temps _ _) at 1;
                  psimpl_hyp_ltac1 rt; subst rt;
                  rewrite XS; clear XS; try clear s)
         | exec_stmt _ _ (if ?c then _ else _) _ _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ISA_step_and_simplify_ltac1 XS
         | exec_stmt _ _ (Seq (if ?c then _ else _) _) _ _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             ISA_step_and_simplify_ltac1 XS
         | exec_stmt _ _ (N.iter _ _ _) _ _ _ => fail
         | _ => ISA_step_and_simplify_ltac1 XS
         end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  repeat match goal with [ x:N |- _ ] => clear x end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

(* Clear any stale memory-access hypotheses (arising from previous computation
   steps) and either step to the next machine instruction (if we're not at an
   invariant) or produce an invariant as a proof goal. *)
Ltac ISA_step_ltac1 :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ ISA_invseek_ltac1; try ISA_invhere_ltac1 | ISA_invhere_ltac1 ].

(* Ltac2 owns sequencing, branching, and backtracking.  Reflective
   computations and ISA/user hooks remain explicit Ltac1 boundaries. *)
Ltac2 isa_step_stmt (xs : ident) :=
  let h := Ltac1.of_ident xs in
  lazy_match! Constr.type (Control.hyp xs) with
  | exec_stmt _ _ _ _ _ _ =>
      ltac1:(h |- populate_varlist h) h;
      Control.dispatch
      [ (fun () =>
          ltac1:(h |- step_precheck h; eapply reduce_stmt in h) h;
          Control.dispatch
          [ (fun () =>
              let unknown := Fresh.in_goal @unknown in
              let u1 := Ltac1.of_ident unknown in
              ltac1:(h u |- destruct h as [u h]; compute in h) h u1;
              let u := Control.hyp unknown in
              repeat (match! Constr.type (Control.hyp xs) with
              | context [?f ?index] =>
                  if Constr.equal f u then () else fail;
                  let n := Fresh.in_goal @n in
                  ltac1:(h u i n |- set (n:=u i) in h)
                    h u1 (Ltac1.of_constr index) (Ltac1.of_ident n);
                  Std.clearbody [n]
              end);
              try (Std.clear [unknown]))
          ; (fun () => reflexivity) ];
          ltac1:(h |- cbv beta match delta [noe_setop noe_typop] in h) h)
      ; (fun () => reflexivity) ]
  | _ => Control.zero (Tactic_failure (Some
      (Message.of_string "Hypothesis is not of the form (exec_stmt ...)")))
  end.

Ltac2 isa_abstract_ignored_vars (xs : ident) :=
  let h := Ltac1.of_ident xs in
  repeat (match! Constr.type (Control.hyp xs) with
  | context [update ?s ?v ?n] =>
      ltac1:(v n |- let b := ltac:(ignore_vars v) in
        lazymatch eval cbv in b with
        | true => tryif is_var n then fail else idtac
        | _ => fail
        end) (Ltac1.of_constr v) (Ltac1.of_constr n);
      let tmp := Fresh.in_goal @n in
      ltac1:(h s v n tmp |- pose (tmp:=n);
        change (update s v n) with (update s v tmp) in h)
        h (Ltac1.of_constr s) (Ltac1.of_constr v)
        (Ltac1.of_constr n) (Ltac1.of_ident tmp);
      Std.clearbody [tmp]
  end).

Ltac2 rec isa_split_memaccs (accs : ident) :=
  let h := Ltac1.of_ident accs in
  lazy_match! Constr.type (Control.hyp accs) with
  | ?p /\ _ =>
      first
      [ ltac1:(p |- lazymatch goal with [ _ : p |- _ ] => idtac end)
          (Ltac1.of_constr p);
        ltac1:(h |- apply proj2 in h) h
      | let acc := Fresh.in_goal @ACC in
        ltac1:(h acc |- destruct h as [acc h]) h (Ltac1.of_ident acc) ];
      isa_split_memaccs accs
  | True => Std.clear [accs]
  | _ => let acc := Fresh.in_goal @ACC in Std.rename [(accs, acc)]
  end.

Ltac2 isa_destruct_memaccs (xs : ident) :=
  let accs := Fresh.in_goal @ACCs in
  ltac1:(xs accs |- destruct xs as [xs accs])
    (Ltac1.of_ident xs) (Ltac1.of_ident accs);
  isa_split_memaccs accs.

Ltac2 isa_step_and_simplify (xs : ident) :=
  let h := Ltac1.of_ident xs in
  isa_step_stmt xs;
  Control.enter (fun () =>
    isa_abstract_ignored_vars xs;
    ltac1:(h |- psimpl_hyp h) h;
    ltac1:(h |- simpl_memaccs h) h;
    isa_destruct_memaccs xs;
    Control.enter (fun () => try ltac1:(generalize_trace))).

Ltac2 isa_invhere () :=
  eapply nextinv_here > [ reflexivity | hnf; ltac1:(psimpl_goal) ].

Ltac2 isa_invseek () :=
  eapply NIStep > [ reflexivity | reflexivity | ];
  let c := Fresh.in_goal @c in let s := Fresh.in_goal @s in
  let x := Fresh.in_goal @x in let xs := Fresh.in_goal @XS in
  let c1 := Ltac1.of_ident c in let s1 := Ltac1.of_ident s in
  let x1 := Ltac1.of_ident x in let h := Ltac1.of_ident xs in
  ltac1:(c s x h |- intros c s x h) c1 s1 x1 h;
  isa_step_and_simplify xs;
  Control.enter (fun () =>
    repeat (lazy_match! Constr.type (Control.hyp xs) with
    | reset_temps _ _ = _ /\ _ = _ =>
        ltac1:(c s x h |- try clear c; destruct h as [h ?]; subst x;
          try (let rt := fresh in set (rt := reset_temps _ _) at 1;
            psimpl_hyp rt; subst rt; rewrite h; clear h; try clear s)) c1 s1 x1 h
    | exec_stmt _ _ (if ?b then _ else _) _ _ _ =>
        let bc := Fresh.in_goal @BC in
        ltac1:(b bc |- destruct b eqn:bc) (Ltac1.of_constr b) (Ltac1.of_ident bc);
        Control.enter (fun () => isa_step_and_simplify xs)
    | exec_stmt _ _ (Seq (if ?b then _ else _) _) _ _ _ =>
        let bc := Fresh.in_goal @BC in
        ltac1:(b bc |- destruct b eqn:bc) (Ltac1.of_constr b) (Ltac1.of_ident bc);
        Control.enter (fun () => isa_step_and_simplify xs)
    | exec_stmt _ _ (N.iter _ _ _) _ _ _ => fail
    | _ => isa_step_and_simplify xs
    end);
    Control.enter (fun () =>
      try ltac1:(lazymatch goal with |- context [exitof (N.add ?m ?n)] => simpl (N.add m n) end);
      repeat (match! goal with [ h : N |- _ ] => Std.clear [h] end);
      try (first [ rewrite exitof_none | rewrite exitof_some ]))).

Ltac2 isa_step () :=
  repeat (match! goal with [ h : MemAcc _ _ _ _ _ |- _ ] => Std.clear [h] end);
  first [ isa_invseek (); Control.enter (fun () => try (isa_invhere ()))
        | isa_invhere () ].

Ltac ISA_step_and_simplify xs :=
  let f := ltac2:(xs |- isa_step_and_simplify (picinae_hyp_ident xs)) in f xs.
Ltac ISA_invhere := ltac2:(isa_invhere ()).
Ltac ISA_invseek := ltac2:(isa_invseek ()).
Ltac ISA_step := ltac2:(isa_step ()).

End Picinae_ISA.

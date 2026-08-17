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
   Static Semantics Theory module:                     MMMMMMMMMMMMMMMMM^NZMMN+Z
   * boundedness of modular arithmetic outputs,         MMMMMMMMMMMMMMM/.$MZM8O+
   * type-preservation of operational semantics,         MMMMMMMMMMMMMM7..$MNDM+
   * progress of memory-safe programs, and                MMDMMMMMMMMMZ7..$DM$77
   * proof of type-safety.                                 MMMMMMM+MMMZ7..7ZM~++
                                                            MMMMMMMMMMM7..ZNOOMZ
   To compile this module, first load and compile:           MMMMMMMMMM$.$MOMO=7
   * Picinae_core                                             MDMMMMMMMO.7MDM7M+
   * Picinae_theory                                            ZMMMMMMMM.$MM8$MN
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

Require Import Picinae_theory.
Require Import NArith.
Require Import ZArith.
Require Import Program.Equality.
Require Import FunctionalExtensionality.



Section HasUpperBound.

(* Define the has-upper-bound property of pairs of partial functions, and
   prove some general sufficiency conditions for having the property. *)

Definition has_upper_bound {A B} (f g: A -> option B) :=
  forall x y z, f x = Some y -> g x = Some z -> y = z.

Lemma hub_refl:
  forall A B (f: A -> option B), has_upper_bound f f.
Proof.
  unfold has_upper_bound. intros.
  rewrite H0 in H. inversion H.
  reflexivity.
Qed.

Lemma hub_sym:
  forall A B (f g: A -> option B), has_upper_bound f g -> has_upper_bound g f.
Proof.
  intros. intros x gx fx H1 H2. symmetry. eapply H; eassumption.
Qed.

Lemma hub_subset:
  forall A B (f g f' g': A -> option B) (HUB: has_upper_bound f g)
         (SS1: f' ⊆ f) (SS2: g' ⊆ g),
  has_upper_bound f' g'.
Proof.
  unfold has_upper_bound. intros. eapply HUB.
    apply SS1. eassumption.
    apply SS2. assumption.
Qed.

Lemma hub_update {A B} {eq:EqDec A}:
  forall (f g: A -> option B) x y (HUB: has_upper_bound f g),
  has_upper_bound (f[x:=y]) (g[x:=y]).
Proof.
  unfold has_upper_bound. intros. destruct (x0 == x).
    subst. rewrite update_updated in H,H0. rewrite H0 in H. inversion H. reflexivity.
    rewrite update_frame in H,H0 by assumption. eapply HUB; eassumption.
Qed.

End HasUpperBound.



Module Type PICINAE_STATICS_DEFS (IL: PICINAE_IL) (TIL: PICINAE_THEORY IL).

(* This module proves that the semantics of the IL are type-safe in the sense that
   programs whose constants have proper bitwidths never produce variable values or
   expressions that exceed their declared bitwidths as they execute.  This is
   important for (1) providing assurance that the semantics are correctly defined,
   and (2) proving practical results that rely upon the assumption that machine
   registers and memory contents always have values of appropriate bitwidths. *)

Import IL.
Import TIL.
Open Scope N.

(* Memory is well-typed if it is 2^w bytes concatenated. *)
Definition welltyped_memory (m:memory) (w:bitwidth) : Prop :=
  m < memsize w.

(* Type-check an expression in a typing context, returning its value type. *)
Inductive hasmtyp_exp (c:mtypctx): exp -> typ -> Prop :=
| MTVar v t (CV: c v = Some t): hasmtyp_exp c (Var v) t
| MTWord n w : hasmtyp_exp c (Word n w) NumT
| MTLoad e1 e2 en len
        (M1: hasmtyp_exp c e1 MemT) (T2: hasmtyp_exp c e2 NumT):
        hasmtyp_exp c (Load e1 e2 en len) NumT
| MTStore e1 e2 e3 en len
         (M1: hasmtyp_exp c e1 MemT) (T2: hasmtyp_exp c e2 NumT)
         (M3: hasmtyp_exp c e3 NumT):
         hasmtyp_exp c (Store e1 e2 e3 en len) MemT
| MTBinOp bop e1 e2
         (M1: hasmtyp_exp c e1 NumT) (T2: hasmtyp_exp c e2 NumT):
         hasmtyp_exp c (BinOp bop e1 e2) NumT
| MTUnOp uop e (T1: hasmtyp_exp c e NumT):
        hasmtyp_exp c (UnOp uop e) NumT
| MTCast ct w' e (T1: hasmtyp_exp c e NumT):
        hasmtyp_exp c (Cast ct w' e) NumT
| MTLet v e1 e2 t1 t2
       (M1: hasmtyp_exp c e1 t1) (T2: hasmtyp_exp (c[v:=Some t1]) e2 t2):
       hasmtyp_exp c (Let v e1 e2) t2
| MTUnknown w: hasmtyp_exp c (Unknown w) NumT
| MTIte e1 e2 e3 t'
       (M1: hasmtyp_exp c e1 NumT) (T2: hasmtyp_exp c e2 t') (T3: hasmtyp_exp c e3 t'):
       hasmtyp_exp c (Ite e1 e2 e3) t'
| MTExtract n1 n2 e1
           (M1: hasmtyp_exp c e1 NumT):
           hasmtyp_exp c (Extract n1 n2 e1) NumT
| MTConcat e1 e2
          (M1: hasmtyp_exp c e1 NumT) (T2: hasmtyp_exp c e2 NumT):
          hasmtyp_exp c (Concat e1 e2) NumT.

(* Static semantics for statements:
   Defining a sound statement typing semantics is tricky for two reasons:

   (1) There are really two kinds of IL variables: (a) those that encode cpu state
   (which are always initialized, and whose types are fixed), and (b) temporary
   variables introduced during lifting to IL (which are not guaranteed to be
   initialized, and whose types may vary across different instruction IL blocks.

   We therefore use separate contexts c0 and c to model the two kinds.  Context
   c0 models the cpu state variables, while c models all variables.  Context c
   therefore usually subsumes c0, and is always consistent with c0 (i.e., the
   join of c and c0 is always a valid context).  This consistency is enforced
   by checking assigned value types against c0 at every Move, but only updating c.

   (2) Since variable initialization states are mutable, we need static rules
   that support meets and joins of contexts.  However, a general cut rule is
   cumbersome because it hampers syntax-directed type-safety proofs.  We therefore
   instead introduce a weakening option within each syntax-directed typing rule.
   This avoids superfluous double-cuts by in-lining a single cut into each rule. *)

Inductive hasmtyp_stmt (c0 c:mtypctx): stmt -> mtypctx -> Prop :=
| MTNop c' (SS: c' ⊆ c): hasmtyp_stmt c0 c Nop c'
| MTMove v t e c' (CV: c0 v = None \/ c0 v = Some t) (TE: hasmtyp_exp c e t) (SS: c' ⊆ c[v:=Some t]):
    hasmtyp_stmt c0 c (Move v e) c'
| MTJmp e c' (TE: hasmtyp_exp c e NumT) (SS: c' ⊆ c): hasmtyp_stmt c0 c (Jmp e) c'
| MTExn ex c' (SS: c' ⊆ c): hasmtyp_stmt c0 c (Exn ex) c'
| MTSeq q1 q2 c1 c2 c'
       (TS1: hasmtyp_stmt c0 c q1 c1) (TS2: hasmtyp_stmt c0 c1 q2 c2) (SS: c' ⊆ c2):
    hasmtyp_stmt c0 c (Seq q1 q2) c'
| MTIf e q1 q2 c2 c'
      (TE: hasmtyp_exp c e NumT)
      (TS1: hasmtyp_stmt c0 c q1 c2) (TS2: hasmtyp_stmt c0 c q2 c2) (SS: c' ⊆ c2):
    hasmtyp_stmt c0 c (If e q1 q2) c'
| MTRep e q c' c''
    (TE: hasmtyp_exp c e NumT) (SS: c' ⊆ c) (TS: hasmtyp_stmt c0 c' q c') (SS: c'' ⊆ c'):
    hasmtyp_stmt c0 c (Rep e q) c''.

(* A program is well-typed if all its statements are well-typed. *)
Definition wellmtyped_prog (c0:mtypctx) (p:program) : Prop :=
  forall s a, match p s a with None => True | Some (_,q) =>
                exists c', hasmtyp_stmt c0 c0 q c' end.

(* Context c "models" a store s trivially because numeric and memory
   types are erased. *)
Definition mmodels (c:mtypctx) (s:store) : Prop := True.

Theorem models_update:
  forall c s x y,
  mmodels c (update s x y).
Proof.
  intros; exact I.
Qed.

(* We next define an effective procedure for type-checking expressions and
   statements.  This procedure is sound but incomplete: it can determine well-
   typedness of most statements, but there exist well-typed statements for
   which it cannot decide their well-typedness.  This happens because the
   formal semantics above allow arbitrary ("magic") context-weakening within
   each well-typedness rule, wherein an effective procedure must guess
   the greatest-lower-bound context sufficient to type-check the remainder of
   the statement.  The procedure below makes the following guesses, which
   suffice to prove well-typedness for IL encodings of all ISAs so far:
     (1) If-contexts are weakened to the lattice-meet of the two branches.
     (2) Rep-contexts are weakened to the input context, to get a fixpoint.
     (3) No other contexts are weakened.
   If these guesses cannot typecheck some statements in your ISA, consider
   changing your lifter for your ISA to produce IL encodings whose variable
   types are not path-sensitive. *)

(* Type-check an expression in a given typing context. *)
Fixpoint mtypchk_exp (e:exp) (c:mtypctx): option typ :=
  match e with
  | Var v => c v
  | Word n w => Some NumT
  | Load e1 e2 _ len =>
      match mtypchk_exp e1 c, mtypchk_exp e2 c with
      | Some MemT, Some NumT => Some NumT
      | _, _ => None
      end
  | Store e1 e2 e3 _ len =>
      match mtypchk_exp e1 c, mtypchk_exp e2 c, mtypchk_exp e3 c with
      | Some MemT, Some NumT, Some NumT => Some MemT
      | _, _, _ => None
      end
  | BinOp bop e1 e2 =>
      match mtypchk_exp e1 c, mtypchk_exp e2 c with
      | Some NumT, Some NumT => Some NumT
      | _, _ => None
      end
  | UnOp uop e1 => match mtypchk_exp e1 c with Some NumT => Some NumT
                                            | _ => None end
  | Cast ct w' e1 =>
      match mtypchk_exp e1 c with Some NumT => Some NumT
      | _ => None
      end
  | Let v e1 e2 =>
      match mtypchk_exp e1 c with Some w => mtypchk_exp e2 (c[v:=Some w])
                               | None => None end
  | Unknown w => Some NumT
  | Ite e1 e2 e3 =>
      match mtypchk_exp e1 c, mtypchk_exp e2 c, mtypchk_exp e3 c with
      | Some NumT, Some w2, Some w3 => if w2 == w3 then Some w2 else None
      | _, _, _ => None
      end
  | Extract n1 n2 e1 =>
      match mtypchk_exp e1 c with
      | Some NumT => Some NumT
      | _ => None
      end
  | Concat e1 e2 =>
      match mtypchk_exp e1 c, mtypchk_exp e2 c with
      | Some NumT, Some NumT => Some NumT
      | _, _ => None
      end
  end.


(* Compute the meet of two input contexts. *)
Definition mtypctx_meet {B:Type} {E:EqDec B} (c1 c2:var -> option B) v :=
  match c1 v, c2 v with
  | Some w1, Some w2 => if w1 == w2 then Some w1 else None
  | _, _ => None
  end.

(* Type-check a statement given a frame-context and initial context. *)
Fixpoint mtypchk_stmt (q:stmt) (c0 c:mtypctx): option mtypctx :=
  match q with
  | Nop => Some c
  | Move v e =>
      match mtypchk_exp e c with
      | Some t => match c0 v with
                  | None => Some (c[v:=Some t])
                  | Some t' => if t == t' then Some (c[v:=Some t]) else None
                  end
      | None => None
      end
  | Jmp e => match mtypchk_exp e c with Some NumT => Some c | _ => None end
  | Exn _ => Some c
  | Seq q1 q2 => match mtypchk_stmt q1 c0 c with
                 | None => None
                 | Some c2 => mtypchk_stmt q2 c0 c2
                 end
  | If e q1 q2 =>
      match mtypchk_exp e c, mtypchk_stmt q1 c0 c, mtypchk_stmt q2 c0 c with
      | Some NumT, Some c1, Some c2 => Some (mtypctx_meet c1 c2)
      | _, _, _ => None
      end
  | Rep e q1 =>
      match mtypchk_exp e c, mtypchk_stmt q1 c c with
      | Some NumT, Some _ => Some c
      | _, _ => None
      end
  end.

End PICINAE_STATICS_DEFS.



Module Type PICINAE_STATICS (IL: PICINAE_IL) (TIL: PICINAE_THEORY IL).

Import IL.
Import TIL.
Include PICINAE_STATICS_DEFS IL TIL.

(* These short lemmas are helpful when automating type-checking in tactics. *)

(* Expression types are unique. *)
Parameter hasmtyp_exp_unique:
  forall e c1 c2 t1 t2 (HUB: has_upper_bound c1 c2)
         (TE1: hasmtyp_exp c1 e t1) (TE2: hasmtyp_exp c2 e t2),
  t1 = t2.

(* Expression typing contexts can be weakened. *)
Parameter hasmtyp_exp_weaken:
  forall c1 c2 e t (TE: hasmtyp_exp c1 e t) (SS: c1 ⊆ c2),
  hasmtyp_exp c2 e t.

(* Statement types can be weakened. *)
Parameter hasmtyp_stmt_weaken:
  forall c0 c1 c2 c' q (TS: hasmtyp_stmt c0 c1 q c') (SS: c1 ⊆ c2),
  hasmtyp_stmt c0 c2 q c'.
Parameter hasmtyp_stmt_weaken':
  forall c0 c c' c'' q (TS: hasmtyp_stmt c0 c q c') (SS: c'' ⊆ c'),
  hasmtyp_stmt c0 c q c''.

(* Statement types agree (though not necessarily unique). *)
Parameter hasmtyp_stmt_compat:
  forall c0 q c1 c2 c1' c2'
         (HUB: has_upper_bound c1 c2)
         (TS1: hasmtyp_stmt c0 c1 q c1') (TS2: hasmtyp_stmt c0 c2 q c2'),
  has_upper_bound c1' c2'.

(* Statement frame contexts can be weakened. *)
Parameter hasmtyp_stmt_frame_weaken:
  forall c0 c0' q c c' (TS: hasmtyp_stmt c0 c q c') (SS: c0' ⊆ c0),
  hasmtyp_stmt c0' c q c'.

(* We next prove type-safety of the IL with respect to the above static semantics.
   In general, interpretation of an arbitrary, unchecked IL program can fail
   (i.e., exec_prog is underivable) for only the following reasons:

   (1) memory access violation ("mem_readable" or "mem_writable" is falsified), or

   (2) a type-mismatch occurs (e.g., arithmetic applied to memory state values).

   Type-safety proves that if type-checking succeeds, then the only reachable
   stuck-states are case (1).  That is, runtime type-mismatches are precluded,
   and all computed values have proper types.

   This property is important in the context of formal validation of native
   code programs because proofs about such code typically rely upon the types
   of values that each cpu state element can hold (e.g., 32-bit registers always
   contain 32-bit numbers).  Proving type-safety allows us to verify these
   basic properties within other proofs by first running the type-checker (as a
   tactic), and then applying the type-soundness theorem(s). *)


(* Weakening the typing context preserves the modeling relation. *)
Parameter models_subset:
  forall c s c' (M: mmodels c s) (SS: c' ⊆ c),
  mmodels c' s.

(* The expression type-checker is sound. *)
Parameter mtypchk_exp_sound:
  forall e c t, mtypchk_exp e c = Some t -> hasmtyp_exp c e t.

(* The meet of two contexts is bounded above by the contexts. *)
Parameter mtypctx_meet_subset:
  forall {B:Type} {E:EqDec B} c1 c2, mtypctx_meet c1 c2 ⊆ c1.

(* Context-meet is commutative. *)
Parameter mtypctx_meet_comm:
  forall {B} {E:EqDec B} c1 c2, mtypctx_meet c1 c2 = mtypctx_meet c2 c1.

(* Context-meet computes the greatest of the lower bounds of the inputs. *)
Parameter mtypctx_meet_lowbound:
  forall {B} {E:EqDec B} c0 c1 c2 (SS1: c0 ⊆ c1) (SS2: c0 ⊆ c2), c0 ⊆ mtypctx_meet c1 c2.

(* The type-checker preserves the frame context. *)
Parameter mtypchk_stmt_mono:
  forall c0 q c c' (TS: mtypchk_stmt q c0 c = Some c') (SS: c0 ⊆ c), c0 ⊆ c'.

(* The statement type-checker is sound. *)
Parameter mtypchk_stmt_sound:
  forall q c0 c c' (SS: c0 ⊆ c) (TS: mtypchk_stmt q c0 c = Some c'),
  hasmtyp_stmt c0 c q c'.

(* Create a theorem that transforms a type-safety goal into an application of
   the type-checker.  This allows type-safety goals to be solved by any of
   Coq's fast reduction tactics, such as vm_compute or native_compute. *)
Parameter mtypchk_stmt_compute:
  forall q c (TS: if mtypchk_stmt q c c then True else False),
  exists c', hasmtyp_stmt c c q c'.

(* Attempt to automatically solve a goal of the form (welltyped_prog c p).
   Statements in p that cannot be type-checked automatically (using context-
   meets at conditionals and the incoming context as the fixpoint of loops)
   are left as subgoals for the user to solve.  For most ISAs, this should
   not happen; the algorithm should fully solve all the goals. *)
Ltac Picinae_mtypecheck :=
  lazymatch goal with [ |- wellmtyped_prog _ _ ] =>
    let s := fresh "s" in let a := fresh "a" in
    intros s a;
    destruct a as [|a]; repeat first [ exact I | destruct a as [a|a|] ];
    try (apply mtypchk_stmt_compute; vm_compute; exact I)
  | _ => fail "goal is not of the form (welltyped_prog c p)"
  end.

End PICINAE_STATICS.


Module PicinaeMStatics (IL: PICINAE_IL) (TIL: PICINAE_THEORY IL): PICINAE_STATICS IL TIL.

Import IL.
Import TIL.
Include PICINAE_STATICS_DEFS IL TIL.

Lemma hasmtyp_binop:
  forall bop c e1 e2
         (T1: hasmtyp_exp c e1 NumT) (T2: hasmtyp_exp c e2 NumT),
  hasmtyp_exp c (BinOp bop e1 e2) NumT.
Proof.
  intros. econstructor; assumption.
Qed.

Lemma hasmtyp_extract:
  forall c n1 n2 e1
         (T1: hasmtyp_exp c e1 NumT),
  hasmtyp_exp c (Extract n1 n2 e1) NumT.
Proof.
  intros. econstructor; assumption.
Qed.

Lemma hasmtyp_concat:
  forall c e1 e2
         (T1: hasmtyp_exp c e1 NumT) (T2: hasmtyp_exp c e2 NumT),
  hasmtyp_exp c (Concat e1 e2) NumT.
Proof.
  intros. econstructor; assumption.
Qed.

Theorem hasmtyp_exp_unique:
  forall e c1 c2 w1 w2 (HUB: has_upper_bound c1 c2)
         (TE1: hasmtyp_exp c1 e w1) (TE2: hasmtyp_exp c2 e w2),
  w1 = w2.
Proof.
  intros. revert c1 c2 w1 w2 HUB TE1 TE2. induction e; intros;
  inversion TE1; inversion TE2; clear TE1 TE2; subst;
  try reflexivity.

  (* Var *)
  eapply HUB; eassumption.

  (* ? *)
  specialize (IHe1 _ _ _ _ HUB M1 M0); subst t0. apply (hub_update _ _ v (Some t1)) in HUB.
  specialize (IHe2 _ _ _ _ HUB T2 T0); now subst.

  (* ? *)
  specialize (IHe2 _ _ _ _ HUB T2 T0); now subst.
Qed.

Theorem hasmtyp_exp_weaken:
  forall c1 c2 e t (TE: hasmtyp_exp c1 e t) (SS: c1 ⊆ c2),
  hasmtyp_exp c2 e t.
Proof.
  intros. revert c2 SS. dependent induction TE; intros; econstructor;
  try (try first [ apply IHTE | apply IHTE1 | apply IHTE2 | apply IHTE3 | apply SS ]; assumption).

  apply IHTE2. unfold update. intros v0 t CV. destruct (v0 == v).
    assumption.
    apply SS. assumption.
Qed.

Theorem hasmtyp_stmt_weaken':
  forall c0 c c' c'' q (TS: hasmtyp_stmt c0 c q c') (SS: c'' ⊆ c'),
  hasmtyp_stmt c0 c q c''.
Proof.
  intros. inversion TS; clear TS; subst;
  econstructor; first [ eassumption | transitivity c'; assumption ].
Qed.

Theorem hasmtyp_stmt_weaken:
  forall c0 c1 c2 c' q (TS: hasmtyp_stmt c0 c1 q c') (SS: c1 ⊆ c2),
  hasmtyp_stmt c0 c2 q c'.
Proof.
  intros. revert c2 SS. dependent induction TS; intros;
  try solve [ econstructor; repeat first
  [ eassumption
  | eapply hasmtyp_exp_weaken; eassumption
  | apply pfsub_update; assumption
  | (apply IHTS1 + apply IHTS2); assumption
  | etransitivity; [eassumption|] ] ].

  econstructor.
    eapply hasmtyp_exp_weaken; eassumption.
    etransitivity; [|eassumption]. eassumption.
    apply IHTS. reflexivity.
    assumption.
Qed.

Theorem hasmtyp_stmt_compat:
  forall c0 q c1 c2 c1' c2'
         (HUB: has_upper_bound c1 c2)
         (TS1: hasmtyp_stmt c0 c1 q c1') (TS2: hasmtyp_stmt c0 c2 q c2'),
  has_upper_bound c1' c2'.
Proof.
  induction q; intros; inversion TS1; inversion TS2; clear TS1 TS2; subst;
  try solve [ apply (hub_subset _ _ _ _ _ _ HUB); assumption ].
    eapply hub_subset; [|eassumption..]. replace t0 with t.
      apply hub_update, HUB.
      eapply hasmtyp_exp_unique; eassumption.
    eapply IHq2.
      eapply IHq1; eassumption.
      eapply hasmtyp_stmt_weaken'. exact TS3. exact SS.
      eapply hasmtyp_stmt_weaken'. exact TS5. exact SS0.
    eapply hub_subset; [|eassumption..]. eapply IHq1; eassumption.
    eapply IHq; [eassumption| |];
      (eapply hasmtyp_stmt_weaken; [|eassumption]);
      eapply hasmtyp_stmt_weaken'; eassumption.
Qed.

Theorem hasmtyp_stmt_frame_weaken:
  forall c0 c0' q c c' (TS: hasmtyp_stmt c0 c q c') (SS: c0' ⊆ c0),
  hasmtyp_stmt c0' c q c'.
Proof.
  induction q; intros; inversion TS; subst.
    apply MTNop. assumption.
    eapply MTMove.
      specialize (SS v). destruct (c0' v).
        right. rewrite (SS t0 (eq_refl _)) in CV. destruct CV. discriminate. eassumption.
        left. reflexivity.
      exact TE.
      assumption.
    eapply MTJmp. exact TE. assumption.
    apply MTExn. assumption.
    eapply MTSeq.
      apply IHq1. exact TS1. exact SS.
      apply IHq2. exact TS2. exact SS.
      exact SS0.
    eapply MTIf.
      exact TE.
      apply IHq1. exact TS1. exact SS.
      apply IHq2. exact TS2. exact SS.
      exact SS0.
    eapply MTRep.
      exact TE.
      exact SS0.
      apply IHq. exact TS0. exact SS.
      exact SS1.
Qed.

Lemma models_subset:
  forall c s c' (M: mmodels c s) (SS: c' ⊆ c),
  mmodels c' s.
Proof.
  intros; exact I.
Qed.

Lemma models_reset_temps:
  forall s2 s1 (MDL: mmodels marchtyps s2), mmodels marchtyps (reset_temps s1 s2).
Proof.
  intros; exact I.
Qed.

Remark shiftl1_3pn:
  forall n, N.shiftl 1 (3+n) = 2^n*8.
Proof.
  intro. rewrite N.shiftl_1_l, N.pow_add_r, N.mul_comm. reflexivity.
Qed.

Theorem mtypchk_exp_sound:
  forall e c t, mtypchk_exp e c = Some t -> hasmtyp_exp c e t.
Proof.
  induction e; cbn [ mtypchk_exp ]; intros.

  (* Var *)
  apply MTVar. assumption.

  (* Word *)
  injection H; intro; subst. apply MTWord.

  (* Load *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (mtypchk_exp e1 c) as [[ | ]|]; try discriminate.
  destruct (mtypchk_exp e2 c) as [[ | ]|]; try discriminate.
  inversion H; subst.
  eapply MTLoad.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.

  (* Store *)
  specialize (IHe1 c). specialize (IHe2 c). specialize (IHe3 c).
  destruct (mtypchk_exp e1 c) as [[|]|]; try discriminate.
  destruct (mtypchk_exp e2 c) as [[|]|]; try discriminate.
  destruct (mtypchk_exp e3 c) as [[|]|]; try discriminate.
  inversion H; subst; clear H.
  apply MTStore.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
    apply IHe3. reflexivity.

  (* BinOp *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (mtypchk_exp e1 c) as [[|]|]; try discriminate.
  destruct (mtypchk_exp e2 c) as [[|]|]; try discriminate.
  inversion H; subst; clear H.
  apply MTBinOp.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.

  (* UnOp *)
  specialize (IHe c).
  destruct (mtypchk_exp e c) as [[|]|]; try discriminate.
  injection H; intro; subst.
  apply MTUnOp. apply IHe. reflexivity.

  (* Cast *)
  specialize (IHe c0).
  destruct (mtypchk_exp e c0) as [[|]|]; try discriminate.
  inversion H; subst; clear H.
  (eapply MTCast; eapply IHe; reflexivity).

  (* Let *)
  specialize (IHe1 c). destruct (mtypchk_exp e1 c); [|discriminate].
  eapply MTLet.
    apply IHe1. reflexivity.
    apply IHe2. assumption.

  (* Unknown *)
  injection H; intro; subst. apply MTUnknown.

  (* Ite *)
  specialize (IHe1 c). specialize (IHe2 c). specialize (IHe3 c).
  destruct (mtypchk_exp e1 c) as [[|]|]; try discriminate.
  destruct (mtypchk_exp e2 c) as [[|]|]; try discriminate;
  destruct (mtypchk_exp e3 c) as [[|]|]; try discriminate;
  injection H; intro; subst.
  eapply MTIte.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
    apply IHe3. reflexivity.
  eapply MTIte.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
    apply IHe3. reflexivity.

  (* Extract *)
  specialize (IHe c).
  destruct (mtypchk_exp e c) as [[|]|]; try discriminate.
  injection H; intro; subst.
  eapply MTExtract.
    apply IHe. reflexivity.

  (* Concat *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (mtypchk_exp e1 c) as [[|]|]; try discriminate.
  destruct (mtypchk_exp e2 c) as [[|]|]; try discriminate.
  injection H; intro; subst.
  apply MTConcat.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
Qed.

Lemma mtypctx_meet_subset {B} {E:EqDec B}:
  forall c1 c2, mtypctx_meet c1 c2 ⊆ c1.
Proof.
  intros c1 c2 v t H. unfold mtypctx_meet in H.
  destruct (c1 v) as [t1|]; [|discriminate].
  destruct (c2 v) as [t2|]; [|discriminate].
  destruct (t1 == t2). exact H. discriminate.
Qed.

Lemma mtypctx_meet_comm {B} {E:EqDec B}:
  forall c1 c2, mtypctx_meet c1 c2 = mtypctx_meet c2 c1.
Proof.
  intros. extensionality v. unfold mtypctx_meet.
  destruct (c1 v) as [w1|], (c2 v) as [w2|]; try reflexivity.
  destruct (w1 == w2).
    subst. destruct (w2 == w2). reflexivity. contradict n. reflexivity.
    destruct (w2 == w1). contradict n. symmetry. assumption. reflexivity.
Qed.

Lemma mtypctx_meet_lowbound {B} {E:EqDec B}:
  forall (c0 c1 c2:var->option B) (SS1: c0 ⊆ c1) (SS2: c0 ⊆ c2), c0 ⊆ mtypctx_meet c1 c2.
Proof.
  unfold "⊆", mtypctx_meet. intros.
  rewrite (SS1 _ _ H). rewrite (SS2 _ _ H).
  destruct (y == y); [|contradict n]; reflexivity.
Qed.

Lemma mtypchk_stmt_mono:
  forall c0 q c c' (TS: mtypchk_stmt q c0 c = Some c') (SS: c0 ⊆ c), c0 ⊆ c'.
Proof.
  induction q; simpl; intros.

  (* Nop *)
  injection TS; intro; subst. exact SS.

  (* Move *)
  destruct (mtypchk_exp e c) as [w|]; [|discriminate].
  destruct (c0 v) as [w'|] eqn:C0V.
    destruct (w == w').
      injection TS; intro; subst. intros v0 t0 H. destruct (v0 == v).
        subst v0. rewrite update_updated, <- C0V, <- H. reflexivity.
        rewrite update_frame by assumption. apply SS, H.
      discriminate.
    injection TS; intro; subst. intros v0 t0 H. destruct (v0 == v).
      subst v0. rewrite C0V in H. discriminate.
      rewrite update_frame by assumption. apply SS, H.

  (* Jmp *)
  destruct (mtypchk_exp e c) as [[|]|]; try discriminate.
  injection TS; intro; subst. exact SS.

  (* Exn *)
  injection TS; intro; subst. exact SS.

  (* Seq *)
  destruct (mtypchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  eapply IHq2. exact TS.
  eapply IHq1. exact TS1. exact SS.

  (* If *)
  destruct (mtypchk_exp e c) as [[|]|]; try discriminate.
  destruct (mtypchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  destruct (mtypchk_stmt q2 c0 c) as [c2|] eqn:TS2; [|discriminate].
  injection TS; intro; subst.
  apply mtypctx_meet_lowbound.
    eapply IHq1. exact TS1. exact SS.
    eapply IHq2. exact TS2. exact SS.

  (* Rep *)
  destruct (mtypchk_exp e c) as [[|]|]; try discriminate.
  destruct (mtypchk_stmt q c c) eqn:TS1; try discriminate.
  injection TS; intro; subst.
  exact SS.
Qed.

Theorem mtypchk_stmt_sound:
  forall q c0 c c' (SS: c0 ⊆ c) (TS: mtypchk_stmt q c0 c = Some c'),
  hasmtyp_stmt c0 c q c'.
Proof.
  induction q; intros; simpl in TS.

  (* Nop *)
  injection TS; intro; subst. apply MTNop. reflexivity.

  (* Move *)
  destruct (mtypchk_exp e c) as [|] eqn:TE; try discriminate.
  destruct (c0 v) as [t'|] eqn:C0V.
    destruct (t==t'); try discriminate. inversion TS; subst.
    econstructor. right; eassumption. apply mtypchk_exp_sound; assumption. reflexivity.

    inversion TS; subst. econstructor. left; assumption. apply mtypchk_exp_sound. eassumption. reflexivity.

  (* Jmp *)
  destruct (mtypchk_exp e c) as [[|]|] eqn:TE; try discriminate.
  injection TS; intro; subst.
  eapply MTJmp. apply mtypchk_exp_sound. exact TE. reflexivity.

  (* Exn *)
  injection TS; intro; subst. apply MTExn. reflexivity.

  (* Seq *)
  specialize (IHq1 c0 c). destruct (mtypchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  specialize (IHq2 c0 c1). destruct (mtypchk_stmt q2 c0 c1); [|discriminate].
  injection TS; clear TS; intro; subst.
  eapply MTSeq.
    apply IHq1. exact SS. reflexivity.
    apply IHq2. eapply mtypchk_stmt_mono; eassumption. reflexivity. reflexivity.

  (* If *)
  destruct (mtypchk_exp e c) as [[|]|] eqn:TE; try discriminate.
  destruct (mtypchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  destruct (mtypchk_stmt q2 c0 c) as [c2|] eqn:TS2; [|discriminate].
  injection TS; clear TS; intro; subst.
  eapply MTIf.
    apply mtypchk_exp_sound. exact TE.
    eapply hasmtyp_stmt_weaken'.
      apply IHq1. exact SS. exact TS1.
      apply mtypctx_meet_subset.
    eapply hasmtyp_stmt_weaken'.
      apply IHq2. exact SS. exact TS2.
      rewrite mtypctx_meet_comm. apply mtypctx_meet_subset.
    reflexivity.

  (* Rep *)
  destruct (mtypchk_exp e c) as [[|]|] eqn:TE; try discriminate.
  specialize (IHq c c). destruct (mtypchk_stmt q c c) as [c1|] eqn:TS1; [|discriminate].
  injection TS; clear TS; intro; subst.
  eapply MTRep.
    apply mtypchk_exp_sound. exact TE.
    reflexivity.
    eapply hasmtyp_stmt_frame_weaken; [|exact SS]. eapply hasmtyp_stmt_weaken'.
      apply IHq. reflexivity. reflexivity.
      eapply mtypchk_stmt_mono. exact TS1. reflexivity.
    reflexivity.
Qed.

Corollary mtypchk_stmt_compute:
  forall q c (TS: if mtypchk_stmt q c c then True else False),
  exists c', hasmtyp_stmt c c q c'.
Proof.
  intros. destruct (mtypchk_stmt q c c) as [c'|] eqn:TS1.
    exists c'. apply mtypchk_stmt_sound. reflexivity. exact TS1.
    contradict TS.
Qed.

End PicinaeMStatics.

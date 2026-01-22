(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2025 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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

(* Type-check an expression in a typing context, returning its bitwidth. *)
Inductive hastyp_exp (c:typctx): exp -> bitwidth -> Prop :=
| TVar v w (CV: c v = Some w): hastyp_exp c (Var v) w
| TWord n w (LT: n < 2^w): hastyp_exp c (Word n w) w
| TLoad e1 e2 en len w (LEN: len <= 2^w)
        (T1: hastyp_exp c e1 (2^w*8)) (T2: hastyp_exp c e2 w):
        hastyp_exp c (Load e1 e2 en len) (len*8)
| TStore e1 e2 e3 en len w (LEN: len <= 2^w)
         (T1: hastyp_exp c e1 (2^w*8)) (T2: hastyp_exp c e2 w)
         (T3: hastyp_exp c e3 (len*8)):
         hastyp_exp c (Store e1 e2 e3 en len) (2^w*8)
| TBinOp bop e1 e2 w
         (T1: hastyp_exp c e1 w) (T2: hastyp_exp c e2 w):
         hastyp_exp c (BinOp bop e1 e2) (widthof_binop bop w)
| TUnOp uop e w (T1: hastyp_exp c e w):
        hastyp_exp c (UnOp uop e) w
| TCast ct w w' e (T1: hastyp_exp c e w)
        (LE: match ct with CAST_UNSIGNED | CAST_SIGNED => w <= w'
                         | CAST_HIGH | CAST_LOW => w' <= w end):
        hastyp_exp c (Cast ct w' e) w'
| TLet v e1 e2 w1 w2
       (T1: hastyp_exp c e1 w1) (T2: hastyp_exp (c[v:=Some w1]) e2 w2):
       hastyp_exp c (Let v e1 e2) w2
| TUnknown w: hastyp_exp c (Unknown w) w
| TIte e1 e2 e3 w w'
       (T1: hastyp_exp c e1 w) (T2: hastyp_exp c e2 w') (T3: hastyp_exp c e3 w'):
       hastyp_exp c (Ite e1 e2 e3) w'
| TExtract w n1 n2 e1
           (T1: hastyp_exp c e1 w) (HI: n1 < w):
           hastyp_exp c (Extract n1 n2 e1) (N.succ n1 - n2)
| TConcat e1 e2 w1 w2
          (T1: hastyp_exp c e1 w1) (T2: hastyp_exp c e2 w2):
          hastyp_exp c (Concat e1 e2) (w1+w2).

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

Inductive hastyp_stmt (c0 c:typctx): stmt -> typctx -> Prop :=
| TNop c' (SS: c' ⊆ c): hastyp_stmt c0 c Nop c'
| TMove v w e c' (CV: c0 v = None \/ c0 v = Some w) (TE: hastyp_exp c e w) (SS: c' ⊆ c[v:=Some w]):
    hastyp_stmt c0 c (Move v e) c'
| TJmp e w c' (TE: hastyp_exp c e w) (SS: c' ⊆ c): hastyp_stmt c0 c (Jmp e) c'
| TExn ex c' (SS: c' ⊆ c): hastyp_stmt c0 c (Exn ex) c'
| TSeq q1 q2 c1 c2 c'
       (TS1: hastyp_stmt c0 c q1 c1) (TS2: hastyp_stmt c0 c1 q2 c2) (SS: c' ⊆ c2):
    hastyp_stmt c0 c (Seq q1 q2) c'
| TIf e q1 q2 c2 c'
      (TE: hastyp_exp c e 1)
      (TS1: hastyp_stmt c0 c q1 c2) (TS2: hastyp_stmt c0 c q2 c2) (SS: c' ⊆ c2):
    hastyp_stmt c0 c (If e q1 q2) c'
| TRep e w q c' c''
    (TE: hastyp_exp c e w) (SS: c' ⊆ c) (TS: hastyp_stmt c0 c' q c') (SS: c'' ⊆ c'):
    hastyp_stmt c0 c (Rep e q) c''.

(* A program is well-typed if all its statements are well-typed. *)
Definition welltyped_prog (c0:typctx) (p:program) : Prop :=
  forall s a, match p s a with None => True | Some (_,q) =>
                exists c', hastyp_stmt c0 c0 q c' end.

(* Context c "models" a store s if all variables in c have values in s
   that are well-typed with respect to c. *)
Definition models (c:typctx) (s:store) : Prop :=
  forall v w (CV: c v = Some w), s v < 2^w.

Theorem models_update:
  forall c s x y
    (HTV: match c x with Some w => y < 2^w | None => True end)
    (MDL: models c s),
  models c (update s x y).
Proof.
  intros. intros v t CV. unfold update. destruct (v == x).
    subst v. rewrite CV in HTV. assumption.
    apply MDL, CV.
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
Fixpoint typchk_exp (e:exp) (c:typctx): option bitwidth :=
  match e with
  | Var v => c v
  | Word n w => if n <? 2^w then Some w else None
  | Load e1 e2 _ len =>
      match typchk_exp e1 c, typchk_exp e2 c with
      | Some mw, Some aw =>
        if andb (len <=? N.shiftr mw 3) (mw =? N.shiftl 1 (3+aw)) then Some (8*len) else None
      | _, _ => None
      end
  | Store e1 e2 e3 _ len =>
      match typchk_exp e1 c, typchk_exp e2 c, typchk_exp e3 c with
      | Some mw, Some aw, Some w =>
          if andb (len <=? N.shiftr mw 3) (andb (mw =? N.shiftl 1 (3+aw)) (w =? 8*len))
          then Some mw else None
      | _, _, _ => None
      end
  | BinOp bop e1 e2 =>
      match typchk_exp e1 c, typchk_exp e2 c with
      | Some w1, Some w2 =>
          if w1 =? w2 then Some (widthof_binop bop w1) else None
      | _, _ => None
      end
  | UnOp uop e1 => match typchk_exp e1 c with Some w => Some w
                                            | _ => None end
  | Cast ct w' e1 =>
      match typchk_exp e1 c with Some w => 
        if match ct with CAST_UNSIGNED | CAST_SIGNED => w <=? w'
                       | CAST_HIGH | CAST_LOW => w' <=? w end then Some w' else None
      | _ => None
      end
  | Let v e1 e2 =>
      match typchk_exp e1 c with Some w => typchk_exp e2 (c[v:=Some w])
                               | None => None end
  | Unknown w => Some w
  | Ite e1 e2 e3 =>
      match typchk_exp e1 c, typchk_exp e2 c, typchk_exp e3 c with
      | Some w1, Some w2, Some w3 => if w2 == w3 then Some w2 else None
      | _, _, _ => None
      end
  | Extract n1 n2 e1 =>
      match typchk_exp e1 c with
      | Some w => if (n1 <? w) then Some (N.succ n1 - n2) else None
      | _ => None
      end
  | Concat e1 e2 =>
      match typchk_exp e1 c, typchk_exp e2 c with
      | Some w1, Some w2 => Some (w1+w2)
      | _, _ => None
      end
  end.

(* Compute the meet of two input contexts. *)
Definition typctx_meet (c1 c2:typctx) v :=
  match c1 v, c2 v with
  | Some w1, Some w2 => if w1 == w2 then Some w1 else None
  | _, _ => None
  end.

(* Type-check a statement given a frame-context and initial context. *)
Fixpoint typchk_stmt (q:stmt) (c0 c:typctx): option typctx :=
  match q with
  | Nop => Some c
  | Move v e =>
      match typchk_exp e c with
      | Some w => match c0 v with
                  | None => Some (c[v:=Some w])
                  | Some w' => if w == w' then Some (c[v:=Some w]) else None
                  end
      | None => None
      end
  | Jmp e => match typchk_exp e c with Some _ => Some c | _ => None end
  | Exn _ => Some c
  | Seq q1 q2 => match typchk_stmt q1 c0 c with
                 | None => None
                 | Some c2 => typchk_stmt q2 c0 c2
                 end
  | If e q1 q2 =>
      match typchk_exp e c, typchk_stmt q1 c0 c, typchk_stmt q2 c0 c with
      | Some 1, Some c1, Some c2 => Some (typctx_meet c1 c2)
      | _, _, _ => None
      end
  | Rep e q1 =>
      match typchk_exp e c, typchk_stmt q1 c c with
      | Some _, Some _ => Some c
      | _, _ => None
      end
  end.

End PICINAE_STATICS_DEFS.



Module Type PICINAE_STATICS (IL: PICINAE_IL) (TIL: PICINAE_THEORY IL).

Import IL.
Import TIL.
Include PICINAE_STATICS_DEFS IL TIL.

(* These short lemmas are helpful when automating type-checking in tactics. *)

Parameter setmem_welltyped:
  forall w en len m a n
    (WTM: m < memsize w),
  setmem w en len m a n < memsize w.

Parameter hastyp_binop:
  forall bop c e1 e2 w w' (W: widthof_binop bop w = w')
         (T1: hastyp_exp c e1 w) (T2: hastyp_exp c e2 w),
  hastyp_exp c (BinOp bop e1 e2) w'.

Parameter hastyp_extract:
  forall w c n1 n2 e1 w' (W: N.succ n1 - n2 = w')
         (T1: hastyp_exp c e1 w) (HI: n1 < w),
  hastyp_exp c (Extract n1 n2 e1) w'.

Parameter hastyp_concat:
  forall c e1 e2 w1 w2 w' (W: w1+w2 = w')
         (T1: hastyp_exp c e1 w1) (T2: hastyp_exp c e2 w2),
  hastyp_exp c (Concat e1 e2) w'.


(* Expression types are unique. *)
Parameter hastyp_exp_unique:
  forall e c1 c2 t1 t2 (HUB: has_upper_bound c1 c2)
         (TE1: hastyp_exp c1 e t1) (TE2: hastyp_exp c2 e t2),
  t1 = t2.

(* Expression typing contexts can be weakened. *)
Parameter hastyp_exp_weaken:
  forall c1 c2 e t (TE: hastyp_exp c1 e t) (SS: c1 ⊆ c2),
  hastyp_exp c2 e t.

(* Statement types can be weakened. *)
Parameter hastyp_stmt_weaken:
  forall c0 c1 c2 c' q (TS: hastyp_stmt c0 c1 q c') (SS: c1 ⊆ c2),
  hastyp_stmt c0 c2 q c'.
Parameter hastyp_stmt_weaken':
  forall c0 c c' c'' q (TS: hastyp_stmt c0 c q c') (SS: c'' ⊆ c'),
  hastyp_stmt c0 c q c''.

(* Statement types agree (though not necessarily unique). *)
Parameter hastyp_stmt_compat:
  forall c0 q c1 c2 c1' c2'
         (HUB: has_upper_bound c1 c2)
         (TS1: hastyp_stmt c0 c1 q c1') (TS2: hastyp_stmt c0 c2 q c2'),
  has_upper_bound c1' c2'.

(* Statement frame contexts can be weakened. *)
Parameter hastyp_stmt_frame_weaken:
  forall c0 c0' q c c' (TS: hastyp_stmt c0 c q c') (SS: c0' ⊆ c0),
  hastyp_stmt c0' c q c'.

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


(* Binary operations on well-typed values yield well-typed values. *)
Parameter typesafe_binop:
  forall bop n1 n2 w
         (TV1: n1 < 2^w) (TV2: n2 < 2^w),
  eval_binop bop w n1 n2 < 2 ^ widthof_binop bop w.

(* Unary operations on well-typed values yield well-typed values. *)
Parameter typesafe_unop:
  forall uop n w
         (TV: n < 2^w),
  eval_unop uop n w < 2^w.

(* Casts of well-typed values yield well-typed values. *)
Parameter typesafe_cast:
  forall c n w w' (TV: n < 2^w)
    (T: match c with CAST_UNSIGNED | CAST_SIGNED => w<=w'
                   | CAST_HIGH | CAST_LOW => w'<=w end),
  cast c w w' n < 2^w'.

Parameter typesafe_getmem:
  forall w len m a e,
  getmem w e len m a < 2^(len*8).

Parameter typesafe_setmem:
  forall w len m a v e
         (TV: m < memsize w),
  setmem w e len m a v < memsize w.

(* Values read from well-typed memory and registers have appropriate bitwidth. *)
Parameter models_var:
  forall v {c s} (MDL: models c s),
  match c v with Some w => s v < 2^w
               | None => True end.

(* Weakening the typing context preserves the modeling relation. *)
Parameter models_subset:
  forall c s c' (M: models c s) (SS: c' ⊆ c),
  models c' s.

(* Every result of evaluating a well-typed expression is a well-typed value. *)
Parameter preservation_eval_exp:
  forall {s e c w1 n w2}
         (MCS: models c s) (TE: hastyp_exp c e w1) (E: eval_exp c s e n w2),
  w1 = w2 /\ n < 2^w1.

(* If an expression is well-typed and there are no memory access violations,
   then evaluating it always succeeds (never gets "stuck"). *)
Parameter progress_eval_exp:
  forall {s e c w}
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c s) (T: hastyp_exp c e w),
  exists n, eval_exp c s e n w.

(* Statement execution preserves the modeling relation. *)
Parameter preservation_exec_stmt:
  forall {s q c0 c c1' c2' s' x}
         (MCS: models c s) (T: hastyp_stmt c0 c q c1') (XS: exec_stmt c s q c2' s' x),
  match x with None => c1' ⊆ c2' | _ => True end /\ models c2' s'.

(* Execution also preserves modeling the frame context c0. *)
Parameter pres_frame_exec_stmt:
  forall {s q c0 c c1' c2' s' x} (MC0S: models c0 s) (MCS: models c s)
         (T: hastyp_stmt c0 c q c1') (XS: exec_stmt c s q c2' s' x),
  models c0 s'.

(* Well-typed statements never get "stuck" except for memory access violations.
   They either exit or run to completion. *)
Parameter progress_exec_stmt:
  forall {s q c0 c c'}
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c s) (T: hastyp_stmt c0 c q c'),
  exists c'' s' x, exec_stmt c s q c'' s' x.

(* Well-typed programs preserve the modeling relation at every execution step. *)
Parameter preservation_exec_prog:
  forall p (WP: welltyped_prog archtyps p),
  forall_endstates p (fun _ s _ s' => forall (MDL: models archtyps s), models archtyps s').

(* Well-typed programs never get "stuck" except for memory access violations.
   They exit, or run to completion.  They never get "stuck" due to a runtime
   type-mismatch. *)
Parameter progress_exec_prog:
  forall p t a1 s1
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models archtyps (snd (startof t (Addr a1,s1))))
         (WP: welltyped_prog archtyps p)
         (XP: exec_prog p ((Addr a1,s1)::t)) (IL: p s1 a1 <> None),
  exists xs', exec_prog p (xs'::(Addr a1,s1)::t).

(* The expression type-checker is sound. *)
Parameter typchk_exp_sound:
  forall e c t, typchk_exp e c = Some t -> hastyp_exp c e t.

(* The meet of two contexts is bounded above by the contexts. *)
Parameter typctx_meet_subset:
  forall c1 c2, typctx_meet c1 c2 ⊆ c1.

(* Context-meet is commutative. *)
Parameter typctx_meet_comm:
  forall c1 c2, typctx_meet c1 c2 = typctx_meet c2 c1.

(* Context-meet computes the greatest of the lower bounds of the inputs. *)
Parameter typctx_meet_lowbound:
  forall c0 c1 c2 (SS1: c0 ⊆ c1) (SS2: c0 ⊆ c2), c0 ⊆ typctx_meet c1 c2.

(* The type-checker preserves the frame context. *)
Parameter typchk_stmt_mono:
  forall c0 q c c' (TS: typchk_stmt q c0 c = Some c') (SS: c0 ⊆ c), c0 ⊆ c'.

(* The statement type-checker is sound. *)
Parameter typchk_stmt_sound:
  forall q c0 c c' (SS: c0 ⊆ c) (TS: typchk_stmt q c0 c = Some c'),
  hastyp_stmt c0 c q c'.

(* Create a theorem that transforms a type-safety goal into an application of
   the type-checker.  This allows type-safety goals to be solved by any of
   Coq's fast reduction tactics, such as vm_compute or native_compute. *)
Parameter typchk_stmt_compute:
  forall q c (TS: if typchk_stmt q c c then True else False),
  exists c', hastyp_stmt c c q c'.

(* Attempt to automatically solve a goal of the form (welltyped_prog c p).
   Statements in p that cannot be type-checked automatically (using context-
   meets at conditionals and the incoming context as the fixpoint of loops)
   are left as subgoals for the user to solve.  For most ISAs, this should
   not happen; the algorithm should fully solve all the goals. *)
Ltac Picinae_typecheck :=
  lazymatch goal with [ |- welltyped_prog _ _ ] =>
    let s := fresh "s" in let a := fresh "a" in
    intros s a;
    destruct a as [|a]; repeat first [ exact I | destruct a as [a|a|] ];
    try (apply typchk_stmt_compute; vm_compute; exact I)
  | _ => fail "goal is not of the form (welltyped_prog c p)"
  end.

Parameter models_at_invariant:
  forall p Invs xp b x x1 s s1 t
    (MDL: models archtyps s) (WTP: welltyped_prog archtyps p)
    (ENTRY: startof t (x1,s1) = (x,s))
    (H: forall (MDL: models archtyps s1), nextinv p Invs xp b ((x1,s1)::t)),
  nextinv p Invs xp b ((x1,s1)::t).

Parameter models_after_steps:
  forall p Invs xp b x s t1 x0 s0 t2
    (MDL: models archtyps s0) (WTP: welltyped_prog archtyps p)
    (H: forall (MDL: models archtyps s), nextinv p Invs xp b ((x,s)::t1++(x0,s0)::t2)),
  nextinv p Invs xp b ((x,s)::t1++(x0,s0)::t2).

End PICINAE_STATICS.


Module PicinaeStatics (IL: PICINAE_IL) (TIL: PICINAE_THEORY IL): PICINAE_STATICS IL TIL.

Import IL.
Import TIL.
Include PICINAE_STATICS_DEFS IL TIL.

Theorem setmem_welltyped:
  forall w en len m a n
    (WTM: m < memsize w),
  setmem w en len m a n < memsize w.
Proof.
  unfold memsize. intros.
  rewrite <- (recompose_bytes (2^w*8) (setmem _ _ _ _ _ _)), setmem_highbits.
  change 8 with (2^3). rewrite <- (N.pow_add_r 2 w 3), shiftr_low_pow2.
    rewrite N.shiftl_0_l, N.lor_0_r, N.pow_add_r. apply mp2_mod_lt.
    rewrite N.pow_add_r. assumption.
Qed.

Lemma hastyp_binop:
  forall bop c e1 e2 w w' (W: widthof_binop bop w = w')
         (T1: hastyp_exp c e1 w) (T2: hastyp_exp c e2 w),
  hastyp_exp c (BinOp bop e1 e2) w'.
Proof.
  intros. rewrite <- W. apply TBinOp; assumption.
Qed.

Lemma hastyp_extract:
  forall w c n1 n2 e1 w' (W: N.succ n1 - n2 = w')
         (T1: hastyp_exp c e1 w) (HI: n1 < w),
  hastyp_exp c (Extract n1 n2 e1) w'.
Proof.
  intros. rewrite <- W. eapply TExtract; eassumption.
Qed.

Lemma hastyp_concat:
  forall c e1 e2 w1 w2 w' (W: w1+w2 = w')
         (T1: hastyp_exp c e1 w1) (T2: hastyp_exp c e2 w2),
  hastyp_exp c (Concat e1 e2) w'.
Proof.
  intros. rewrite <- W. apply TConcat; assumption.
Qed.

Theorem hastyp_exp_unique:
  forall e c1 c2 w1 w2 (HUB: has_upper_bound c1 c2)
         (TE1: hastyp_exp c1 e w1) (TE2: hastyp_exp c2 e w2),
  w1 = w2.
Proof.
  intros. revert c1 c2 w1 w2 HUB TE1 TE2. induction e; intros;
  inversion TE1; inversion TE2; clear TE1 TE2; subst;
  try reflexivity.

  (* Var *)
  eapply HUB; eassumption.

  (* Store *)
  specialize (IHe2 _ _ _ _ HUB T2 T4). subst. reflexivity.

  (* BinOp *)
  specialize (IHe1 _ _ _ _ HUB T1 T0). inversion IHe1. reflexivity.

  (* UnOp *)
  specialize (IHe _ _ _ _ HUB T1 T0). inversion IHe. reflexivity.

  (* Let *)
  specialize (IHe1 _ _ _ _ HUB T1 T0). subst.
  refine (IHe2 _ _ _ _ _ T2 T3). apply hub_update. exact HUB.

  (* Extract *)
  exact (IHe2 _ _ _ _ HUB T2 T4).

  (* Concat *)
  specialize (IHe1 _ _ _ _ HUB T1 T0). inversion IHe1. subst.
  specialize (IHe2 _ _ _ _ HUB T2 T3). inversion IHe2. subst.
  reflexivity.
Qed.

Theorem hastyp_exp_weaken:
  forall c1 c2 e t (TE: hastyp_exp c1 e t) (SS: c1 ⊆ c2),
  hastyp_exp c2 e t.
Proof.
  intros. revert c2 SS. dependent induction TE; intros; econstructor;
  try (try first [ apply IHTE | apply IHTE1 | apply IHTE2 | apply IHTE3 | apply SS ]; assumption).

  assumption.
  apply IHTE2. unfold update. intros v0 t CV. destruct (v0 == v).
    assumption.
    apply SS. assumption.
Qed.

Theorem hastyp_stmt_weaken':
  forall c0 c c' c'' q (TS: hastyp_stmt c0 c q c') (SS: c'' ⊆ c'),
  hastyp_stmt c0 c q c''.
Proof.
  intros. inversion TS; clear TS; subst;
  econstructor; first [ eassumption | transitivity c'; assumption ].
Qed.

Theorem hastyp_stmt_weaken:
  forall c0 c1 c2 c' q (TS: hastyp_stmt c0 c1 q c') (SS: c1 ⊆ c2),
  hastyp_stmt c0 c2 q c'.
Proof.
  intros. revert c2 SS. dependent induction TS; intros;
  try solve [ econstructor; repeat first
  [ eassumption
  | eapply hastyp_exp_weaken; eassumption
  | apply pfsub_update; assumption
  | (apply IHTS1 + apply IHTS2); assumption
  | etransitivity; [eassumption|] ] ].

  econstructor.
    eapply hastyp_exp_weaken; eassumption.
    etransitivity; [|eassumption]. eassumption.
    apply IHTS. reflexivity.
    assumption.
Qed.

Theorem hastyp_stmt_compat:
  forall c0 q c1 c2 c1' c2'
         (HUB: has_upper_bound c1 c2)
         (TS1: hastyp_stmt c0 c1 q c1') (TS2: hastyp_stmt c0 c2 q c2'),
  has_upper_bound c1' c2'.
Proof.
  induction q; intros; inversion TS1; inversion TS2; clear TS1 TS2; subst;
  try solve [ apply (hub_subset _ _ _ _ _ _ HUB); assumption ].
    eapply hub_subset; [|eassumption..]. replace w0 with w.
      apply hub_update, HUB.
      eapply hastyp_exp_unique; eassumption.
    eapply IHq2.
      eapply IHq1; eassumption.
      eapply hastyp_stmt_weaken'. exact TS3. exact SS.
      eapply hastyp_stmt_weaken'. exact TS5. exact SS0.
    eapply hub_subset; [|eassumption..]. eapply IHq1; eassumption.
    eapply IHq; [eassumption| |];
      (eapply hastyp_stmt_weaken; [|eassumption]);
      eapply hastyp_stmt_weaken'; eassumption.
Qed.

Theorem hastyp_stmt_frame_weaken:
  forall c0 c0' q c c' (TS: hastyp_stmt c0 c q c') (SS: c0' ⊆ c0),
  hastyp_stmt c0' c q c'.
Proof.
  induction q; intros; inversion TS; subst.
    apply TNop. assumption.
    eapply TMove.
      specialize (SS v). destruct (c0' v).
        right. rewrite (SS b (eq_refl _)) in CV. destruct CV. discriminate. eassumption.
        left. reflexivity.
      exact TE.
      assumption.
    eapply TJmp. exact TE. assumption.
    apply TExn. assumption.
    eapply TSeq.
      apply IHq1. exact TS1. exact SS.
      apply IHq2. exact TS2. exact SS.
      exact SS0.
    eapply TIf.
      exact TE.
      apply IHq1. exact TS1. exact SS.
      apply IHq2. exact TS2. exact SS.
      exact SS0.
    eapply TRep.
      exact TE.
      exact SS0.
      apply IHq. exact TS0. exact SS.
      exact SS1.
Qed.

Theorem typesafe_binop:
  forall bop n1 n2 w
         (TV1: n1 < 2^w) (TV2: n2 < 2^w),
  eval_binop bop w n1 n2 < 2 ^ widthof_binop bop w.
Proof.
  intros. destruct bop; try first [ apply mp2_mod_lt | apply bit_bound ];
  try apply ofZ_bound.

  (* DIV *)
  eapply N.le_lt_trans. apply div_bound. assumption.

  (* SMOD *)
  apply mod_bound; assumption.

  (* SHIFTR *)
  eapply N.lt_le_trans.
    apply shiftr_bound. eassumption.
    apply N.pow_le_mono_r. discriminate 1. apply N.le_sub_l.

  (* LAND *)
  apply land_bound; assumption.

  (* LOR *)
  apply lor_bound; assumption.

  (* LXOR *)
  apply lxor_bound; assumption.
Qed.

Theorem typesafe_unop:
  forall uop n w
         (TV: n < 2^w),
  eval_unop uop n w < 2^w.
Proof.
  intros. destruct uop.

  (* NEG *)
  apply mp2_mod_lt.

  (* NOT *)
  apply lnot_bound. assumption.

  (* POPCOUNT *)
  eapply N.le_lt_trans. apply popcount_bound.
  eapply N.le_lt_trans. apply size_le_diag. apply TV.

  (* BITWIDTH *)
  eapply N.le_lt_trans. apply size_le_diag. apply TV.
Qed.

Theorem typesafe_cast:
  forall c n w w' (TV: n < 2^w)
    (T: match c with CAST_UNSIGNED | CAST_SIGNED => w<=w'
                   | CAST_HIGH | CAST_LOW => w'<=w end),
  cast c w w' n < 2^w'.
Proof.
  intros. inversion TV. subst. destruct c; simpl.

  (* LOW *)
  apply mp2_mod_lt.

  (* HIGH *)
  apply cast_high_bound; assumption.

  (* SIGNED *)
  apply ofZ_bound.

  (* UNSIGNED *)
  eapply N.lt_le_trans. eassumption.
  apply N.pow_le_mono_r. discriminate 1. assumption.
Qed.

Theorem typesafe_getmem:
  forall w len m a e,
  getmem w e len m a < 2 ^ (len*8).
Proof.
  intros. apply getmem_bound.
Qed.

Corollary typesafe_setmem:
  forall w len m a v e
         (TV: m < memsize w),
  setmem w e len m a v < memsize w.
Proof.
  intros. eapply setmem_welltyped, TV.
Qed.

Theorem models_var:
  forall v {c s} (MDL: models c s),
  match c v with Some w => s v < 2^w
               | None => True end.
Proof.
  intros. destruct (c v) eqn:CV; [|exact I].
  specialize (MDL _ _ CV). inversion MDL; assumption.
Qed.

Lemma models_subset:
  forall c s c' (M: models c s) (SS: c' ⊆ c),
  models c' s.
Proof.
  unfold models. intros. apply M, SS, CV.
Qed.

Lemma preservation_eval_exp:
  forall {s e c w1 n w2}
         (MCS: models c s) (TE: hastyp_exp c e w1) (E: eval_exp c s e n w2),
  w1 = w2 /\ n < 2^w1.
Proof.
  intros. revert s n w2 MCS E. dependent induction TE; intros;
  inversion E; subst;
  repeat match goal with [ IH: forall _ _ _, models _ _ -> eval_exp _ _ ?e _ _ -> _=_ /\ _ < 2^_,
                           M: models ?c ?s,
                           EE: eval_exp ?c ?s ?e _ _ |- _ ] =>
           specialize (IH s _ _ MCS EE); destruct IH as [? IH]; subst;
           try (inversion H2; [idtac]; subst) end;
  try (split; [reflexivity|]).

  (* Var *)
  split.
    rewrite CV in TYP. inversion TYP. reflexivity.
    apply MCS, CV.

  (* Word *)
  assumption.

  (* Load *)
  apply typesafe_getmem.

  (* Store *)
  apply typesafe_setmem. assumption.

  (* BinOp *)
  apply typesafe_binop; assumption.

  (* UnOp *)
  apply typesafe_unop; assumption.

  (* Cast *)
  apply typesafe_cast; assumption.

  (* Let *)
  eapply IHTE2; [|exact E2].
  unfold update. intros v00 t00 VEQT. destruct (v00 == v).
    inversion VEQT. subst. exact IHTE1.
    apply MCS. exact VEQT.

  (* Unknown *)
  assumption.

  (* Ite *)
  destruct n1; assumption.

  (* Extract *)
  apply xbits_bound.

  (* Concat *)
  apply concat_bound; assumption.
Qed.

Lemma progress_eval_exp:
  forall {s e c w}
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c s) (T: hastyp_exp c e w),
  exists n, eval_exp c s e n w.
Proof.
  intros. revert s MCS. dependent induction T; intros;
  repeat match reverse goal with [ IH: forall _, models ?c _ -> exists _, eval_exp ?c _ ?e _ _,
                                    M: models ?c ?s,
                                    T: hastyp_exp ?c ?e _ |- _ ] =>
    specialize (IH s M);
    let n':=fresh "n" in let EE:=fresh "E" in let TV:=fresh "TV" in
      destruct IH as [n' EE];
      assert (TV:=proj2 (preservation_eval_exp M T EE));
      try (inversion TV; [idtac]; clear TV; subst)
  end.

  (* Var *)
  exists (s v). apply EVar. assumption.

  (* Word *)
  eexists. apply EWord; assumption.

  (* Load *)
  eexists. eapply ELoad; try eassumption. intros. apply RW.

  (* Store *)
  eexists. eapply EStore; try eassumption. intros. apply RW.

  (* BinOp *)
  eexists. apply EBinOp; eassumption.

  (* UnOp *)
  eexists. apply EUnOp; eassumption.

  (* Cast *)
  eexists. apply ECast; eassumption.

  (* Let *)
  destruct (IHT2 (s[v:=n])) as [n' E2].
    unfold update. intros v00 t00 VEQT. destruct (v00 == v).
      inversion VEQT. subst. assumption.
      apply MCS. exact VEQT.
    exists n'. eapply ELet; eassumption.

  (* Unknown *)
  exists 0. apply EUnknown. apply mp2_gt_0.

  (* Ite *)
  destruct n; eexists; eapply EIte; eassumption.

  (* Extract *)
  eexists. eapply EExtract. eassumption.

  (* Concat *)
  eexists. apply EConcat; eassumption.
Qed.

Lemma preservation_exec_stmt:
  forall {s q c0 c c1' c2' s' x}
         (MCS: models c s) (T: hastyp_stmt c0 c q c1') (XS: exec_stmt c s q c2' s' x),
  match x with None => c1' ⊆ c2' | _ => True end /\ models c2' s'.
Proof.
  intros. revert c1' MCS T. dependent induction XS; intros; inversion T; subst;
  try (split; (reflexivity || assumption)).

  apply (preservation_eval_exp MCS TE) in E. destruct E as [H E]. subst.
  split. assumption.
  unfold update. intros v0 t0 T0. destruct (v0 == v).
    inversion T0. subst. assumption.
    apply MCS. assumption.

  specialize (IHXS _ MCS TS1). destruct IHXS as [H1 MCS2].
  split. reflexivity. assumption.

  specialize (IHXS1 _ MCS TS1). destruct IHXS1 as [H1 MCS2].
  apply IHXS2. assumption.
  eapply hastyp_stmt_weaken; [|eassumption].
  eapply hastyp_stmt_weaken'; eassumption.

  eapply IHXS. assumption.
  eapply hastyp_stmt_weaken'; [|eassumption].
  destruct b; assumption.

  destruct (IHXS c'0 MCS) as [H1 H2].
    eapply hastyp_stmt_weaken; [|eassumption]. eapply Niter_invariant.
      econstructor. reflexivity.
      intros. econstructor; eassumption || reflexivity.
    split. destruct x. reflexivity. etransitivity; eassumption. assumption.
Qed.

Lemma pres_frame_exec_stmt:
  forall {s q c0 c c1' c2' s' x} (MC0S: models c0 s) (MCS: models c s)
         (T: hastyp_stmt c0 c q c1') (XS: exec_stmt c s q c2' s' x),
  models c0 s'.
Proof.
  intros. revert c1' T. dependent induction XS; intros;
  try assumption;
  inversion T; subst.

  intros v00 t00 CV00. unfold update. destruct (v00 == v).
    subst. destruct CV as [CV|CV]; rewrite CV00 in CV.
      discriminate.
      inversion CV. subst t00. apply (preservation_eval_exp MCS TE E).
    apply MC0S, CV00.

  eapply IHXS; eassumption.

  destruct (preservation_exec_stmt MCS TS1 XS1) as [H1 H2].
  eapply IHXS2.
    eapply IHXS1; eassumption.
    eapply preservation_exec_stmt. exact MCS. exact TS1. exact XS1.
    eapply hastyp_stmt_weaken; eassumption.

  destruct b; eapply IHXS; eassumption.

  eapply IHXS. assumption. exact MCS.
  eapply hastyp_stmt_weaken; [|eassumption].
  apply Niter_invariant. econstructor. eassumption.
  intros. econstructor. eassumption. eassumption. reflexivity.
Qed.

Lemma progress_exec_stmt:
  forall {s q c0 c c'}
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models c s) (T: hastyp_stmt c0 c q c'),
  exists c'' s' x, exec_stmt c s q c'' s' x.
Proof.
  intros. revert c c' s T MCS. induction q using stmt_ind2; intros;
  try (inversion T; subst).

  (* Nop *)
  exists c,s,None. apply XNop.

  (* Move *)
  destruct (progress_eval_exp RW MCS TE) as [n E].
  exists (c[v:=Some w]),(s[v:=n]),None. apply XMove. assumption.

  (* Jmp *)
  destruct (progress_eval_exp RW MCS TE) as [n E].
  assert (TV:=proj2 (preservation_eval_exp MCS TE E)).
  exists c,s,(Some (Addr n)). apply XJmp with (w:=w). assumption.

  (* Exn *)
  exists c,s,(Some (Raise i)). apply XExn.

  (* Seq *)
  destruct (IHq1 _ _ _ TS1 MCS) as [c1' [s1' [x1 XS1]]].
  destruct (preservation_exec_stmt MCS TS1 XS1) as [H1 H2].
  destruct x1.
    exists c1',s1',(Some e). apply XSeq1. exact XS1.
    destruct (IHq2 c1' c2 s1') as [c2' [s2' [x2 XS2]]].
      eapply hastyp_stmt_weaken; eassumption.
      assumption.
      exists c2',s2',x2. eapply XSeq2; eassumption.

  (* If *)
  destruct (progress_eval_exp RW MCS TE) as [n E].
  assert (TV:=proj2 (preservation_eval_exp MCS TE E)).
  destruct n as [|n].
    destruct (IHq2 _ _ _ TS2 MCS) as [c'2 [s'2 [x2 XS2]]]. exists c'2,s'2,x2. apply XIf with (b:=0); assumption.
    destruct (IHq1 _ _ _ TS1 MCS) as [c'1 [s'1 [x1 XS1]]]. exists c'1,s'1,x1. apply XIf with (b:=N.pos n); assumption.

  (* Rep *)
  destruct (progress_eval_exp RW MCS TE) as [n E].
  assert (TV:=proj2 (preservation_eval_exp MCS TE E)). inversion TV; subst.
  destruct (IHq2 n c c' s) as [c'' [s' [x XS]]].
    eapply hastyp_stmt_weaken; [|eassumption].
    eapply hastyp_stmt_weaken'; [|eassumption].
    apply Niter_invariant.
      apply TNop. reflexivity.
      intros. eapply TSeq. exact TS. exact IH. reflexivity.
    exact MCS.
    exists c'',s',x. eapply XRep. exact E. assumption.
Qed.

Lemma models_reset_temps:
  forall s2 s1 (MDL: models archtyps s2), models archtyps (reset_temps s1 s2).
Proof.
  intros. intros v w H. unfold reset_temps, reset_vars. rewrite H. apply MDL, H.
Qed.

Theorem preservation_exec_prog:
  forall p (WP: welltyped_prog archtyps p),
  forall_endstates p (fun _ s _ s' => forall (MDL: models archtyps s), models archtyps s').
Proof.
  unfold forall_endstates. intros.
  change s with (snd (x,s)) in MDL. rewrite <- ENTRY in MDL.
  clear x s ENTRY. revert x' s' MDL XP. induction t as [|(x1,s1) t]; intros.
    exact MDL.

    assert (CS:=exec_prog_final _ _ _ _ XP). inversion CS; subst.
    specialize (WP s1 a). rewrite LU in WP. destruct WP as [c'' TS].
    rewrite startof_cons in MDL. apply exec_prog_tail in XP. specialize (IHt _ _ MDL XP).
    apply models_reset_temps.
    clear MDL. eapply pres_frame_exec_stmt; eassumption.
Qed.

Theorem progress_exec_prog:
  forall p t a1 s1
         (RW: forall s0 a0, mem_readable s0 a0 /\ mem_writable s0 a0)
         (MCS: models archtyps (snd (startof t (Addr a1,s1))))
         (WP: welltyped_prog archtyps p)
         (XP: exec_prog p ((Addr a1,s1)::t)) (IL: p s1 a1 <> None),
  exists xs', exec_prog p (xs'::(Addr a1,s1)::t).
Proof.
  intros.
  assert (WPA':=WP s1 a1). destruct (p s1 a1) as [(sz,q)|] eqn:IL'; [|contradict IL; reflexivity]. clear IL.
  destruct WPA' as [c' T]. eapply progress_exec_stmt in T.
    destruct T as [c'' [s' [x' XS]]]. eexists (_,reset_temps s1 s'). eapply exec_prog_step.
      exact XP.
      econstructor; eassumption.
    exact RW.
    eapply preservation_exec_prog; try eassumption. apply surjective_pairing.
Qed.

Remark shiftl1_3pn:
  forall n, N.shiftl 1 (3+n) = 2^n*8.
Proof.
  intro. rewrite N.shiftl_1_l, N.pow_add_r, N.mul_comm. reflexivity.
Qed.

Theorem typchk_exp_sound:
  forall e c w, typchk_exp e c = Some w -> hastyp_exp c e w.
Proof.
  induction e; cbn [ typchk_exp ]; intros.

  (* Var *)
  apply TVar. assumption.

  (* Word *)
  destruct (n <? 2^w) eqn:LT.
    injection H; intro; subst. apply TWord, N.ltb_lt, LT.
    discriminate.

  (* Load *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (typchk_exp e1 c) as [w1|]; try discriminate.
  destruct (typchk_exp e2 c) as [w2|]; try discriminate.
  destruct (_ <=? _) eqn:EQ1; [|discriminate].
  destruct (_ =? _) eqn:EQ2; [|discriminate].
  rewrite N.mul_comm in H. inversion H.
  rewrite shiftl1_3pn in EQ2. apply N.eqb_eq in EQ2. subst.
  rewrite <- shiftl1_3pn, N.add_comm, <- N.shiftl_shiftl, N.shiftr_shiftl_l,
          N.sub_diag, N.shiftl_0_r, N.shiftl_1_l in EQ1 by reflexivity.
  eapply TLoad.
    apply N.leb_le, EQ1.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.

  (* Store *)
  specialize (IHe1 c). specialize (IHe2 c). specialize (IHe3 c).
  destruct (typchk_exp e1 c) as [w1|]; try discriminate.
  destruct (typchk_exp e2 c) as [w2|]; try discriminate.
  destruct (typchk_exp e3 c) as [w3|]; try discriminate.
  destruct (_ <=? _) eqn:EQ0; [|discriminate].
  destruct (w1 =? _) eqn:EQ1; [|discriminate].
  destruct (w3 =? _) eqn:EQ2; [|discriminate].
  inversion H. apply N.eqb_eq in EQ1,EQ2. subst.
  rewrite N.add_comm, <- N.shiftl_shiftl, N.shiftr_shiftl_r, N.sub_diag, N.shiftr_0_r,
    N.shiftl_1_l in EQ0 by reflexivity.
  rewrite shiftl1_3pn.
  apply TStore.
    apply N.leb_le, EQ0.
    apply IHe1. rewrite <- shiftl1_3pn. reflexivity.
    apply IHe2. reflexivity.
    apply IHe3. rewrite N.mul_comm. reflexivity.

  (* BinOp *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (typchk_exp e1 c) as [w1|]; try discriminate.
  destruct (typchk_exp e2 c) as [w2|]; try discriminate.
  destruct (w1 =? w2) eqn:EQ; [|discriminate].
  apply N.eqb_eq in EQ. injection H; intro; subst.
  apply TBinOp.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.

  (* UnOp *)
  specialize (IHe c).
  destruct (typchk_exp e c) as [w1|]; try discriminate.
  injection H; intro; subst.
  apply TUnOp. apply IHe. reflexivity.

  (* Cast *)
  specialize (IHe c0).
  destruct (typchk_exp e c0) as [w1|]; try discriminate.
  destruct c; destruct (_ <=? _) eqn:LE; try discriminate;
  apply N.leb_le in LE; injection H; intro; subst;
  (eapply TCast; [ apply IHe; reflexivity | exact LE ]).

  (* Let *)
  specialize (IHe1 c). destruct (typchk_exp e1 c); [|discriminate].
  eapply TLet.
    apply IHe1. reflexivity.
    apply IHe2. assumption.

  (* Unknown *)
  injection H; intro; subst. apply TUnknown.

  (* Ite *)
  specialize (IHe1 c). specialize (IHe2 c). specialize (IHe3 c).
  destruct (typchk_exp e1 c) as [w1|]; try discriminate.
  destruct (typchk_exp e2 c) as [w2|]; [|discriminate].
  destruct (typchk_exp e3 c) as [w3|]; [|discriminate].
  destruct (w2 == w3); [|discriminate].
  injection H; intro; subst.
  eapply TIte.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
    apply IHe3. reflexivity.

  (* Extract *)
  specialize (IHe c).
  destruct (typchk_exp e c) as [w1|]; try discriminate.
  destruct (n1 <? w1) eqn:LT; [|discriminate]. apply N.ltb_lt in LT.
  injection H; intro; subst.
  eapply TExtract.
    apply IHe. reflexivity.
    exact LT.

  (* Concat *)
  specialize (IHe1 c). specialize (IHe2 c).
  destruct (typchk_exp e1 c) as [w1|]; try discriminate.
  destruct (typchk_exp e2 c) as [w2|]; try discriminate.
  injection H; intro; subst.
  apply TConcat.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
Qed.

Lemma typctx_meet_subset:
  forall c1 c2, typctx_meet c1 c2 ⊆ c1.
Proof.
  intros c1 c2 v t H. unfold typctx_meet in H.
  destruct (c1 v) as [t1|]; [|discriminate].
  destruct (c2 v) as [t2|]; [|discriminate].
  destruct (t1 == t2). exact H. discriminate.
Qed.

Lemma typctx_meet_comm:
  forall c1 c2, typctx_meet c1 c2 = typctx_meet c2 c1.
Proof.
  intros. extensionality v. unfold typctx_meet.
  destruct (c1 v) as [w1|], (c2 v) as [w2|]; try reflexivity.
  destruct (w1 == w2).
    subst. destruct (w2 == w2). reflexivity. contradict n. reflexivity.
    destruct (w2 == w1). contradict n. symmetry. assumption. reflexivity.
Qed.

Lemma typctx_meet_lowbound:
  forall c0 c1 c2 (SS1: c0 ⊆ c1) (SS2: c0 ⊆ c2), c0 ⊆ typctx_meet c1 c2.
Proof.
  unfold "⊆", typctx_meet. intros.
  rewrite (SS1 _ _ H). rewrite (SS2 _ _ H).
  destruct (y == y); [|contradict n]; reflexivity.
Qed.

Lemma typchk_stmt_mono:
  forall c0 q c c' (TS: typchk_stmt q c0 c = Some c') (SS: c0 ⊆ c), c0 ⊆ c'.
Proof.
  induction q; simpl; intros.

  (* Nop *)
  injection TS; intro; subst. exact SS.

  (* Move *)
  destruct (typchk_exp e c) as [w|]; [|discriminate].
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
  destruct (typchk_exp e c) as [w|]; try discriminate.
  injection TS; intro; subst. exact SS.

  (* Exn *)
  injection TS; intro; subst. exact SS.

  (* Seq *)
  destruct (typchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  eapply IHq2. exact TS.
  eapply IHq1. exact TS1. exact SS.

  (* If *)
  destruct (typchk_exp e c) as [[|[| |]]|]; try discriminate.
  destruct (typchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  destruct (typchk_stmt q2 c0 c) as [c2|] eqn:TS2; [|discriminate].
  injection TS; intro; subst.
  apply typctx_meet_lowbound.
    eapply IHq1. exact TS1. exact SS.
    eapply IHq2. exact TS2. exact SS.

  (* Rep *)
  destruct (typchk_exp e c) as [|]; try discriminate.
  destruct (typchk_stmt q c c) eqn:TS1; [|discriminate].
  injection TS; intro; subst.
  exact SS.
Qed.

Theorem typchk_stmt_sound:
  forall q c0 c c' (SS: c0 ⊆ c) (TS: typchk_stmt q c0 c = Some c'),
  hastyp_stmt c0 c q c'.
Proof.
  induction q; intros; simpl in TS.

  (* Nop *)
  injection TS; intro; subst. apply TNop. reflexivity.

  (* Move *)
  destruct (typchk_exp e c) as [w1|] eqn:TE; [|discriminate].
  destruct (c0 v) eqn:C0V; [destruct (w1 == _)|];
  try (injection TS; clear TS; intro); subst;
  first [ discriminate | eapply TMove; [| |reflexivity] ].
    right. exact C0V. apply typchk_exp_sound. exact TE.
    left. exact C0V. apply typchk_exp_sound. exact TE.

  (* Jmp *)
  destruct (typchk_exp e c) as [w|] eqn:TE; try discriminate.
  injection TS; intro; subst.
  eapply TJmp. apply typchk_exp_sound. exact TE. reflexivity.

  (* Exn *)
  injection TS; intro; subst. apply TExn. reflexivity.

  (* Seq *)
  specialize (IHq1 c0 c). destruct (typchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  specialize (IHq2 c0 c1). destruct (typchk_stmt q2 c0 c1); [|discriminate].
  injection TS; clear TS; intro; subst.
  eapply TSeq.
    apply IHq1. exact SS. reflexivity.
    apply IHq2. eapply typchk_stmt_mono; eassumption. reflexivity. reflexivity.

  (* If *)
  destruct (typchk_exp e c) as [[|[| |]]|] eqn:TE; try discriminate.
  destruct (typchk_stmt q1 c0 c) as [c1|] eqn:TS1; [|discriminate].
  destruct (typchk_stmt q2 c0 c) as [c2|] eqn:TS2; [|discriminate].
  injection TS; clear TS; intro; subst.
  eapply TIf.
    apply typchk_exp_sound. exact TE.
    eapply hastyp_stmt_weaken'.
      apply IHq1. exact SS. exact TS1.
      apply typctx_meet_subset.
    eapply hastyp_stmt_weaken'.
      apply IHq2. exact SS. exact TS2.
      rewrite typctx_meet_comm. apply typctx_meet_subset.
    reflexivity.

  (* Rep *)
  destruct (typchk_exp e c) as [|] eqn:TE; try discriminate.
  specialize (IHq c c). destruct (typchk_stmt q c c) as [c1|] eqn:TS1; [|discriminate].
  injection TS; clear TS; intro; subst.
  eapply TRep.
    apply typchk_exp_sound. exact TE.
    reflexivity.
    eapply hastyp_stmt_frame_weaken; [|exact SS]. eapply hastyp_stmt_weaken'.
      apply IHq. reflexivity. reflexivity.
      eapply typchk_stmt_mono. exact TS1. reflexivity.
    reflexivity.
Qed.

Corollary typchk_stmt_compute:
  forall q c (TS: if typchk_stmt q c c then True else False),
  exists c', hastyp_stmt c c q c'.
Proof.
  intros. destruct (typchk_stmt q c c) as [c'|] eqn:TS1.
    exists c'. apply typchk_stmt_sound. reflexivity. exact TS1.
    contradict TS.
Qed.

(* Use the exec_prog assumption within nextinv to prove that the "models"
   relation has been preserved at the start of an invariant.  (This is
   important for setting up the proof context after destruct_invs.) *)
Theorem models_at_invariant:
  forall p Invs xp b x x1 s s1 t
    (MDL: models archtyps s) (WTP: welltyped_prog archtyps p)
    (ENTRY: startof t (x1,s1) = (x,s))
    (H: forall (MDL: models archtyps s1), nextinv p Invs xp b ((x1,s1)::t)),
  nextinv p Invs xp b ((x1,s1)::t).
Proof.
  intros. apply exec_prog_nextinv. intro XP. apply H.
  eapply preservation_exec_prog; eassumption.  
Qed.

(* Use the exec_prog assumption within nextinv to prove that the "models"
   relation has been preserved after a series of steps.  (This is
   important for setting up the proof context for a subroutine call.) *)
Theorem models_after_steps:
  forall p Invs xp b x s t1 x0 s0 t2
    (MDL: models archtyps s0) (WTP: welltyped_prog archtyps p)
    (H: forall (MDL: models archtyps s), nextinv p Invs xp b ((x,s)::t1++(x0,s0)::t2)),
  nextinv p Invs xp b ((x,s)::t1++(x0,s0)::t2).
Proof.
  intros. apply exec_prog_nextinv. intro XP. apply H.
  eapply preservation_exec_prog.
    apply WTP.
    rewrite split_subtraces in XP. apply exec_prog_split,proj2,proj2 in XP. apply XP.
    apply startof_niltail.
    apply MDL.
Qed.

End PicinaeStatics.

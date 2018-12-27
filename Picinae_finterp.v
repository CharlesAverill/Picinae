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
   Functional interpretation of IL programs.           MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   * Picinae_statics                                        MMMMMMMMMMM7..ZNOOMZ
   Then compile this module with menu option                 MMMMMMMMMM$.$MOMO=7
   Compile->Compile_buffer.                                   MDMMMMMMMO.7MDM7M+
                                                               ZMMMMMMMM.$MM8$MN
                                                               $ZMMMMMMZ..MMMOMZ
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

Require Import Picinae_statics.
Require Import NArith.
Require Import ZArith.
Require Import List.

(* Functional Interpretation of Programs:
   This module defines an IL interpreter that is purely functional instead of
   inductive.  Since programs can be non-deterministic (if there are Unknown
   expressions), the interpreter introduces a fresh context variable for each
   unknown.  The interpreter is proved correct according to the operational
   semantics, so it does not contribute to Picinae's trusted core definitions.
   This facilitates a series of tactics that can symbolically evaluate
   expressions and statements in proofs to automatically infer the resulting
   store after execution of each assembly language instruction. *)


(* In order to help Coq expression simplification to infer a value for each
   symbolic expression, we define our interpreter in terms of "untyped values"
   (uvalues), which always contain both a memory value and a numeric value.
   This allows the interpreter to progress even when it can't automatically
   infer a IL expression's IL-type. *)

Inductive uvalue := VaU (z:bool) (m:addr->N) (n:N) (w:N).

Definition vget (v:value) :=
  match v with
  | VaN n w => VaU true (fun _ => 0) n w
  | VaM m w => VaU false m 0 w
  end.


(* When the interpreter cannot determine an IL variable's type and/or value
   (e.g., because store s is a proof variable), the interpreter returns an
   expression that contains the following accessor functions to refer to the
   unknown type/value. *)

Definition vtyp (u:value) :=
  match u with VaM _ _ => false | VaN _ _ => true end.

Definition vnum (u:value) :=
  match u with VaN n _ => n | VaM _ _ => N0 end.

Definition vmem (u:value) :=
  match u with VaM m _ => m | VaN _ _ => (fun _ => N0) end.

Definition vwidth (u:value) :=
  match u with VaN _ w | VaM _ w => w end.

Lemma vtyp_num n w: vtyp (VaN n w) = true. Proof eq_refl.
Lemma vtyp_mem m w: vtyp (VaM m w) = false. Proof eq_refl.
Lemma vnum_num n w: vnum (VaN n w) = n. Proof eq_refl.
Lemma vmem_mem m w: vmem (VaM m w) = m. Proof eq_refl.
Lemma vwidth_num n w: vwidth (VaN n w) = w. Proof eq_refl.
Lemma vwidth_mem m w: vwidth (VaM m w) = w. Proof eq_refl.

Lemma fold_vget:
  forall u, VaU (vtyp u) (vmem u) (vnum u) (vwidth u) = vget u.
Proof. intro. destruct u as [u|]; [destruct u|]; reflexivity. Qed.


(* Unknowns are modeled as return values of an oracle function f that maps
   unknown-identifiers (binary positive numbers) to the values of each
   unknown.  In order to assign a unique unknown-identifier to each unknown
   appearing in the statement without preprocessing the statement to count
   them all, we use a trick from proofs about partitioning countably infinite
   domains:  To assign mutually exclusive identifiers to two expressions e1
   and e2, we assign only even identifiers to unknowns in e1 and only odd
   identifiers to unknowns in e2.  When this strategy is followed recursively,
   all unknowns get unique ids. *)

Definition unknowns0 f i : N := f (xO i).
Definition unknowns1 f i : N := f (xI i).
Definition unknowns00 f i : N := f (xO (xO i)).
Definition unknowns01 f i : N := f (xI (xO i)).
Definition unknowns10 f i : N := f (xO (xI i)).


(* The interpreter accumulates memory access predicates as a separate list
   of propositions during interpretation.  This allows the proof to infer
   memory accessibility facts from successful executions.  The list of
   propositions is later assembled into a conjunction, which is then split
   off into separate hypotheses in the proof context.  Sometimes it is
   useful to end the conjunction with a prop of "True" (to signal the end)
   while other times it is more succinct to not include the extra "True".
   We therefore define functions for both treatments. *)

Definition conjallT := List.fold_right and True.

Fixpoint conjall l :=
  match l with nil => True | P::nil => P | P::t => P /\ conjall t end.

Lemma conjallT_app:
  forall l1 l2, conjallT l1 -> conjallT l2 -> conjallT (l1++l2).
Proof.
  intros. revert H. induction l1; intros.
    assumption.
    split.
      apply H.
      apply IHl1. apply H.
Qed.

Lemma conjall_iffT:
  forall l, conjallT l <-> conjall l.
Proof.
  induction l.
    reflexivity.
    destruct l; split; intro H.
      apply H.
      split. apply H. exact I.
      split. apply H. apply IHl, H.
      split. apply H. apply IHl, H.
Qed.

Inductive NoE_SETOP :=
| NOE_ADD | NOE_SUB | NOE_MUL | NOE_DIV | NOE_MOD | NOE_POW
| NOE_SHL | NOE_SHR | NOE_AND | NOE_OR  | NOE_XOR | NOE_NOT
| NOE_NEG
| NOE_EQB | NOE_LTB | NOE_LEB
| NOE_SLT | NOE_SLE
| NOE_QUO | NOE_REM | NOE_ASR
| NOE_CAS
| NOE_ZST
| NOE_TYP
| NOE_NUM | NOE_WID
| NOE_MEM
| NOE_GET | NOE_SET.

Inductive NoE_TYPOP := NOE_ITR | NOE_UPD | NOE_MAR | NOE_MAW.



(* Functional interpretation of expressions and statements entails instantiating
   a functor that accepts the architecture-specific IL syntax and semantics. *)

Module Type PICINAE_FINTERP (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL).

Import IL.
Module PTheory := PicinaeTheory IL.
Import PTheory.
Import TIL.

Local Definition vupdate := @update var value VarEqDec.

(* Memory access propositions resulting from functional interpretation are
   encoded as (MemAcc (mem_readable|mem_writable) heap store addr length). *)
Definition MemAcc (P: store -> addr -> Prop) h s a len :=
  forall n, n < len -> h (a+n) = Some tt /\ P s (a+n).


(* For speed, the interpreter function is designed to be evaluated using
   vm_compute or native_compute.  However, those tactics perform uncontrolled
   expansion of every term, resulting in huge terms that are completely
   intractable for users (and very slow for Coq) to manipulate.  To control
   and limit this expansion, we create a Module that hides the expansions of
   functions we don't want vm_compute to evaluate.  After vm_compute completes,
   we replace the opaque functions with the real ones (using rewrite). *)

(* First, enumerate the various operations whose expansion we wish to inhibit,
   along with their type signatures.  We group these into two dependently
   typed functions (for ops in Set and Type, respectively) instead of many
   separate definitions for more efficient "rewrite" tactics. *)

Definition noe_setop_typsig op :=
  match op with
  | NOE_ADD | NOE_SUB | NOE_MUL | NOE_DIV | NOE_MOD | NOE_POW
  | NOE_SHL | NOE_SHR | NOE_AND | NOE_OR  | NOE_XOR | NOE_NOT => N -> N -> N
  | NOE_NEG => bool -> bool
  | NOE_EQB | NOE_LTB | NOE_LEB => N -> N -> bool
  | NOE_SLT | NOE_SLE => bitwidth -> N -> N -> bool
  | NOE_QUO | NOE_REM | NOE_ASR => bitwidth -> N -> N -> N
  | NOE_CAS => bitwidth -> bitwidth -> N -> N
  | NOE_ZST => addr -> N
  | NOE_TYP => value -> bool
  | NOE_NUM | NOE_WID => value -> N
  | NOE_MEM => value -> addr -> N
  | NOE_GET => endianness -> bitwidth -> (addr -> N) -> addr -> N
  | NOE_SET => endianness -> bitwidth -> (addr -> N) -> addr -> N -> addr -> N
  end.

Definition noe_setop op : noe_setop_typsig op :=
  match op with
  | NOE_ADD => N.add
  | NOE_SUB => N.sub
  | NOE_MUL => N.mul
  | NOE_DIV => N.div
  | NOE_MOD => N.modulo
  | NOE_POW => N.pow
  | NOE_SHL => N.shiftl
  | NOE_SHR => N.shiftr
  | NOE_AND => N.land
  | NOE_OR => N.lor
  | NOE_XOR => N.lxor
  | NOE_NOT => N.lnot
  | NOE_NEG => negb
  | NOE_EQB => N.eqb
  | NOE_LTB => N.ltb
  | NOE_LEB => N.leb
  | NOE_SLT => slt
  | NOE_SLE => sle
  | NOE_QUO => sbop Z.quot
  | NOE_REM => sbop Z.rem
  | NOE_ASR => ashiftr
  | NOE_CAS => scast
  | NOE_ZST => (fun (_:addr) => N0)
  | NOE_TYP => vtyp
  | NOE_NUM => vnum
  | NOE_WID => vwidth
  | NOE_MEM => vmem
  | NOE_GET => getmem
  | NOE_SET => setmem
  end.

Definition noe_typop_typsig op :=
  match op with
  | NOE_ITR => N -> forall A, (A -> A) -> A -> A
  | NOE_UPD => store -> var -> value -> store
  | NOE_MAR | NOE_MAW => hdomain -> store -> N -> N -> Prop
  end.

Definition noe_typop op : noe_typop_typsig op :=
  match op with
  | NOE_ITR => N.iter
  | NOE_UPD => @update var value VarEqDec
  | NOE_MAR => MemAcc mem_readable
  | NOE_MAW => MemAcc mem_writable
  end.

(* Now create a Module Type that hides the definitions within two Axioms. *)
Module Type NOEXPAND.
  Parameter f: forall op, noe_setop_typsig op.
  Parameter g: forall op, noe_typop_typsig op.

  Axiom f_eq: forall op, f op = match op with
  | NOE_ADD => N.add
  | NOE_SUB => N.sub
  | NOE_MUL => N.mul
  | NOE_DIV => N.div
  | NOE_MOD => N.modulo
  | NOE_POW => N.pow
  | NOE_SHL => N.shiftl
  | NOE_SHR => N.shiftr
  | NOE_AND => N.land
  | NOE_OR => N.lor
  | NOE_XOR => N.lxor
  | NOE_NOT => N.lnot
  | NOE_NEG => negb
  | NOE_EQB => N.eqb
  | NOE_LTB => N.ltb
  | NOE_LEB => N.leb
  | NOE_SLT => slt
  | NOE_SLE => sle
  | NOE_QUO => sbop Z.quot
  | NOE_REM => sbop Z.rem
  | NOE_ASR => ashiftr
  | NOE_CAS => scast
  | NOE_ZST => (fun (_:addr) => N0)
  | NOE_TYP => vtyp
  | NOE_NUM => vnum
  | NOE_WID => vwidth
  | NOE_MEM => vmem
  | NOE_GET => getmem
  | NOE_SET => setmem
  end.
  Axiom g_eq: forall op, g op = match op with
  | NOE_ITR => N.iter
  | NOE_UPD => @update var value VarEqDec
  | NOE_MAR => MemAcc mem_readable
  | NOE_MAW => MemAcc mem_writable
  end.
End NOEXPAND.

(* Instantiate the Module Type with our definitions. *)
Module NoE : NOEXPAND.
  Definition f := noe_setop.
  Definition g := noe_typop.

  Theorem f_eq op: f op = noe_setop op. Proof eq_refl.
  Theorem g_eq op: g op = noe_typop op. Proof eq_refl.
End NoE.

(* Implementation note:  The following tactic uses "rewrite" with a list of
   lemmas rather than using autorewrite or rewrite_strat because the former
   currently seems to be the fastest method (tested with Coq 8.8.2). *)

Ltac NoE_rewrite H :=
  rewrite
    ?NoE.f_eq, ?NoE.g_eq,
    ?vtyp_num, ?vtyp_mem,
    ?vnum_num, ?vmem_mem,
    ?vwidth_num, ?vwidth_mem,
    ?fold_vget
  in H.

Ltac NoE_rewrite_goal :=
  lazymatch goal with |- ?G =>
    let H := fresh in let Heq := fresh in remember G as H eqn:Heq; NoE_rewrite Heq; subst H
  end.


(* Functionally evaluate binary and unary operations using the opaque
   functions above. *)

Definition of_uvalue (u:uvalue) :=
  match u with VaU z m n w => if z then VaN n w else VaM m w end.

Definition utowidth (w n:N) : uvalue :=
  VaU true (NoE.f NOE_ZST) (NoE.f NOE_MOD n (NoE.f NOE_POW 2 w)) w.

Definition utobit (b:bool) : uvalue :=
  VaU true (NoE.f NOE_ZST) (if b then 1 else 0) 1.

Definition feval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : uvalue :=
  match bop with
  | OP_PLUS => utowidth w (NoE.f NOE_ADD n1 n2)
  | OP_MINUS => utowidth w (NoE.f NOE_SUB (NoE.f NOE_ADD (NoE.f NOE_POW 2 w) n1) n2)
  | OP_TIMES => utowidth w (NoE.f NOE_MUL n1 n2)
  | OP_DIVIDE => VaU true (NoE.f NOE_ZST) (NoE.f NOE_DIV n1 n2) w
  | OP_SDIVIDE => VaU true (NoE.f NOE_ZST) (NoE.f NOE_QUO w n1 n2) w
  | OP_MOD => VaU true (NoE.f NOE_ZST) (NoE.f NOE_MOD n1 n2) w
  | OP_SMOD => VaU true (NoE.f NOE_ZST) (NoE.f NOE_REM w n1 n2) w
  | OP_LSHIFT => utowidth w (NoE.f NOE_SHL n1 n2)
  | OP_RSHIFT => VaU true (NoE.f NOE_ZST) (NoE.f NOE_SHR n1 n2) w
  | OP_ARSHIFT => VaU true (NoE.f NOE_ZST) (NoE.f NOE_ASR w n1 n2) w
  | OP_AND => VaU true (NoE.f NOE_ZST) (NoE.f NOE_AND n1 n2) w
  | OP_OR => VaU true (NoE.f NOE_ZST) (NoE.f NOE_OR n1 n2) w
  | OP_XOR => VaU true (NoE.f NOE_ZST) (NoE.f NOE_XOR n1 n2) w
  | OP_EQ => utobit (NoE.f NOE_EQB n1 n2)
  | OP_NEQ => utobit (NoE.f NOE_NEG (NoE.f NOE_EQB n1 n2))
  | OP_LT => utobit (NoE.f NOE_LTB n1 n2)
  | OP_LE => utobit (NoE.f NOE_LEB n1 n2)
  | OP_SLT => utobit (NoE.f NOE_SLT w n1 n2)
  | OP_SLE => utobit (NoE.f NOE_SLE w n1 n2)
  end.

Definition feval_unop (uop:unop_typ) (n:N) (w:bitwidth) : uvalue :=
  match uop with
  | OP_NEG => utowidth w (NoE.f NOE_SUB (NoE.f NOE_POW 2 w) n)
  | OP_NOT => VaU true (NoE.f NOE_ZST) (NoE.f NOE_NOT n w) w
  end.

Definition feval_cast (c:cast_typ) (w w':bitwidth) (n:N) : N :=
  match c with
  | CAST_UNSIGNED => n
  | CAST_SIGNED => NoE.f NOE_CAS w w' n
  | CAST_HIGH => NoE.f NOE_SHR n (w - w')
  | CAST_LOW => NoE.f NOE_MOD n (NoE.f NOE_POW 2 w')
  end.

(* Functionally evaluate an expression.  Parameter unk is an oracle function
   that returns values of unknown expressions. *)
Fixpoint feval_exp e h s unk :=
  match e with
  | Var v => (VaU (NoE.f NOE_TYP (s vupdate v))
                  (NoE.f NOE_MEM (s vupdate v))
                  (NoE.f NOE_NUM (s vupdate v))
                  (NoE.f NOE_WID (s vupdate v)), nil)
  | Word n w => (VaU true (NoE.f NOE_ZST) n w, nil)
  | Load e1 e2 en len =>
      match feval_exp e1 h s (unknowns0 unk), feval_exp e2 h s (unknowns1 unk) with
      | (VaU _ m _ _, ma1), (VaU _ _ n _, ma2) =>
        (VaU true (NoE.f NOE_ZST) (NoE.f NOE_GET en len m n) (Mb*len),
         NoE.g NOE_MAR h (s (NoE.g NOE_UPD)) n len :: ma1++ma2)
      end
  | Store e1 e2 e3 en len =>
      match feval_exp e1 h s (unknowns00 unk), feval_exp e2 h s (unknowns01 unk), feval_exp e3 h s (unknowns10 unk) with
      | (VaU _ m _ mw, ma1), (VaU _ _ a _, ma2), (VaU _ _ v _, ma3) =>
        (VaU false (NoE.f NOE_SET en len m a v) 0 mw,
         NoE.g NOE_MAW h (s (NoE.g NOE_UPD)) a len :: ma1++ma2++ma3)
      end
  | BinOp bop e1 e2 =>
      match feval_exp e1 h s (unknowns0 unk), feval_exp e2 h s (unknowns1 unk) with
      | (VaU _ _ n1 w, ma1), (VaU _ _ n2 _, ma2) => (feval_binop bop w n1 n2, ma1++ma2)
      end
  | UnOp uop e1 =>
      match feval_exp e1 h s unk with (VaU _ _ n w, ma) =>
        (feval_unop uop n w, ma)
      end
  | Cast c w' e1 =>
      match feval_exp e1 h s unk with (VaU _ _ n w, ma) =>
        (VaU true (NoE.f NOE_ZST) (feval_cast c w w' n) w', ma)
      end
  | Let v e1 e2 =>
      match feval_exp e1 h s (unknowns0 unk) with (u,ma1) =>
        match feval_exp e2 h (fun upd => upd (s upd) v (of_uvalue u)) (unknowns1 unk) with
        | (u',ma2) => (u', ma1++ma2)
        end
      end
  | Unknown w => (VaU true (NoE.f NOE_ZST) (NoE.f NOE_MOD (unk xH) (NoE.f NOE_POW 2 w)) w, nil)
  | Ite e1 e2 e3 =>
      match feval_exp e1 h s (unknowns0 unk), feval_exp e2 h s (unknowns1 unk), feval_exp e3 h s (unknowns1 unk) with
      | (VaU _ _ n1 _, ma1), (VaU b2 m2 n2 w2, ma2), (VaU b3 m3 n3 w3, ma3) =>
        (VaU (if n1 then b3 else b2) (if n1 then m3 else m2) (if n1 then n3 else n2) (if n1 then w3 else w2),
         match ma2,ma3 with nil,nil => ma1 | _,_ => ma1++(if n1 then conjall ma3 else conjall ma2)::nil end)
      end
  | Extract n1 n2 e1 =>
      match feval_exp e1 h s unk with
      | (VaU _ _ n w, ma) => (VaU true (NoE.f NOE_ZST) (feval_cast CAST_HIGH (N.succ n1) (N.succ (n1-n2))
                                                       (feval_cast CAST_LOW w (N.succ n1) n)) (N.succ (n1-n2)), ma)
      end
  | Concat e1 e2 =>
      match feval_exp e1 h s (unknowns0 unk), feval_exp e2 h s (unknowns1 unk) with
      | (VaU _ _ n1 w1, ma1), (VaU _ _ n2 w2, ma2) =>
        (VaU true (NoE.f NOE_ZST) (NoE.f NOE_OR (NoE.f NOE_SHL n1 w2) n2) (w1+w2), ma1++ma2)
      end
  end.


(* Convert a list of variables and their values to a store function. *)
Fixpoint updlst s (l: list (var * value)) upd : store :=
  match l with nil => s | (v,u)::t => upd (updlst s t upd) v u end.

(* Remove a variable from a list of variables and their values. *)
Fixpoint remlst v l : list (var * value) :=
  match l with nil => nil | (v',u)::t => if v == v' then t else (v',u)::(remlst v t) end.


(* The statement interpreter returns a list of known variables and their values,
   a "continuation" state (which is either an exit or a new statement that, if
   interpreted, would yield the final state), and a list of memory access props.
   Returning a statement-continuation allows the interpreter to stop interpretation
   early if it encounters a conditional or loop that requires a tactic-level
   case-distinction or induction before interpretation can proceed.  This prevents
   the interpreted term from blowing up into a huge conditional expression in which
   every possible branch is fully expanded. *)

Inductive finterp_cont := FIExit (x: option exit) | FIStmt (q: stmt).

Inductive finterp_state :=
| FIS (l: list (var * value)) (xq: finterp_cont) (ma: list Prop).

Fixpoint fexec_stmt q h s unk l :=
  match q with
  | Nop => FIS l (FIExit None) nil
  | Move v e => match feval_exp e h (updlst s l) unk with
                | (u,ma) => FIS ((v, of_uvalue u)::remlst v l) (FIExit None) ma
                end
  | Jmp e => match feval_exp e h (updlst s l) unk with
             | (VaU _ _ n _, ma) => FIS l (FIExit (Some (Exit n))) ma
             end
  | Exn i => FIS l (FIExit (Some (Raise i))) nil
  | Seq q1 q2 =>
      match fexec_stmt q1 h s (unknowns0 unk) l with
      | FIS l1 (FIStmt q1') ma1 => FIS l1 (FIStmt (Seq q1' q2)) ma1
      | FIS l1 (FIExit (Some x1)) ma1 => FIS l1 (FIExit (Some x1)) ma1
      | FIS l1 (FIExit None) ma1 => match fexec_stmt q2 h s (unknowns1 unk) l1 with
                                    | FIS l2 qx2 ma2 => FIS l2 qx2 (ma1++ma2)
                                    end
      end
  | If e q1 q2 =>
      match feval_exp e h (updlst s l) unk with (VaU _ _ n _, ma0) =>
        FIS l (FIStmt (if n then q2 else q1)) ma0
      end
  | Rep e q1 =>
      match feval_exp e h (updlst s l) unk with (VaU _ _ n _, ma0) =>
        FIS l (FIStmt (NoE.g NOE_ITR n stmt (Seq q1) Nop)) ma0
      end
  end.


(* Now we prove that the functional interpreter obeys the operational semantics.
   The proved theorems can be used as tactics that convert eval_exp and exec_stmt
   propositions to feval_exp and fexec_stmt functions that can be evaluated using
   vm_compute or other reduction tactics. *)

Theorem reduce_exp:
  forall h e s u (E: eval_exp h (s vupdate) e u),
  exists unk, match feval_exp e h s unk with (u',ma) =>
    u = of_uvalue u' /\ conjallT ma end.
Proof.
  induction e; intros; inversion E; clear E; subst.

  (* Var *)
  exists (fun _ => N0). split.
    simpl. NoE_rewrite_goal. destruct (s vupdate v); reflexivity.
    exact I.

  (* Word *)
  exists (fun _ => N0). split.
    reflexivity.
    exact I.

  (* Load *)
  apply IHe1 in E1. apply IHe2 in E2. clear IHe1 IHe2.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2].
  exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
  unfold feval_exp; fold feval_exp. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
  destruct (feval_exp e1 _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  destruct (feval_exp e2 _ _ _) as (u2,ma2). destruct u2. destruct E2 as [U2 M2].
  simpl in U1,U2. destruct z; destruct z0; try discriminate. injection U1; injection U2; intros; subst.
  NoE_rewrite_goal. split.
    reflexivity.
    split.
      exact R.
      apply conjallT_app; assumption.

  (* Store *)
  apply IHe1 in E1. apply IHe2 in E2. apply IHe3 in E3. clear IHe1 IHe2 IHe3.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2]. destruct E3 as [unk3 E3].
  exists (fun i => match i with xO (xO j) => unk1 j | xI (xO j) => unk2 j | xO (xI j) => unk3 j | _ => N0 end).
  unfold feval_exp; fold feval_exp. change (unknowns00 _) with unk1. change (unknowns01 _) with unk2. change (unknowns10 _) with unk3.
  destruct (feval_exp e1 _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  destruct (feval_exp e2 _ _ _) as (u2,ma2). destruct u2. destruct E2 as [U2 M2].
  destruct (feval_exp e3 _ _ _) as (u3,ma3). destruct u3. destruct E3 as [U3 M3].
  simpl in U1,U2,U3. destruct z; destruct z0; destruct z1; try discriminate. injection U1; injection U2; injection U3; intros; subst.
  NoE_rewrite_goal. split.
    reflexivity.
    split.
      exact W.
      repeat try apply conjallT_app; assumption.

  (* BinOp *)
  apply IHe1 in E1. apply IHe2 in E2. clear IHe1 IHe2.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2].
  exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
  unfold feval_exp; fold feval_exp. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
  destruct (feval_exp e1 _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  destruct (feval_exp e2 _ _ _) as (u2,ma2). destruct u2. destruct E2 as [U2 M2].
  simpl in U1,U2. destruct z; destruct z0; try discriminate. injection U1; injection U2; intros; subst.
  split.
    destruct b; simpl; NoE_rewrite_goal; reflexivity.
    apply conjallT_app; assumption.

  (* UnOp *)
  apply IHe in E1. clear IHe.
  destruct E1 as [unk1 E1].
  exists unk1.
  unfold feval_exp; fold feval_exp.
  destruct (feval_exp e _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  split.
    destruct u; simpl; NoE_rewrite_goal; reflexivity.
    assumption.

  (* Cast *)
  apply IHe in E1. clear IHe.
  destruct E1 as [unk1 E1].
  exists unk1.
  unfold feval_exp; fold feval_exp.
  destruct (feval_exp e _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  split.
    destruct c; simpl; NoE_rewrite_goal; reflexivity.
    assumption.

  (* Let *)
  change (s vupdate [v:=u1]) with ((fun upd => upd (s upd) v u1) vupdate) in E2.
  apply IHe1 in E1. apply IHe2 in E2. clear IHe1 IHe2.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2].
  exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
  unfold feval_exp; fold feval_exp. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
  destruct (feval_exp e1 _ _ _) as (u0,ma1). destruct E1 as [U1 M1]. subst.
  destruct (feval_exp e2 _ _ _) as (u2,ma2). destruct E2 as [U2 M2]. subst.
  split.
    reflexivity.
    apply conjallT_app; assumption.

  (* Unknown *)
  exists (fun _ => n).
  unfold feval_exp; fold feval_exp.
  simpl. NoE_rewrite_goal. split.
    rewrite N.mod_small by assumption. reflexivity.
    exact I.

  (* Ife *)
  apply IHe1 in E1. clear IHe1. destruct E1 as [unk1 E1].
  destruct n1.

    apply IHe3 in E'. clear IHe2 IHe3. destruct E' as [unk3 E3].
    exists (fun i => match i with xO j => unk1 j | xI j => unk3 j | _ => N0 end).
    unfold feval_exp; fold feval_exp. change (unknowns0 _) with unk1. change (unknowns1 _) with unk3.
    destruct (feval_exp e1 _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
    destruct (feval_exp e3 _ _ _) as (u3,ma3). destruct u3. destruct E3 as [U3 M3]. subst.
    simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
    destruct (feval_exp e2 _ _ _) as (u2,ma2). destruct u2.
    split.
      reflexivity.
      destruct ma2; destruct ma3.
        assumption.
        apply conjallT_app. assumption. split. apply conjall_iffT. assumption. exact I.
        apply conjallT_app. assumption. split; exact I.
        apply conjallT_app. assumption. split. apply conjall_iffT. assumption. exact I.

    apply IHe2 in E'. clear IHe2 IHe3. destruct E' as [unk2 E2].
    exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
    unfold feval_exp; fold feval_exp. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
    destruct (feval_exp e1 _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
    destruct (feval_exp e2 _ _ _) as (u2,ma2). destruct u2. destruct E2 as [U2 M2]. subst.
    simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
    destruct (feval_exp e3 _ _ _) as (u3,ma3). destruct u3.
    split.
      reflexivity.
      destruct ma3; destruct ma2.
        assumption.
        apply conjallT_app. assumption. split. apply conjall_iffT. assumption. exact I.
        apply conjallT_app. assumption. split; exact I.
        apply conjallT_app. assumption. split. apply conjall_iffT. assumption. exact I.

  (* Extract *)
  apply IHe in E1. clear IHe.
  destruct E1 as [unk1 E1].
  exists unk1.
  unfold feval_exp; fold feval_exp.
  destruct (feval_exp e _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  split.
    simpl. NoE_rewrite_goal. reflexivity.
    assumption.

  (* Concat *)
  apply IHe1 in E1. apply IHe2 in E2. clear IHe1 IHe2.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2].
  exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
  unfold feval_exp; fold feval_exp. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
  destruct (feval_exp e1 _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  destruct (feval_exp e2 _ _ _) as (u2,ma2). destruct u2. destruct E2 as [U2 M2].
  simpl in U1,U2. destruct z; destruct z0; try discriminate. injection U1; injection U2; intros; subst.
  split.
    simpl. NoE_rewrite_goal. reflexivity.
    apply conjallT_app; assumption.
Qed.

Lemma updlst_remlst:
  forall v u l s, updlst s (remlst v l) vupdate [v:=u] = updlst s l vupdate [v:=u].
Proof.
  induction l; intros.
    reflexivity.
    destruct a as (v1,u1). simpl. destruct (vareq v v1).
      subst. unfold vupdate at 2. rewrite update_cancel. reflexivity.
      simpl. unfold vupdate at 1 3. rewrite update_swap.
        rewrite IHl. rewrite update_swap by assumption. reflexivity.
        intro H. apply n. symmetry. exact H.
Qed.

Theorem reduce_stmt:
  forall s l q h s' x (XS: exec_stmt h (updlst s l vupdate) q s' x),
  exists unk, match fexec_stmt q h s unk l with
              | FIS l' (FIExit x') ma => (s' = updlst s l' (NoE.g NOE_UPD) /\ x = x') /\ conjallT ma
              | FIS l' (FIStmt q') ma => exec_stmt h (updlst s l' (NoE.g NOE_UPD)) q' s' x /\ conjallT ma
              end.
Proof.
  NoE_rewrite_goal.
  intros s l q h. revert s l. induction q using stmt_ind2; intros;
  inversion XS; clear XS; subst.

  (* Nop *)
  exists (fun _ => N0).
  simpl. repeat split.

  (* Move *)
  apply reduce_exp in E. destruct E as [unk E]. exists unk.
  simpl. destruct (feval_exp _ _ _ _) as (u1,ma1).
  destruct E as [U1 M1]. subst.
  repeat split.
    simpl. rewrite updlst_remlst. reflexivity.
    exact M1.

  (* Jmp *)
  apply reduce_exp in E. destruct E as [unk E]. exists unk.
  simpl. destruct (feval_exp _ _ _ _) as (u1,ma1). destruct u1.
  destruct E as [U1 M1]. simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  repeat split. exact M1.

  (* Exn *)
  exists (fun _ => N0).
  simpl. repeat split.

  (* Seq1 *)
  apply IHq1 in XS0. clear IHq1. destruct XS0 as [unk XS1].
  exists (fun i => match i with xO j => unk j | _ => N0 end).
  simpl. change (unknowns0 _) with unk.
  destruct (fexec_stmt _ _ _ _ _) as [l1 [x1|q1'] ma1].
    destruct XS1 as [[S1 X1] M1]. subst. repeat split. exact M1.
    split; try apply XSeq1; apply XS1.

  (* Seq2 *)
  apply IHq1 in XS1. clear IHq1. destruct XS1 as [unk1 XS1].
  destruct (fexec_stmt q1 _ _ _ _) as [l1 [x1|q1'] ma1] eqn:FS1.

    destruct XS1 as [[S1 X1] M1]. subst.
    apply IHq2 in XS0. clear IHq2. destruct XS0 as [unk2 XS2].
    exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
    simpl. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
    rewrite FS1.
    destruct (fexec_stmt q2 _ _ _ _) as [l2 [x2|q2'] ma2].
      destruct XS2 as [[S2 X2] M2]. subst. repeat split. apply conjallT_app; assumption.
      split. apply XS2. apply conjallT_app. exact M1. apply XS2.

    exists (fun i => match i with xO j => unk1 j | _ => N0 end).
    simpl. change (unknowns0 _) with unk1. rewrite FS1.
    split. eapply XSeq2. apply XS1. assumption. apply XS1.

  (* If *)
  apply reduce_exp in E. destruct E as [unk E].
  exists unk. simpl.
  destruct (feval_exp _ _ _ _) as [u ma0].
  destruct E as [E M]. destruct u as [z m n w]. destruct z; [|discriminate]. injection E; intros; subst.
  split; assumption.

  (* Rep *)
  apply reduce_exp in E. destruct E as [unk E].
  exists unk. simpl.
  destruct (feval_exp _ _ _ _) as [u ma0].
  destruct E as [E M]. destruct u as [z m c ?]. destruct z; [|discriminate]. injection E; intros; subst.
  NoE_rewrite_goal. split; assumption.
Qed.

Theorem update_updlst:
  forall upd s v u l,
  updlst (upd s v u) (rev l) upd = updlst s (rev ((v,u)::l)) upd.
Proof.
  intros. simpl. generalize (rev l) as l'. induction l'.
    reflexivity.
    simpl. rewrite IHl'. reflexivity.
Qed.


(* Using the functional interpreter, we now define a set of tactics that reduce
   expressions to values, and statements to stores & exits.  These tactics are
   carefully implemented to avoid simplifying anything other than the machinery
   of the functional interpreter, so that Coq does not spin out of control
   attempting to execute the entire program.  Our objective is to infer a
   reasonably small, well-formed symbolic expression that captures the result
   of executing each assembly instruction.  This result can be further reduced
   by the user (e.g., using "simpl") if desired. *)

(* Statement simplification most often gets stuck at variable-reads, since the
   full content of the store is generally not known (s is a symbolic expression).
   We can often push past this obstacle by applying the update_updated and
   update_frame theorems to automatically infer that the values of variables not
   being read are irrelevant.  The "simpl_stores" tactic does so. *)

Remark if_N_same: forall A (n:N) (a:A), (if n then a else a) = a.
Proof. intros. destruct n; reflexivity. Qed.

Ltac simpl_stores :=
  repeat first [ rewrite update_updated | rewrite update_frame; [|discriminate 1] ];
  repeat rewrite if_N_same;
  repeat match goal with |- context [ update ?S ?V ?U ] =>
    match S with context c [ update ?T V _ ] => let r := context c[T] in
      replace (update S V U) with (update r V U) by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.

Tactic Notation "simpl_stores" "in" hyp(H) :=
  repeat lazymatch type of H with context [ update _ ?v _ ?v ] => rewrite update_updated in H
                                | context [ update _ _ _ _ ] => rewrite update_frame in H; [|discriminate 1] end;
  repeat rewrite if_N_same in H;
  repeat match type of H with context [ update ?S ?V ?U ] =>
    match S with context c [ update ?T V _ ] => let r := context c[T] in
      replace (update S V U) with (update r V U) in H by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.


(* To facilitate expression simplification, it is often convenient to first
   consolidate all information about known variable values into the expression
   to be simplified.  The "stock_store" tactic searches the proof context for
   hypotheses of the form "s var = value", where "var" is some variable
   appearing in the expression to be reduced and "s" is the store, and adds
   "s[var:=value]" to the expression.  If no such hypothesis is found for var,
   it next looks for "models c s" where c is a typing context that assigns a
   type to var.  If such a hypothesis exists, it creates a fresh name for the
   value of var with the correct type.

   Note: "stock_store" is no longer called by the functional interpreter.  The
   interpreter now performs this task as part of populate_varlist, which is
   faster.  However, we keep stock_store available in stand-alone form in case
   the user wants to consolidate store info manually. *)

Theorem models_val:
  forall v s t (TV: hastyp_val (s v) t),
  match t with
  | NumT w => exists n, s = s [v := VaN n w]
  | MemT w => exists m, s = s [v := VaM m w]
  end.
Proof.
  intros. destruct t; inversion TV; subst;
  eexists; apply store_upd_eq; symmetry; eassumption.
Qed.

Ltac stock_store :=
  lazymatch goal with |- exec_stmt _ _ ?q _ _ => repeat
    match q with context [ Var ?v ] =>
      lazymatch goal with |- exec_stmt _ ?s _ _ _ =>
        lazymatch s with context [ update _ v _ ] => fail | _ => first
        [ erewrite (store_upd_eq s v) by (simpl_stores; eassumption)
        | match goal with [ MDL: models ?c _ |- _ ] => let H := fresh in
            lazymatch eval hnf in (c v) with
            | Some (NumT ?w) => destruct (models_val v s (NumT w)) as [?n H]
            | Some (MemT ?w) => destruct (models_val v s (MemT w)) as [?m H]
            end;
            [ solve [ simpl_stores; apply MDL; reflexivity ]
            | rewrite H; clear H ]
          end ]
        end
      end
    end
  | _ => fail "Goal is not of the form (exec_stmt ...)"
  end.

Tactic Notation "stock_store" "in" hyp(XS) :=
  lazymatch type of XS with exec_stmt _ _ ?q _ _ => repeat
    match q with context [ Var ?v ] =>
      lazymatch type of XS with exec_stmt _ ?s _ _ _ =>
        lazymatch s with context [ update _ v _ ] => fail | _ => first
        [ erewrite (store_upd_eq s v) in XS by (simpl_stores; eassumption)
        | match goal with [ MDL: models ?c _ |- _ ] => let H := fresh in
            lazymatch eval hnf in (c v) with
            | Some (NumT ?w) => destruct (models_val v s (NumT w)) as [?n H]
            | Some (MemT ?w) => destruct (models_val v s (MemT w)) as [?m H]
            end;
            [ solve [ simpl_stores; apply MDL; reflexivity ]
            | rewrite H in XS; clear H ]
          end ]
        end
      end
    end
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.


(* To prevent vm_compute from expanding symbolic expressions that the user
   already has in a desired form, the following lemmas introduce symbolic
   constants for those expressions and sets them equal to the original terms.
   The "destruct" tactic can then be used to separate those terms out into
   a different hypothesis to which vm_compute is not applied, and then use
   "subst" to substitute them back into the evaluated term after vm_compute
   is done. *)

Lemma fexec_stmt_init:
  forall h s q s' x (XS: exec_stmt h s q s' x),
  exec_stmt h (updlst s (rev nil) vupdate) q s' x /\ True.
Proof. split. assumption. exact I. Qed.

Lemma fexec_stmt_updn:
  forall h s v n w l q s' x EQs,
  exec_stmt h (updlst (vupdate s v (VaN n w)) (rev l) vupdate) q s' x /\ EQs ->
  exists a, exec_stmt h (updlst s (rev ((v, VaN a w)::l)) vupdate) q s' x /\ (a=n /\ EQs).
Proof.
  intros. exists n. split.
    rewrite <- update_updlst. apply H.
    split. reflexivity. apply H.
Qed.

Lemma fexec_stmt_updm:
  forall h s v m w l q s' x EQs,
  exec_stmt h (updlst (vupdate s v (VaM m w)) (rev l) vupdate) q s' x /\ EQs ->
  exists a, exec_stmt h (updlst s (rev ((v, VaM a w)::l)) vupdate) q s' x /\ (a=m /\ EQs).
Proof.
  intros. exists m. split.
    rewrite <- update_updlst. apply H.
    split. reflexivity. apply H.
Qed.

Lemma fexec_stmt_updu:
  forall h s v u l q s' x EQs,
  exec_stmt h (updlst (vupdate s v u) (rev l) vupdate) q s' x /\ EQs ->
  exists a, exec_stmt h (updlst s (rev ((v,u)::l)) vupdate) q s' x /\ (a=u /\ EQs).
Proof.
  intros. exists u. split.
    rewrite <- update_updlst. apply H.
    split. reflexivity. apply H.
Qed.

Lemma fexec_stmt_hypn:
  forall h s v n w l q s' x EQs (SV: s v = VaN n w),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ EQs ->
  exists a, exec_stmt h (updlst s (rev ((v, VaN a w)::l)) vupdate) q s' x /\ (a=n /\ EQs).
Proof.
  intros. exists n. split.
    rewrite <- update_updlst. change (vupdate s) with (update s). rewrite <- store_upd_eq by exact SV. apply H.
    split. reflexivity. apply H.
Qed.

Lemma fexec_stmt_hypm:
  forall h s v m w l q s' x EQs (SV: s v = VaM m w),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ EQs ->
  exists a, exec_stmt h (updlst s (rev ((v, VaM a w)::l)) vupdate) q s' x /\ (a=m /\ EQs).
Proof.
  intros. exists m. split.
    rewrite <- update_updlst. change (vupdate s) with (update s). rewrite <- store_upd_eq by exact SV. apply H.
    split. reflexivity. apply H.
Qed.

Lemma fexec_stmt_hypu:
  forall h s v u l q s' x EQs (SV: s v = u),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ EQs ->
  exists a, exec_stmt h (updlst s (rev ((v,u)::l)) vupdate) q s' x /\ (a=u /\ EQs).
Proof.
  intros. exists u. split.
    rewrite <- update_updlst. change (vupdate s) with (update s). rewrite <- store_upd_eq by exact SV. apply H.
    split. reflexivity. apply H.
Qed.

Lemma fexec_stmt_typ:
  forall h c s v t l q s' x EQs (MDL: models c s) (CV: c v = Some t),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ EQs ->
  match t with NumT w => exists a, s v = VaN a w /\ exec_stmt h (updlst s (rev ((v, VaN a w)::l)) vupdate) q s' x /\ EQs
             | MemT w => exists a, s v = VaM a w /\ exec_stmt h (updlst s (rev ((v, VaM a w)::l)) vupdate) q s' x /\ EQs
  end.
Proof.
  intros. specialize (MDL _ _ CV). inversion MDL; subst;
  eexists; rewrite <- update_updlst;
  change (vupdate s) with (update s);
  rewrite <- store_upd_eq by (symmetry; eassumption);
  (split; [ reflexivity | exact H ]).
Qed.


(* Prepare an exec_stmt hypothesis for the symbolic interpreter by converting
   its store argument s into an expression of the form (updlst s0 l), where
   s0 is a store expression and l is a list of variable-value pairs. By passing
   list l directly to the interpreter as a functional input, it can reduce many
   variables to values without consulting the proof context (which it cannot
   access programmatically) and without risking uncontrolled expansion of the
   potentially complex original store expression s.  Members of list l can come
   from three potential sources of information:

   (1) If s has the form "s0[v1:=u1]...[vn:=un]", then (v1,u1),...,(vn,un) are
       added to list l and s is reduced to s0.

   (2) For each hypothesis of the form "s0 v = u", pair (v,u) is added to l.

   (3) For any remaining variable v read by the statement being interpreted
       whose value cannot be inferred by the above, if there is a hypothesis of
       the form "models c s0" and typing context c assigns a type to v, then a
       fresh proof variable is introduced for the value of v having appropriate
       IL-type.  This allows the interpreter to at least infer the type of v
       (including, most importantly, its bitwidth), which typically yields a
       symbolic expression that is much simpler because it doesn't need to
       generalize over bitwidths. *)

Ltac populate_varlist XS :=
  apply fexec_stmt_init in XS;
  repeat lazymatch type of XS with
  | exec_stmt ?h (updlst (update ?s ?v (VaN ?n ?w)) (rev ?l) vupdate) ?q ?s' ?x /\ ?EQs =>
      simple apply (fexec_stmt_updn h s v n w l q s' x EQs) in XS;
      let _n := fresh in destruct XS as [_n XS]
  | exec_stmt ?h (updlst (update ?s ?v (VaM ?m ?w)) (rev ?l) vupdate) ?q ?s' ?x /\ ?EQs =>
      simple apply (fexec_stmt_updm h s v m w l q s' x EQs) in XS;
      let _m := fresh in destruct XS as [_m XS]
  | exec_stmt ?h (updlst (update ?s ?v ?u) (rev ?l) vupdate) ?q ?s' ?x /\ ?EQs =>
      simple apply (fexec_stmt_updu h s v u l q s' x EQs) in XS;
      let _u := fresh in destruct XS as [_u XS]
  end;
  repeat lazymatch type of XS with exec_stmt ?h (updlst ?s (rev ?l) vupdate) ?q ?s' ?x /\ ?EQs =>
    match q with context [ Var ?v ] =>
      lazymatch l with context [ (v,_)::_ ] => fail | _ =>
        match goal with
        | [ SV: s v = VaN ?n ?w |- _ ] =>
            simple apply (fexec_stmt_hypn h s v n w l q s' x EQs SV) in XS;
            let _n := fresh in destruct XS as [_n XS]
        | [ SV: s v = VaM ?m ?w |- _ ] =>
            simple apply (fexec_stmt_hypm h s v m w l q s' x EQs SV) in XS;
            let _m := fresh in destruct XS as [_m XS]
        | [ MDL: models ?c s |- _ ] =>
            lazymatch eval hnf in (c v) with Some ?t =>
              simple apply (fexec_stmt_typ h c s v t l q s' x EQs MDL (eq_refl _)) in XS;
              let _a := match t with NumT _ => fresh "n" | MemT _ => fresh "m" end in
              let H := fresh "Hsv" in
                destruct XS as [_a [H XS]]
            end
        end
      end
    end
  end.


(* Finally, simplifying a hypothesis H of the form (exec_stmt ...) entails first
   removing any user-supplied expressions in H that we don't want expanded, then
   applying the reduce_stmt theorem to convert it into an fexec_stmt expression,
   launching vm_compute on it, then abstracting any unknowns as unique proof
   context variables, and finally substituting any removed or opaque expressions
   back into the evaluated expression. *)

Ltac step_stmt XS :=
  lazymatch type of XS with exec_stmt _ _ _ _ _ =>
    populate_varlist XS;
    let EQs := fresh in destruct XS as [XS EQs];
    lazymatch type of XS with exec_stmt ?h (updlst ?s _ _) _ ?s' ?x =>
      let _h  := fresh in remember h  as _h  in XS;
      let _s  := fresh in remember s  as _s  in XS;
      let _s' := fresh in remember s' as _s' in XS;
      let _x  := fresh in remember x  as _x  in XS;
      apply reduce_stmt in XS;
      let unk := fresh "unknown" in (
        destruct XS as [unk XS];
        vm_compute in XS;
        repeat match type of XS with context [ unk ?i ] =>
          let u := fresh "u" in set (u:=unk i) in XS; clearbody u
        end;
        try clear unk
      );
      NoE_rewrite XS;
      subst _h _s _s' _x
    end;
    repeat lazymatch type of EQs with (?_nmu = _) /\ _ =>
      let H1 := fresh in destruct EQs as [H1 EQs]; subst _nmu
    end;
    clear EQs
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.


(* We can then break the memory access part of XS resulting from step_stmt into
   separate hypotheses.  This is provided as a separate tactic because often
   the user may want to perform some sort of simplification before splitting. *)

Ltac destruct_memaccs XS :=
  let ACCs := fresh "ACCs" in
    destruct XS as [XS ACCs];
    repeat lazymatch type of ACCs with
    | ?H1 /\ _ =>
        lazymatch goal with [ H0:H1 |- _ ] => apply proj2 in ACCs
        | _ => let ACC := fresh "ACC" in destruct ACCs as [ACC ACCs]
        end
    | True => clear ACCs
    | _ => let ACC := fresh "ACC" in rename ACCs into ACC
    end.

End PICINAE_FINTERP.


Module PicinaeFInterp (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL) <: PICINAE_FINTERP IL TIL.
  Include PICINAE_FINTERP IL TIL.
End PicinaeFInterp.

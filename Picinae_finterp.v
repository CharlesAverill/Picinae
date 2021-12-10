(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2021 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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

Require Import Picinae_theory.
Require Import Picinae_statics.
Require Import NArith.
Require Import ZArith.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Etacs.

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
| NOE_PARITY8
| NOE_CAS
| NOE_BAND
| NOE_ZST
| NOE_TYP
| NOE_NUM | NOE_WID
| NOE_MEM
| NOE_GET | NOE_SET.

Inductive NoE_TYPOP := NOE_ITR | NOE_UPD | NOE_MAR | NOE_MAW.

Definition noe_setop_typsig op :=
  match op with
  | NOE_ADD | NOE_SUB | NOE_MUL | NOE_DIV | NOE_MOD | NOE_POW
  | NOE_SHL | NOE_SHR | NOE_AND | NOE_OR  | NOE_XOR | NOE_NOT => N -> N -> N
  | NOE_NEG => bool -> bool
  | NOE_EQB | NOE_LTB | NOE_LEB => N -> N -> bool
  | NOE_SLT | NOE_SLE => bitwidth -> N -> N -> bool
  | NOE_QUO | NOE_REM | NOE_ASR => bitwidth -> N -> N -> N
  | NOE_PARITY8 => N -> N
  | NOE_CAS => bitwidth -> bitwidth -> N -> N
  | NOE_BAND => bool -> bool -> bool
  | NOE_ZST => addr -> N
  | NOE_TYP => value -> bool
  | NOE_NUM | NOE_WID => value -> N
  | NOE_MEM => value -> addr -> N
  | NOE_GET => endianness -> bitwidth -> (addr -> N) -> addr -> N
  | NOE_SET => endianness -> bitwidth -> (addr -> N) -> addr -> N -> addr -> N
  end.

Definition parity8 n :=
  N.lnot ((N.lxor
    (N.shiftr (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
                      (N.lxor (N.shiftr n 4) n)) 1)
    (N.lxor (N.shiftr (N.lxor (N.shiftr n 4) n) 2)
            (N.lxor (N.shiftr n 4) n))) mod 2^1) 1.



(* Functional interpretation of expressions and statements entails instantiating
   a functor that accepts the architecture-specific IL syntax and semantics. *)

Module Type PICINAE_FINTERP_DEFS (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL).

Import IL.
Import TIL.

Definition vupdate := @update var value VarEqDec.

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
   we replace the opaque functions with the real ones (using cbv). *)

(* First, enumerate the various operations whose expansion we wish to inhibit,
   along with their type signatures.  We group these into two dependently
   typed functions (for ops in Set and Type, respectively) instead of many
   separate definitions for more efficient expansion tactics. *)

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
  | NOE_QUO => sbop2 Z.quot
  | NOE_REM => sbop2 Z.rem
  | NOE_ASR => ashiftr
  | NOE_CAS => scast
  | NOE_PARITY8 => parity8
  | NOE_BAND => andb
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

(* Decide whether an expression e's type is statically known given a list l of
   variables and their values, and return its bitwidth if so.  When e's result
   type can be statically predicted, the functional interpreter can expand and
   reduce much more of the expression, yielding smaller terms and improving speed.
   The type inferred here is the type of the value yielded by evaluating e even
   if e is not well-typed according to the static semantics.  This allows the
   functional interpreter to work without requiring the user to supply a proof
   of well-typedness for e. *)

Definition feval_varwidth l v :=
  option_map (fun p => vwidth (snd p)) (find (fun p => if v == fst p then true else false) l).
Arguments feval_varwidth !l / v.

Fixpoint feval_width (l:list (var*value)) e {struct e} :=
  match e with
  | Var v => feval_varwidth l v
  | Word _ w | Cast _ w _ | Unknown w => Some w
  | Load _ _ _ len => Some (Mb*len)
  | Store e1 _ _ _ _ | UnOp _ e1 => feval_width l e1
  | BinOp bop e1 _ =>
    match bop with
    | OP_PLUS | OP_MINUS | OP_TIMES | OP_DIVIDE | OP_SDIVIDE | OP_MOD | OP_SMOD
    | OP_LSHIFT | OP_RSHIFT | OP_ARSHIFT | OP_AND | OP_OR | OP_XOR => feval_width l e1
    | OP_EQ | OP_NEQ | OP_LT | OP_LE | OP_SLT | OP_SLE => Some 1
    end
  | Let v e1 e2 => feval_width
      match feval_width l e1 with
      | None => filter (fun p => if v == fst p then false else true) l
      | Some w => (v,VaN 0 w)::l
      end e2
  | Ite _ e2 e3 => match feval_width l e2 with None => None | Some w1 =>
                     match feval_width l e3 with None => None | Some w2 =>
                       if w1 =? w2 then Some w1 else None
                     end
                   end
  | Extract n1 n2 _ => Some (N.succ n1 - n2)
  | Concat e1 e2 => match feval_width l e1 with None => None | Some w1 =>
                      option_map (N.add w1) (feval_width l e2)
                    end
  end.

(* The following implements a safety check that can optionally be executed prior
   to evaluating a stmt to warn the user that the term is likely to blow up due
   to unknown-type subexpressions.  Unknown types usually arise from references
   to IL variables not in the typing context.  This usually indicates a missing
   "models" hypothesis or read from an uninitialized temp var. *)

Fixpoint feval_check (l:list (var*value)) e {struct e} :=
  match e with
  | Var v => match feval_varwidth l v with None => Some e | Some _ => None end
  | Word _ _ | Unknown _ => None
  | Load e1 e2 _ _ | BinOp _ e1 e2 | Concat e1 e2 =>
      match feval_check l e1 with Some e' => Some e' | None => feval_check l e2 end
  | Store e1 e2 e3 _ _ =>
      match feval_check l e1 with Some e' => Some e' | None =>
        match feval_check l e2 with Some e' => Some e' | None =>
          feval_check l e3
        end
      end
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => feval_check l e1
  | Let v e1 e2 =>
      match feval_check l e1 with Some e' => Some e' | None =>
        feval_check match feval_width l e1 with
        | None => filter (fun p => if v == fst p then false else true) l
        | Some w => ((v,VaN 0 w)::l)
        end e2
      end
  | Ite e1 e2 e3 =>
      match feval_check l e1 with Some e' => Some e' | None =>
        match feval_check l e2 with Some e' => Some e' | None =>
          match feval_check l e3 with Some e' => Some e' | None =>
            match feval_width l e2, feval_width l e3 with
            | Some w1, Some w2 => if w1 =? w2 then None else Some e
            | _,_ => Some e
            end
          end
        end
      end
  end.

Inductive fxc_context := FXC_Vars (l: list (var*value)) | FXC_Err (e:exp).

Fixpoint fexec_check (l:list (var*value)) q {struct q} :=
  match q with
  | Nop | Exn _ => FXC_Vars l
  | Move v e => match feval_check l e with Some e' => FXC_Err e' | None =>
                  match feval_width l e with None => FXC_Err e | Some w =>
                    FXC_Vars ((v,VaN 0 w)::l)
                  end
                end
  | Jmp e => match feval_check l e with Some e' => FXC_Err e' | None => FXC_Vars l end
  | Seq q1 q2 => match fexec_check l q1 with
                 | FXC_Err e => FXC_Err e
                 | FXC_Vars l2 => fexec_check l2 q2
                 end
  | If e q1 q2 =>
      match feval_check l e with Some e' => FXC_Err e' | None =>
        match fexec_check l q1 with FXC_Err e' => FXC_Err e' | FXC_Vars l1 =>
          match fexec_check l q2 with FXC_Err e' => FXC_Err e' | FXC_Vars l2 =>
            FXC_Vars (filter (fun v1 => existsb (fun v2 => if fst v1 == fst v2 then true else false) l2) l1)
          end
        end
      end
  | Rep e q1 =>
      match feval_check l e with Some e' => FXC_Err e' | None =>
        match fexec_check l q1 with FXC_Err e' => FXC_Err e' | FXC_Vars _ => FXC_Vars l end
      end
  end.

(* Functionally evaluate binary and unary operations using the opaque
   functions above. *)

Definition of_uvalue (u:uvalue) :=
  match u with VaU z m n w => if z then VaN n w else VaM m w end.

Definition utowidth (noe:forall op, noe_setop_typsig op) (w n:N) : uvalue :=
  VaU true (noe NOE_ZST) (noe NOE_MOD n (noe NOE_POW 2 w)) w.

Definition utobit (noe:forall op, noe_setop_typsig op) (b:bool) : uvalue :=
  VaU true (noe NOE_ZST) (if b then 1 else 0) 1.

Definition feval_binop (bop:binop_typ) (noe:forall op, noe_setop_typsig op) (w:bitwidth) (n1 n2:N) : uvalue :=
  match bop with
  | OP_PLUS => utowidth noe w (noe NOE_ADD n1 n2)
  | OP_MINUS => utowidth noe w (noe NOE_SUB (noe NOE_ADD (noe NOE_POW 2 w) n1) n2)
  | OP_TIMES => utowidth noe w (noe NOE_MUL n1 n2)
  | OP_DIVIDE => VaU true (noe NOE_ZST) (noe NOE_DIV n1 n2) w
  | OP_SDIVIDE => VaU true (noe NOE_ZST) (noe NOE_QUO w n1 n2) w
  | OP_MOD => VaU true (noe NOE_ZST) (noe NOE_MOD n1 n2) w
  | OP_SMOD => VaU true (noe NOE_ZST) (noe NOE_REM w n1 n2) w
  | OP_LSHIFT => utowidth noe w (noe NOE_SHL n1 n2)
  | OP_RSHIFT => VaU true (noe NOE_ZST) (noe NOE_SHR n1 n2) w
  | OP_ARSHIFT => VaU true (noe NOE_ZST) (noe NOE_ASR w n1 n2) w
  | OP_AND => VaU true (noe NOE_ZST) (noe NOE_AND n1 n2) w
  | OP_OR => VaU true (noe NOE_ZST) (noe NOE_OR n1 n2) w
  | OP_XOR => VaU true (noe NOE_ZST) (noe NOE_XOR n1 n2) w
  | OP_EQ => utobit noe (noe NOE_EQB n1 n2)
  | OP_NEQ => utobit noe (noe NOE_NEG (noe NOE_EQB n1 n2))
  | OP_LT => utobit noe (noe NOE_LTB n1 n2)
  | OP_LE => utobit noe (noe NOE_LEB n1 n2)
  | OP_SLT => utobit noe (noe NOE_SLT w n1 n2)
  | OP_SLE => utobit noe (noe NOE_SLE w n1 n2)
  end.

Definition feval_unop (uop:unop_typ) (noe:forall op, noe_setop_typsig op) (n:N) (w:bitwidth) : uvalue :=
  match uop with
  | OP_NEG => utowidth noe w (noe NOE_SUB (noe NOE_POW 2 w) n)
  | OP_NOT => VaU true (noe NOE_ZST) (noe NOE_NOT n w) w
  end.

Definition feval_cast (c:cast_typ) (noe:forall op, noe_setop_typsig op) (w w':bitwidth) (n:N) : N :=
  match c with
  | CAST_UNSIGNED => n
  | CAST_SIGNED => noe NOE_CAS w w' n
  | CAST_HIGH => noe NOE_SHR n (noe NOE_SUB w w')
  | CAST_LOW => noe NOE_MOD n (noe NOE_POW 2 w')
  end.

(* Convert a list of variables and their values to a store function. *)
Fixpoint updlst s (l: list (var * value)) upd : store :=
  match l with nil => s | (v,u)::t => upd (updlst s t upd) v u end.

(* Remove a variable from a list of variables and their values. *)
Fixpoint remlst v (l: list (var * value)) : list (var * value) :=
  match l with nil => nil | (v',u)::t => if v == v' then t else (v',u)::(remlst v t) end.

(* Functionally evaluate an expression.  Parameter unk is an oracle function
   that returns values of unknown expressions. *)
Definition feval_exp (noe:forall op, noe_setop_typsig op) (noet:forall op, noe_typop_typsig op) h s :=
  fix feval_exp' e unk l {struct e} := match e with
  | Var v => let u := updlst s l vupdate v in
             (match feval_width l e with
              | None => VaU (noe NOE_TYP u) (noe NOE_MEM u) (noe NOE_NUM u) (noe NOE_WID u)
              | Some _ => VaU (vtyp u) (vmem u) (vnum u) (vwidth u)
              end, nil)
  | Word n w => (VaU true (noe NOE_ZST) n w, nil)
  | Load e1 e2 en len =>
      match feval_exp' e1 (unknowns0 unk) l, feval_exp' e2 (unknowns1 unk) l with
      | (VaU _ m _ _, ma1), (VaU _ _ n _, ma2) =>
        (VaU true (noe NOE_ZST) (noe NOE_GET en len m n) (Mb*len),
         noet NOE_MAR h (updlst s l (noet NOE_UPD)) n len :: ma1++ma2)
      end
  | Store e1 e2 e3 en len =>
      match feval_exp' e1 (unknowns00 unk) l, feval_exp' e2 (unknowns01 unk) l, feval_exp' e3 (unknowns10 unk) l with
      | (VaU _ m _ mw, ma1), (VaU _ _ a _, ma2), (VaU _ _ v _, ma3) =>
        (VaU false (noe NOE_SET en len m a v) 0 mw,
         noet NOE_MAW h (updlst s l (noet NOE_UPD)) a len :: ma1++ma2++ma3)
      end
  | BinOp bop e1 e2 =>
      match feval_exp' e1 (unknowns0 unk) l, feval_exp' e2 (unknowns1 unk) l with
      | (VaU _ _ n1 w, ma1), (VaU _ _ n2 _, ma2) => (feval_binop bop noe w n1 n2, ma1++ma2)
      end
  | UnOp uop e1 =>
      match feval_exp' e1 unk l with (VaU _ _ n w, ma) =>
        (feval_unop uop noe n w, ma)
      end
  | Cast c w' e1 =>
      match feval_exp' e1 unk l with (VaU _ _ n w, ma) =>
        (VaU true (noe NOE_ZST) (feval_cast c noe w w' n) w', ma)
      end
  | Let v e1 e2 =>
      match feval_exp' e1 (unknowns0 unk) l with (u,ma1) =>
        match feval_exp' e2 (unknowns1 unk) ((v,of_uvalue u)::remlst v l) with
        | (u',ma2) => (u', ma1++ma2)
        end
      end
  | Unknown w => (VaU true (noe NOE_ZST) (noe NOE_MOD (unk xH) (noe NOE_POW 2 w)) w, nil)
  | Ite e1 e2 e3 =>
      match feval_exp' e1 (unknowns0 unk) l, feval_exp' e2 (unknowns1 unk) l, feval_exp' e3 (unknowns1 unk) l with
      | (VaU _ _ n1 _, ma1), (VaU b2 m2 n2 w2, ma2), (VaU b3 m3 n3 w3, ma3) =>
        (match feval_width l e with
         | Some w => VaU (if Bool.eqb b2 b3 then b2 else if n1 then b3 else b2)
                         (if n1 then m3 else m2) (if n1 then n3 else n2) w
         | None => VaU (if n1 then b3 else b2) (if n1 then m3 else m2)
                       (if n1 then n3 else n2) (if n1 then w3 else w2)
         end,
         match ma2,ma3 with nil,nil => ma1 | _,_ => ma1++(if n1 then conjall ma3 else conjall ma2)::nil end)
      end
  | Extract n1 n2 e1 =>
      match feval_exp' e1 unk l with
      | (VaU _ _ n w, ma) => (VaU true (noe NOE_ZST)
          (noe NOE_MOD (noe NOE_SHR n n2) (noe NOE_POW 2 (N.succ n1 - n2))) (N.succ n1 - n2), ma)
      end
  | Concat e1 e2 =>
      match feval_exp' e1 (unknowns0 unk) l, feval_exp' e2 (unknowns1 unk) l with
      | (VaU _ _ n1 w1, ma1), (VaU _ _ n2 w2, ma2) =>
        (VaU true (noe NOE_ZST) (noe NOE_OR (noe NOE_SHL n1 w2) n2)
        match feval_width l e with None => noe NOE_ADD w1 w2 | Some w => w end, ma1++ma2)
      end
  end.


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

Definition fexec_stmt (noe:forall op, noe_setop_typsig op) (noet:forall op, noe_typop_typsig op) h :=
  fix fexec_stmt' q s unk l := match q with
  | Nop => FIS l (FIExit None) nil
  | Move v e => match feval_exp noe noet h s e unk l with
                | (u,ma) => FIS ((v, of_uvalue u)::remlst v l) (FIExit None) ma
                end
  | Jmp e => match feval_exp noe noet h s e unk l with
             | (VaU _ _ n _, ma) => FIS l (FIExit (Some (Exit n))) ma
             end
  | Exn i => FIS l (FIExit (Some (Raise i))) nil
  | Seq q1 q2 =>
      match fexec_stmt' q1 s (unknowns0 unk) l with
      | FIS l1 (FIStmt q1') ma1 => FIS l1 (FIStmt (Seq q1' q2)) ma1
      | FIS l1 (FIExit (Some x1)) ma1 => FIS l1 (FIExit (Some x1)) ma1
      | FIS l1 (FIExit None) ma1 => match fexec_stmt' q2 s (unknowns1 unk) l1 with
                                    | FIS l2 qx2 ma2 => FIS l2 qx2 (ma1++ma2)
                                    end
      end
  | If e q1 q2 =>
      match feval_exp noe noet h s e unk l with (VaU _ _ n _, ma0) =>
        FIS l (FIStmt (if n then q2 else q1)) ma0
      end
  | Rep e q1 =>
      match feval_exp noe noet h s e unk l with (VaU _ _ n _, ma0) =>
        FIS l (FIStmt (noet NOE_ITR n stmt (Seq q1) Nop)) ma0
      end
  end.

Definition list_union {A} (eqb: A -> A -> bool) (l1 l2: list A) :=
  List.fold_left (fun l x => if existsb (eqb x) l2 then l else (x::l)) l1 l2.

Fixpoint vars_read_by_exp e :=
  match e with 
  | Var v => v::nil
  | Word _ _ | Unknown _ => nil
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => vars_read_by_exp e1
  | Load e1 e2 _ _ | BinOp _ e1 e2 | Concat e1 e2 => list_union vareqb (vars_read_by_exp e1) (vars_read_by_exp e2)
  | Store e1 e2 e3 _ _ | Ite e1 e2 e3 => list_union vareqb (list_union vareqb (vars_read_by_exp e1) (vars_read_by_exp e2)) (vars_read_by_exp e3)
  | Let v e1 e2 => list_union vareqb (vars_read_by_exp e1) (List.remove vareq v (vars_read_by_exp e2))
  end.

Fixpoint noassignb q v :=
  match q with
  | Nop | Jmp _ | Exn _ => true
  | Move v0 _ => if vareq v0 v then false else true
  | Seq q1 q2 | If _ q1 q2 => andb (noassignb q1 v) (noassignb q2 v)
  | Rep _ q1 => noassignb q1 v
  end.

Fixpoint vars_read_by_stmt q :=
  match q with
  | Nop | Exn _ => nil
  | Move _ e | Jmp e => vars_read_by_exp e
  | Seq q1 q2 => list_union vareqb (vars_read_by_stmt q1) (List.filter (noassignb q1) (vars_read_by_stmt q2))
  | If e q1 q2 => list_union vareqb (vars_read_by_exp e) (list_union vareqb (vars_read_by_stmt q1) (vars_read_by_stmt q2))
  | Rep e q1 => list_union vareqb (vars_read_by_exp e) (vars_read_by_stmt q1)
  end.

Definition other_vars_read (l: list (var * value)) q :=
  let old := List.map fst l in
  List.filter (fun v => negb (existsb (vareqb v) old)) (vars_read_by_stmt q).

End PICINAE_FINTERP_DEFS.



Module Type PICINAE_FINTERP (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL).

Import IL.
Import TIL.
Include PICINAE_FINTERP_DEFS IL TIL.
Module PTheory := PicinaeTheory IL.
Import PTheory.

(* Using the functional interpreter, we now define a set of tactics that reduce
   expressions to values, and statements to stores & exits.  These tactics are
   carefully implemented to avoid simplifying anything other than the machinery
   of the functional interpreter, so that Coq does not spin out of control
   attempting to execute the entire program.  Our objective is to infer a
   reasonably small, well-formed symbolic expression that captures the result
   of executing each assembly instruction.  This result can be further reduced
   by the user (e.g., using "psimpl") if desired. *)

(* Statement simplification most often gets stuck at variable-reads, since the
   full content of the store is generally not known (s is a symbolic expression).
   We can often push past this obstacle by applying the update_updated and
   update_frame theorems to automatically infer that the values of variables not
   being read are irrelevant.  The "simpl_stores" tactic does so. *)

Parameter if_N_same: forall A (n:N) (a:A), (if n then a else a) = a.

Ltac simpl_stores :=
  repeat first [ rewrite update_updated | rewrite update_frame; [|discriminate 1] ];
  repeat rewrite if_N_same;
  repeat match goal with |- context [ update ?S ?V ?U ] =>
    match S with context c [ update ?T V _ ] => let r := context c[T] in
      replace (update S V U) with (update r V U) by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.

Ltac simpl_stores_in H :=
  repeat lazymatch type of H with context [ update _ ?v _ ?v ] => rewrite update_updated in H
                                | context [ update _ _ _ _ ] => rewrite update_frame in H; [|discriminate 1] end;
  repeat rewrite if_N_same in H;
  repeat match type of H with context [ update ?S ?V ?U ] =>
    match S with context c [ update ?T V _ ] => let r := context c[T] in
      replace (update S V U) with (update r V U) in H by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.

Tactic Notation "simpl_stores" "in" hyp(H) := simpl_stores_in H.

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

Parameter models_val:
  forall v s t (TV: hastyp_val (s v) t),
  match t with
  | NumT w => exists n, s = s [v := VaN n w]
  | MemT w => exists m, s = s [v := VaM m w]
  end.

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

Ltac stock_store_in XS :=
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

Tactic Notation "stock_store" "in" hyp(XS) := stock_store_in XS.

(* To prevent vm_compute from expanding symbolic expressions that the user
   already has in a desired form, the following lemmas introduce symbolic
   constants for those expressions and sets them equal to the original terms.
   The "destruct" tactic can then be used to separate those terms out into
   a different hypothesis to which vm_compute is not applied, and then use
   "subst" to substitute them back into the evaluated term after vm_compute
   is done. *)

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

Parameter fexec_stmt_init:
  forall {EQT} (eq1 eq2:EQT) h s q s' x (XS: exec_stmt h s q s' x),
  eq1=eq2 -> exec_stmt h (updlst s (rev nil) vupdate) q s' x /\ (eq1=eq2).

Parameter fexec_stmt_fin:
  forall a_h a_s a_s' a_x h s l q s' x, 
  exec_stmt h (updlst s l vupdate) q s' x /\ (a_h,a_s,a_s',a_x)=(h,s,s',x) ->
  exec_stmt a_h (updlst a_s l vupdate) q a_s' a_x.

Parameter fexec_stmt_updn:
  forall {EQT} a (eq1 eq2:EQT) h s v n w l q s' x,
  exec_stmt h (updlst (vupdate s v (VaN n w)) (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,n) ->
  exec_stmt h (updlst s (rev ((v, VaN a w)::l)) vupdate) q s' x /\ eq1=eq2.

Parameter fexec_stmt_updm:
  forall {EQT} a (eq1 eq2:EQT) h s v m w l q s' x,
  exec_stmt h (updlst (vupdate s v (VaM m w)) (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,m) ->
  exec_stmt h (updlst s (rev ((v, VaM a w)::l)) vupdate) q s' x /\ eq1=eq2.

Parameter fexec_stmt_updu:
  forall {EQT} a (eq1 eq2:EQT) h s v u l q s' x,
  exec_stmt h (updlst (vupdate s v u) (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,u) ->
  exec_stmt h (updlst s (rev ((v,u)::l)) vupdate) q s' x /\ eq1=eq2.

Parameter fexec_stmt_hypn:
  forall {EQT} a (eq1 eq2:EQT) h s v n w l q s' x (SV: s v = VaN n w),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,n) ->
  exec_stmt h (updlst s (rev ((v, VaN a w)::l)) vupdate) q s' x /\ eq1=eq2.

Parameter fexec_stmt_hypm:
  forall {EQT} a (eq1 eq2:EQT) h s v m w l q s' x (SV: s v = VaM m w),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,m) ->
  exec_stmt h (updlst s (rev ((v, VaM a w)::l)) vupdate) q s' x /\ eq1=eq2.

Parameter fexec_stmt_hypu:
  forall {EQT} a (eq1 eq2:EQT) h s v u l q s' x (SV: s v = u),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,u) ->
  exec_stmt h (updlst s (rev ((v,u)::l)) vupdate) q s' x /\ eq1=eq2.

Parameter fexec_stmt_typ:
  forall h c s v t l q s' x EQs (MDL: models c s) (CV: c v = Some t),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ EQs ->
  match t with NumT w => exists a, s v = VaN a w /\ exec_stmt h (updlst s (rev ((v, VaN a w)::l)) vupdate) q s' x /\ EQs
             | MemT w => exists a, s v = VaM a w /\ exec_stmt h (updlst s (rev ((v, VaM a w)::l)) vupdate) q s' x /\ EQs
  end.

Ltac tacmap T l :=
  match l with nil => idtac | ?h::?t => T h; tacmap T t end.

Ltac populate_varlist XS :=
  eapply fexec_stmt_init in XS; [
  repeat lazymatch type of XS with
  | exec_stmt _ (updlst (update _ _ (VaN _ _)) (rev _) vupdate) _ _ _ /\ _ =>
      eapply fexec_stmt_updn in XS
  | exec_stmt _ (updlst (update _ _ (VaM _ _)) (rev _) vupdate) _ _ _ /\ _ =>
      eapply fexec_stmt_updm in XS
  | exec_stmt _ (updlst (update _ _ _) (rev _) vupdate) _ _ _ /\ _ =>
      eapply fexec_stmt_updu in XS
  end;
  lazymatch type of XS with exec_stmt ?h (updlst ?s (rev ?l) vupdate) ?q ?s' ?x /\ _ =>
    let vs := (eval compute in (other_vars_read l q)) in
    tacmap ltac:(fun v =>
      try match goal with
      | [ SV: s v = VaN ?n ?w |- _ ] =>
          eapply (fexec_stmt_hypn _ _ _ h s v n w _ q s' x SV) in XS
      | [ SV: s v = VaM ?m ?w |- _ ] =>
          eapply (fexec_stmt_hypm _ _ _ h s v m w _ q s' x SV) in XS
      | [ MDL: models ?c s |- _ ] =>
          lazymatch eval hnf in (c v) with Some ?t =>
            apply (fexec_stmt_typ h c s v t _ q s' x _ MDL (eq_refl _)) in XS;
            let _a := match t with NumT _ => fresh "n" | MemT _ => fresh "m" end in
            let H := fresh "Hsv" in
              destruct XS as [_a [H XS]]
          end
      end) vs
  end;
  eapply fexec_stmt_fin in XS |].

(* The main theorem proves that the functional interpreter obeys the operational
   semantics.  Tactics apply this to convert eval_exp and exec_stmt propositions
   to feval_exp and fexec_stmt functions that can be evaluated using vm_compute
   or other reduction tactics. *)

Parameter reduce_stmt:
  forall noe noet s l q h s' x (XS: exec_stmt h (updlst s l vupdate) q s' x)
         (NOE: noe = noe_setop) (NOET: noet = noe_typop),
  exists unk, match fexec_stmt noe noet h q s unk l with
              | FIS l' (FIExit x') ma => (s' = updlst s l' (noet NOE_UPD) /\ x = x') /\ conjallT ma
              | FIS l' (FIStmt q') ma => exec_stmt h (updlst s l' (noet NOE_UPD)) q' s' x /\ conjallT ma
              end.

(* Check a statement for typeability before interpreting it, since statements that
   cannot be statically typed can potentially blow up into huge terms. *)

Ltac step_precheck XS :=
  lazymatch type of XS with exec_stmt _ (updlst _ ?l _) ?q _ _ =>
    lazymatch (eval compute in (fexec_check l q)) with
    | FXC_Err ?e => fail 1 "Untyped subexpression:" e
    | FXC_Vars _ => idtac
    end
  | _ => idtac
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
    [ step_precheck XS;
      eapply reduce_stmt in XS;
      [ let unk := fresh "unknown" in (
          destruct XS as [unk XS];
          compute in XS;
          repeat match type of XS with context [ unk ?i ] =>
            let u := fresh "u" in set (u:=unk i) in XS; clearbody u
          end;
          try clear unk
        )
      | reflexivity | reflexivity ];
      cbv beta match delta [ noe_setop noe_typop ] in XS
    | reflexivity ]
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

(* Similar as above, except this is for evaluating deterministic expressions *)
Definition other_vars_read_exp (l: list (var * value)) e :=
  let old := List.map fst l in
  List.filter (fun v => negb (existsb (vareqb v) old)) (vars_read_by_exp e).

Parameter fstore_init: forall s EQT (eq1 eq2: EQT),
  eq1 = eq2 ->
  (s = (updlst s (rev nil) update)) /\ eq1 = eq2.

Parameter fstore_updu: forall {EQT} (eq1 eq2: EQT) s0 s v u l,
  (s0 = updlst (update s v u) (rev l) update /\ eq1 = eq2) ->
  (s0 = updlst s (rev ((v, u)::l)) update /\ eq1 = eq2).

Parameter fstore_updn: forall {EQT} (eq1 eq2: EQT) s0 s v a w n l,
  (s0 = updlst (update s v (VaN n w)) (rev l) update /\ (eq1, a) = (eq2, n)) ->
  (s0 = updlst s (rev ((v, (VaN a w))::l)) update /\ eq1 = eq2).

Parameter fstore_updm: forall {EQT} (eq1 eq2: EQT) s0 s v a w m l,
  (s0 = updlst (update s v (VaM m w)) (rev l) update /\ (eq1, a) = (eq2, m)) ->
  (s0 = updlst s (rev ((v, (VaM a w))::l)) update /\ eq1 = eq2).

Parameter fstore_hypn: forall {EQT} {eq1 eq2: EQT} {s0 a s v n w l}
  (SV: s v = VaN n w),
  (s0 = updlst s (rev l) update /\ (eq1, a) = (eq2, n)) ->
  (s0 = updlst s (rev ((v, (VaN a w))::l)) update /\ eq1 = eq2).

Parameter fstore_hypm: forall {EQT} {eq1 eq2: EQT} {s0 a s v m w l}
  (SV: s v = VaM m w),
  (s0 = updlst s (rev l) update /\ (eq1, a) = (eq2, m)) ->
  (s0 = updlst s (rev ((v, (VaM a w))::l)) update /\ eq1 = eq2).

Parameter fstore_hypu: forall EQs s0 s v u l (SV: s v = u),
  (s0 = updlst s (rev l) update /\ EQs) <->
  (s0 = updlst s (rev ((v, u)::l)) update /\ EQs).

Parameter fstore_typ: forall {c s0 s t l EQs} v (MDL: models c s) (CV: c v = Some t),
  (s0 = updlst s (rev l) update /\ EQs) ->
  match t with
  | NumT w => exists a, s v = VaN a w /\ s0 =
      updlst s (rev ((v, VaN a w) :: l)) update /\ EQs
  | MemT w => exists a, s v = VaM a w /\ s0 =
      updlst s (rev ((v, VaM a w) :: l)) update /\ EQs
  end.

Parameter fstore_fin: forall (h: hdomain) a_c a_h a_s0 a_s e c s0 s l t
  (MDL: models c s0) (TE: hastyp_exp c e t),
  (s0 = updlst s l update /\ (a_c, a_h, a_s0, a_s) = (c, h, s0, s)) ->
  (a_h, a_s0) = (a_h, updlst a_s l update) /\
    models a_c (updlst a_s l update) /\ hastyp_exp a_c e t.

Parameter do_eval_exp:
  forall h s e c t l noet noe u' ma (NU: forall_exps_in_exp not_unknown e)
    (MDL: models c (updlst s l vupdate)) (TE: hastyp_exp c e t)
    (FE: (feval_exp noe noet h s e (fun _ => 0) l) = (u', ma))
    (CONJ: conjallT ma), (noet = noe_typop) -> (noe = noe_setop) ->
    eval_exp h (updlst s l update) e (of_uvalue u').

Ltac exp2_populate_varlist h s0 e ST MDL :=
  let _ := eval hnf in (@eq_refl store s0) in idtac;
  let _ := eval hnf in (@eq_refl exp e) in idtac;
  einstantiate (fstore_init s0) as ST; try unfold s0 in ST;
  [ | repeat match type of ST with
           | _ = updlst (update _ _ (VaN _ _)) (rev _) update /\ _ =>
               eapply fstore_updn in ST
           | _ = updlst (update _ _ (VaM _ _)) (rev _) update /\ _ =>
               eapply fstore_updm in ST
           | _ = updlst (update _ _ _) (rev _) update /\ _ =>
               eapply fstore_updu in ST
           end;
    lazymatch type of ST with
    | _ = updlst ?s (rev ?l) update /\ _ =>
        let vs := eval compute in (other_vars_read_exp l e) in
        tacmap ltac:(fun v =>
          try match goal with
          | [ SV: s v = VaN _ _ |- _ ] =>
              eapply (fstore_hypn SV) in ST
          | [ SV: s v = VaM _ _ |- _ ] =>
              eapply (fstore_hypm SV) in ST
          | [ MDL: models ?c s |- _ ] =>
              lazymatch eval hnf in (c v) with Some ?t =>
                  eapply (fstore_typ v MDL (eq_refl _)) in ST;
                  let _a := match t with NumT _ => fresh "n" | MemT _ => fresh "m" end in
                  let SV := fresh "Hsv" in
                  destruct ST as [_a [SV ST] ]
              end
          end) vs
    end;
    match type of MDL with models ?c _ =>
    match eval compute in (typchk_exp e c) with
    | None => fail "Cannot type check " e
    | Some ?te =>
        let TE := fresh "TE" in
        pose proof (TE := typchk_exp_sound e c te eq_refl);
        eapply (fstore_fin h) in ST; [|exact MDL|exact TE];
        clear TE
    end
    end].

Ltac exp2_eval_precheck e ST :=
  lazymatch type of ST with _ = updlst _ ?l _ =>
    lazymatch (eval compute in (feval_check l e)) with
    | Some ?e => fail 1 "Untyped subexpression:" e
    | None => idtac
    end
  end.

Ltac mk_eval_exp h s e EE :=
  let ST := fresh "ST" in
  lazymatch eval compute in (IL.forallb_exps_in_exp not_unknownb e) with
  | true => idtac
  | false => fail "Cannot deterministically evaluate expression because it has some unknowns!"
  end;
  lazymatch goal with
  | MDL: models ?c s |- _ =>
      exp2_populate_varlist h s e ST MDL; [ |
      match type of ST with (?h', _) = (_, updlst ?s' ?l _) /\ models ?c' _ /\ _ =>
          let MDL' := fresh "MDL'" in
          let TE' := fresh "TE'" in
          destruct ST as [ST [MDL' TE'] ]; apply pair_equal_spec in ST;
          destruct ST as [_ ST]; exp2_eval_precheck e ST;
          einstantiate (do_eval_exp h' s' e c') as EE;
          (* No unknowns because we computationally decided that it has
             no unknowns *)
          [ apply (forall_exps_iff_forallb_exps not_unknown not_unknown_dec);
            reflexivity
          (* Type-checked store and expression  *)
          | exact MDL' | exact TE'
          (* Here we compute the value of feval_exp with currently all the
           * existential variables masking over any stuff we do not want
           * expanded. NOTE: do NOT use vm_compute here, as this will cause a
           * long lag on the magnitude of hours to complete Qed. *)
          | compute
          (* Finally fill out the existential variables for the operations *)
          | | reflexivity | reflexivity | ];
          (* feval_exp evaluates *)
          [ reflexivity | | ];
          (* Expand to the operators that we masked out only *)
          cbv beta match delta [ noe_setop noe_typop of_uvalue ] in *
      end ]; [reflexivity| |]; repeat rewrite <- ST in *; clear ST
  | _ =>
      let m := uconstr:(models ?c s) in
      fail "Must have hypothesis of the form " m
  end.

End PICINAE_FINTERP.



Module PicinaeFInterp (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL) : PICINAE_FINTERP IL TIL.

Import IL.
Import TIL.
Module PTheory := PicinaeTheory IL.
Import PTheory.
Include PICINAE_FINTERP_DEFS IL TIL.

Lemma updlst_remlst:
  forall v u l s, updlst s (remlst v l) vupdate [v:=u] = updlst s l vupdate [v:=u].
Proof.
  induction l; intros.
    reflexivity.
    destruct a as (v1,u1). simpl. destruct (v == v1).
      subst. unfold vupdate at 2. rewrite update_cancel. reflexivity.
      simpl. unfold vupdate at 1 3. rewrite update_swap.
        rewrite IHl. rewrite update_swap by assumption. reflexivity.
        intro H. apply n. symmetry. exact H.
Qed.

Lemma find_remlst:
  forall f v (H: forall '(v', u), v = v' -> f (v, u) = false) l,
  find f (remlst v l) = find f l.
Proof.
  induction l; intros.
    reflexivity.
    simpl. specialize (H a). destruct a as [v' u']. destruct (v == v').
      subst. rewrite H by reflexivity. reflexivity.
      simpl. rewrite <- IHl. reflexivity.
Qed.

Lemma find_filter:
  forall {A} f g (H: forall x:A, g x = false -> f x = false) l,
  find f (filter g l) = find f l.
Proof.
  induction l; intros.
    reflexivity.
    simpl. specialize (H a). destruct (g a).
      rewrite <- IHl. reflexivity.
      rewrite H by reflexivity. apply IHl.
Qed.

Lemma find_filter_none:
  forall {A} f g (H: forall x:A, f x = true -> g x = false) l,
  find f (filter g l) = None.
Proof.
  induction l; intros.
    reflexivity.
    simpl. specialize (H a). destruct (g a).
      simpl. destruct (f a). discriminate H. reflexivity. apply IHl.
      apply IHl.
Qed.

Theorem feval_width_mono:
  forall l1 l2 (SS: feval_varwidth l1 ⊆ feval_varwidth l2), feval_width l1 ⊆ feval_width l2.
Proof.
  intros. intros e w H. revert l1 l2 w SS H. induction e; intros; try assumption.

  (* Var *)
  apply SS. assumption.

  (* Store *)
  eapply IHe1; eassumption.

  (* BinOp *)
  destruct b; solve [ assumption | eapply IHe1; eassumption ].

  (* UnOp *)
  destruct u; eapply IHe; eassumption.

  (* Let *)
  simpl in *. destruct (feval_width l1 e1) as [w1|] eqn:FEW1.
    erewrite IHe1; [eapply IHe2|..]; [|eassumption..]. simpl. intros v0 w0 H0. destruct (v0 == v).
      subst v0. exact H0.
      apply SS. exact H0.
    eapply IHe2; [|exact H]. clear - SS. destruct (feval_width l2 e1) as [w2|].
      intros v0 w0 H0. destruct (v0 == v).
        subst v0. unfold feval_varwidth in H0. destruct find eqn:F in H0.
          apply find_some in F. destruct F as [IN F]. apply filter_In, proj2 in IN. destruct (v == fst p); discriminate.
          discriminate H0.
        simpl. vantisym v0 v; [|assumption]. apply SS. unfold feval_varwidth in H0. destruct find eqn:F in H0.
          unfold feval_varwidth. replace (find _ l1) with (Some p).
            exact H0.
            rewrite <- F. clear - n. apply find_filter. intros p H. destruct p as (v1,u1). simpl in *. destruct (v == v1).
              subst v1. vantisym v0 v. reflexivity. assumption.
              discriminate H.
          discriminate H0.
      intros v0 w0 H0. unfold feval_varwidth in *. destruct (v == v0).
        subst v0. simpl in H0. rewrite find_filter_none in H0.
          discriminate H0.
          intros p H1. destruct (v == fst p). reflexivity. discriminate H1.
        rewrite !find_filter in * by
          ( intros p H1; destruct p as (v1,u1); simpl in *; destruct (v == v1);
            [ subst v1; vantisym v0 v; [ reflexivity | apply not_eq_sym, n ]
            | discriminate H1 ]).
          apply SS. exact H0.

  (* Ite *)
  simpl in *.
  destruct (feval_width l1 e2) as [w2|] eqn:FEW2; [|discriminate]. erewrite IHe2 by eassumption.
  destruct (feval_width l1 e3) as [w3|] eqn:FEW3; [|discriminate]. erewrite IHe3 by eassumption.
  assumption.

  (* Concat *)
  simpl in *.
  destruct (feval_width l1 e1) as [w1|] eqn:FEW1; [|discriminate]. erewrite IHe1 by eassumption.
  destruct (feval_width l1 e2) as [w2|] eqn:FEW2; [|discriminate]. erewrite IHe2 by eassumption.
  assumption.
Qed.

Corollary feval_width_eq:
  forall l1 l2 (EQ: feval_varwidth l1 = feval_varwidth l2), feval_width l1 = feval_width l2.
Proof.
  intros. apply pfsub_antisym; apply feval_width_mono; rewrite EQ; reflexivity.
Qed.

Theorem feval_width_sound:
  forall h s e l w u
    (FW: feval_width l e = Some w)
    (E: eval_exp h (updlst s l vupdate) e u),
  w = vwidth u.
Proof.
  induction e; intros; inversion E; subst;
  try solve [ inversion FW; reflexivity ].

  (* Var *)
  simpl in FW. unfold feval_varwidth in FW. destruct find eqn:F in FW; [|discriminate].
  inversion FW. destruct p as (v',u). simpl.
  replace v' with v in F.
    clear FW E H0 h w v'. revert F. induction l; intros.
      discriminate F.
      destruct a as (v0,u0). simpl. unfold vupdate. destruct (v == v0).
        subst v0. simpl in F. vreflexivity v. inversion F.
          rewrite update_updated. reflexivity.
        simpl in F. vantisym v v0; [|assumption].
          rewrite update_frame by assumption. apply IHl. assumption.
    destruct (v == v').
      assumption.
      apply find_some, proj2 in F. simpl in F. vantisym v v'. discriminate. assumption.

  (* Store *)
  change (vwidth _) with (vwidth (VaM m mw)). eapply IHe1; eassumption.

  (* BinOp *)
  destruct b; solve
  [ change (vwidth _) with (vwidth (VaN n1 w0)); eapply IHe1; eassumption
  | inversion FW; reflexivity ].

  (* UnOp *)
  destruct u;
  change (vwidth _) with (vwidth (VaN n1 w1)); eapply IHe; eassumption.

  (* Let *)
  apply IHe2 with (l := (v,u1)::l); [|exact E2].
  simpl in FW. destruct (feval_width l e1) eqn:FW1 in FW.
    erewrite feval_width_eq. exact FW. extensionality v0. simpl. destruct (v0 == v).
      simpl. erewrite <- IHe1. reflexivity. exact FW1. exact E1.
      reflexivity.
    eapply feval_width_mono; [|exact FW]. unfold feval_varwidth. intros v0 w0 H0. simpl. destruct (v0 == v).
      subst v0. rewrite find_filter_none in H0.
        discriminate H0.
        intro p. destruct (v == fst p). reflexivity. discriminate 1.
      rewrite find_filter in H0. assumption. intros (v2,u2) H. unfold fst in *. destruct (v0 == v2).
        subst v0. vantisym v v2. discriminate H. apply not_eq_sym, n.
        reflexivity.

  (* Ife *)
  simpl in FW.
  destruct (feval_width l e2) eqn:FW2 in FW; [|discriminate].
  destruct (feval_width l e3) eqn:FW3 in FW; [|discriminate].
  destruct (b =? b0) eqn:W; [|discriminate].
  apply N.eqb_eq in W. subst b0. inversion FW. subst b.
  destruct n1.
    eapply IHe3; eassumption.
    eapply IHe2; eassumption.

  (* Concat *)
  simpl in FW.
  destruct (feval_width l e1) eqn:FW1 in FW; [|discriminate].
  destruct (feval_width l e2) eqn:FW2 in FW; [|discriminate].
  inversion FW. apply f_equal2.
    change w1 with (vwidth (VaN n1 w1)). eapply IHe1; eassumption.
    change w2 with (vwidth (VaN n2 w2)). eapply IHe2; eassumption.
Qed.

Theorem feval_check_imp_width:
  forall e l (CHK: feval_check l e = None), feval_width l e <> None.
Proof.
  induction e; intros l CHK FEW; simpl in CHK; simpl in FEW; try discriminate.
    rewrite FEW in CHK. discriminate.
    specialize (IHe1 l). destruct (feval_check l e1).
      discriminate.
      apply IHe1. reflexivity. exact FEW.
    specialize (IHe1 l). destruct (feval_check l e1).
      discriminate.
      apply IHe1. reflexivity. destruct b; solve [ exact FEW | discriminate FEW ].
    eapply IHe; eassumption.
    specialize (IHe1 l). destruct (feval_check l e1).
      discriminate.
      destruct (feval_width l e1).
        eapply IHe2; eassumption.
        apply IHe1; reflexivity.

    specialize (IHe1 l). destruct (feval_check l e1). discriminate.
    specialize (IHe2 l). destruct (feval_check l e2). discriminate.
    destruct (feval_width l e2); [| apply IHe2; reflexivity ].
    specialize (IHe3 l). destruct (feval_check l e3). discriminate.
    destruct (feval_width l e3); [| apply IHe3; reflexivity ].
    destruct (_ =? _); discriminate.

    specialize (IHe1 l). destruct (feval_check l e1). discriminate.
    destruct (feval_width l e1); [| apply IHe1; reflexivity ].
    specialize (IHe2 l). destruct (feval_check l e2). discriminate.
    destruct (feval_width l e2).
      discriminate.
      apply IHe2; reflexivity.
Qed.

Theorem reduce_exp:
  forall noe noet h s e u l (E: eval_exp h (updlst s l vupdate) e u)
         (NOE: noe = noe_setop) (NOET: noet = noe_typop),
  exists unk, match feval_exp noe noet h s e unk l with (u',ma) =>
    u = of_uvalue u' /\ conjallT ma end.
Proof.
  intros. subst noe noet. revert u l E.
  induction e; intros; inversion E; rename E into E0; subst.

  (* Var *)
  exists (fun _ => N0). split.
    destruct feval_width; simpl; destruct (updlst s l vupdate v); reflexivity.
    exact I.

  (* Word *)
  exists (fun _ => N0). split.
    reflexivity.
    exact I.

  (* Load *)
  apply IHe1 in E1. apply IHe2 in E2. clear IHe1 IHe2.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2].
  exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
  simpl. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
  destruct (feval_exp _ _ _ _ e1 _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  destruct (feval_exp _ _ _ _ e2 _ _) as (u2,ma2). destruct u2. destruct E2 as [U2 M2].
  simpl in U1,U2. destruct z; destruct z0; try discriminate. injection U1; injection U2; intros; subst.
  split.
    reflexivity.
    split.
      exact R.
      apply conjallT_app; assumption.

  (* Store *)
  apply IHe1 in E1. apply IHe2 in E2. apply IHe3 in E3. clear IHe1 IHe2 IHe3.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2]. destruct E3 as [unk3 E3].
  exists (fun i => match i with xO (xO j) => unk1 j | xI (xO j) => unk2 j | xO (xI j) => unk3 j | _ => N0 end).
  simpl. change (unknowns00 _) with unk1. change (unknowns01 _) with unk2. change (unknowns10 _) with unk3.
  destruct (feval_exp _ _ _ _ e1 _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  destruct (feval_exp _ _ _ _ e2 _ _) as (u2,ma2). destruct u2. destruct E2 as [U2 M2].
  destruct (feval_exp _ _ _ _ e3 _ _) as (u3,ma3). destruct u3. destruct E3 as [U3 M3].
  simpl in U1,U2,U3. destruct z; destruct z0; destruct z1; try discriminate. injection U1; injection U2; injection U3; intros; subst.
  split.
    reflexivity.
    split.
      exact W.
      repeat try apply conjallT_app; assumption.

  (* BinOp *)
  apply IHe1 in E1. apply IHe2 in E2. clear IHe1 IHe2.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2].
  exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
  simpl. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
  destruct (feval_exp _ _ _ _ e1 _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  destruct (feval_exp _ _ _ _ e2 _ _) as (u2,ma2). destruct u2. destruct E2 as [U2 M2].
  simpl in U1,U2. destruct z; destruct z0; try discriminate. injection U1; injection U2; intros; subst.
  split.
    destruct b; reflexivity.
    apply conjallT_app; assumption.

  (* UnOp *)
  apply IHe in E1. clear IHe.
  destruct E1 as [unk1 E1].
  exists unk1.
  simpl.
  destruct (feval_exp _ _ _ _ e _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  split.
    destruct u; reflexivity.
    assumption.

  (* Cast *)
  apply IHe in E1. clear IHe.
  destruct E1 as [unk1 E1].
  exists unk1.
  simpl.
  destruct (feval_exp _ _ _ _ e _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  split.
    destruct c; reflexivity.
    assumption.

  (* Let *)
  rewrite <- updlst_remlst in E2.
  change (updlst s _ vupdate [v:=u1]) with (updlst s ((v,u1)::remlst v l) vupdate) in E2.
  apply IHe1 in E1. apply IHe2 in E2. clear IHe1 IHe2.
  destruct E1 as [unk1 E1]. destruct E2 as [unk2 E2].
  exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
  simpl. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
  destruct (feval_exp _ _ _ _ e1 _ _) as (u0,ma1). destruct E1 as [U1 M1]. subst.
  destruct (feval_exp _ _ _ _ e2 _ _) as (u2,ma2). destruct E2 as [U2 M2]. subst.
  split.
    reflexivity.
    apply conjallT_app; assumption.

  (* Unknown *)
  exists (fun _ => n).
  simpl. split.
    rewrite N.mod_small by assumption. reflexivity.
    exact I.

  (* Ife *)
  specialize (IHe1 _ _ E1). destruct IHe1 as [unk1 IHe1].
  rename n1 into c. rename w1 into w.
  eassert (IHe': exists unk', match c with 0 => _ | _ => _ end).
    destruct c. exact (IHe3 _ _ E'). exact (IHe2 _ _ E').
  clear IHe2 IHe3. destruct IHe' as [unk' IHe'].
  exists (fun i => match i with xO j => unk1 j | xI j => unk' j | _ => N0 end).
  cbn - [feval_width].
  change (unknowns0 _) with unk1. change (unknowns1 _) with unk'.
  destruct (feval_exp _ _ _ _ e1 _ _) as [[b1 m1 n1 w1] ma1].
  destruct IHe1 as [U1 M1]. destruct b1; [|discriminate U1]. inversion U1. subst c w. clear U1.
  destruct (feval_exp _ _ _ _ e2 _ _) as [[b2 m2 n2 w2] ma2].
  destruct (feval_exp _ _ _ _ e3 _ _) as [[b3 m3 n3 w3] ma3].
  replace (if (_:bool) then b2 else _) with (if n1 then b3 else b2) by (destruct n1, b3, b2; reflexivity).
  split.
    destruct feval_width as [w|] eqn:FW.

      simpl in FW.
      destruct (feval_width l e2) as [w2'|] eqn:FEW2; [|discriminate].
      destruct (feval_width l e3) as [w3'|] eqn:FEW3; [|discriminate].
      destruct (w2' =? w3') eqn:WEQ; [|discriminate].
      inversion FW. subst w2'. apply N.eqb_eq in WEQ. subst w3'.
      destruct n1; apply proj1 in IHe'; subst u.
        eapply feval_width_sound in FEW3; [|exact E']. subst w. destruct b3; reflexivity.
        eapply feval_width_sound in FEW2; [|exact E']. subst w. destruct b2; reflexivity.

      destruct n1; apply IHe'.

    destruct ma2.
      destruct ma3.
        assumption.
        apply conjallT_app. assumption. split.
          destruct n1. apply conjall_iffT, IHe'. exact I.
          exact I.
      apply conjallT_app. assumption. split.
        destruct n1; apply conjall_iffT, IHe'.
        exact I.

  (* Extract *)
  apply IHe in E1. clear IHe.
  destruct E1 as [unk1 E1].
  exists unk1.
  simpl.
  destruct (feval_exp _ _ _ _ e _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  split. reflexivity. assumption.

  (* Concat *)
  specialize (IHe1 _ _ E1). destruct IHe1 as [unk1 IHe1].
  specialize (IHe2 _ _ E2). destruct IHe2 as [unk2 IHe2].
  exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
  cbn - [feval_width]. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
  destruct (feval_exp _ _ _ _ e1 _ _) as (u1,ma1). destruct u1. destruct IHe1 as [U1 M1].
  destruct (feval_exp _ _ _ _ e2 _ _) as (u2,ma2). destruct u2. destruct IHe2 as [U2 M2].
  simpl in U1,U2. destruct z; destruct z0; try discriminate. injection U1; injection U2; intros; subst.
  split.
    destruct feval_width eqn:FW.
      eapply feval_width_sound in FW; [|econstructor; eassumption]. subst. reflexivity.
      reflexivity.
    apply conjallT_app; assumption.
Qed.

Theorem reduce_stmt:
  forall noe noet s l q h s' x (XS: exec_stmt h (updlst s l vupdate) q s' x)
         (NOE: noe = noe_setop) (NOET: noet = noe_typop),
  exists unk, match fexec_stmt noe noet h q s unk l with
              | FIS l' (FIExit x') ma => (s' = updlst s l' (noet NOE_UPD) /\ x = x') /\ conjallT ma
              | FIS l' (FIStmt q') ma => exec_stmt h (updlst s l' (noet NOE_UPD)) q' s' x /\ conjallT ma
              end.
Proof.
  intros. subst noe noet. unfold noe_typop at -1.
  revert s l s' x XS. induction q using stmt_ind2; intros;
  inversion XS; clear XS; subst.

  (* Nop *)
  exists (fun _ => N0).
  simpl. repeat split.

  (* Move *)
  eapply reduce_exp in E; [|reflexivity..]. destruct E as [unk E]. exists unk.
  simpl. destruct feval_exp as (u1,ma1).
  destruct E as [U1 M1]. subst.
  repeat split.
    simpl. rewrite updlst_remlst. reflexivity.
    exact M1.

  (* Jmp *)
  eapply reduce_exp in E; [|reflexivity..]. destruct E as [unk E]. exists unk.
  simpl. destruct feval_exp as (u1,ma1). destruct u1.
  destruct E as [U1 M1]. simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  repeat split. exact M1.

  (* Exn *)
  exists (fun _ => N0).
  simpl. repeat split.

  (* Seq1 *)
  apply IHq1 in XS0. clear IHq1. destruct XS0 as [unk XS1].
  exists (fun i => match i with xO j => unk j | _ => N0 end).
  simpl. change (unknowns0 _) with unk.
  destruct fexec_stmt as [l1 [x1|q1'] ma1].
    destruct XS1 as [[S1 X1] M1]. subst. repeat split. exact M1.
    split; try apply XSeq1; apply XS1.

  (* Seq2 *)
  apply IHq1 in XS1. clear IHq1. destruct XS1 as [unk1 XS1].
  destruct (fexec_stmt _ _ _ q1 _ _) as [l1 [x1|q1'] ma1] eqn:FS1.

    destruct XS1 as [[S1 X1] M1]. subst.
    apply IHq2 in XS0. clear IHq2. destruct XS0 as [unk2 XS2].
    exists (fun i => match i with xO j => unk1 j | xI j => unk2 j | _ => N0 end).
    simpl. change (unknowns0 _) with unk1. change (unknowns1 _) with unk2.
    rewrite FS1.
    destruct (fexec_stmt _ _ _ q2 _ _) as [l2 [x2|q2'] ma2].
      destruct XS2 as [[S2 X2] M2]. subst. repeat split. apply conjallT_app; assumption.
      split. apply XS2. apply conjallT_app. exact M1. apply XS2.

    exists (fun i => match i with xO j => unk1 j | _ => N0 end).
    simpl. change (unknowns0 _) with unk1. rewrite FS1.
    split. eapply XSeq2. apply XS1. assumption. apply XS1.

  (* If *)
  eapply reduce_exp in E; [|reflexivity..]. destruct E as [unk E].
  exists unk. simpl.
  destruct feval_exp as [u ma0].
  destruct E as [E M]. destruct u as [z m n w]. destruct z; [|discriminate]. injection E; intros; subst.
  split; assumption.

  (* Rep *)
  eapply reduce_exp in E; [|reflexivity..]. destruct E as [unk E].
  exists unk. simpl.
  destruct feval_exp as [u ma0].
  destruct E as [E M]. destruct u as [z m c ?]. destruct z; [|discriminate]. injection E; intros; subst.
  split; assumption.
Qed.

Theorem update_updlst:
  forall upd s v u l,
  updlst (upd s v u) (rev l) upd = updlst s (rev ((v,u)::l)) upd.
Proof.
  intros. simpl. generalize (rev l) as l'. induction l'.
    reflexivity.
    simpl. rewrite IHl'. reflexivity.
Qed.

Theorem if_N_same: forall A (n:N) (a:A), (if n then a else a) = a.
Proof. intros. destruct n; reflexivity. Qed.

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

Lemma fexec_stmt_init:
  forall {EQT} (eq1 eq2:EQT) h s q s' x (XS: exec_stmt h s q s' x),
  eq1=eq2 -> exec_stmt h (updlst s (rev nil) vupdate) q s' x /\ (eq1=eq2).
Proof. split; assumption. Qed.

Lemma fexec_stmt_fin:
  forall a_h a_s a_s' a_x h s l q s' x, 
  exec_stmt h (updlst s l vupdate) q s' x /\ (a_h,a_s,a_s',a_x)=(h,s,s',x) ->
  exec_stmt a_h (updlst a_s l vupdate) q a_s' a_x.
Proof.
  intros. destruct H as [H1 H2]. inversion H2. exact H1.
Qed.

Lemma fexec_stmt_updn:
  forall {EQT} a (eq1 eq2:EQT) h s v n w l q s' x,
  exec_stmt h (updlst (vupdate s v (VaN n w)) (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,n) ->
  exec_stmt h (updlst s (rev ((v, VaN a w)::l)) vupdate) q s' x /\ eq1=eq2.
Proof.
  intros. destruct H as [H1 H2]. inversion H2. split.
    rewrite <- update_updlst. apply H1.
    reflexivity.
Qed.

Lemma fexec_stmt_updm:
  forall {EQT} a (eq1 eq2:EQT) h s v m w l q s' x,
  exec_stmt h (updlst (vupdate s v (VaM m w)) (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,m) ->
  exec_stmt h (updlst s (rev ((v, VaM a w)::l)) vupdate) q s' x /\ eq1=eq2.
Proof.
  intros. destruct H as [H1 H2]. inversion H2. split.
    rewrite <- update_updlst. apply H1.
    reflexivity.
Qed.

Lemma fexec_stmt_updu:
  forall {EQT} a (eq1 eq2:EQT) h s v u l q s' x,
  exec_stmt h (updlst (vupdate s v u) (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,u) ->
  exec_stmt h (updlst s (rev ((v,u)::l)) vupdate) q s' x /\ eq1=eq2.
Proof.
  intros. destruct H as [H1 H2]. inversion H2. split.
    rewrite <- update_updlst. apply H1.
    reflexivity.
Qed.

Lemma fexec_stmt_hypn:
  forall {EQT} a (eq1 eq2:EQT) h s v n w l q s' x (SV: s v = VaN n w),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,n) ->
  exec_stmt h (updlst s (rev ((v, VaN a w)::l)) vupdate) q s' x /\ eq1=eq2.
Proof.
  intros. destruct H as [H1 H2]. inversion H2. split.
    rewrite <- update_updlst. change (vupdate s) with (update s). rewrite <- store_upd_eq by exact SV. apply H1.
    reflexivity.
Qed.

Lemma fexec_stmt_hypm:
  forall {EQT} a (eq1 eq2:EQT) h s v m w l q s' x (SV: s v = VaM m w),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,m) ->
  exec_stmt h (updlst s (rev ((v, VaM a w)::l)) vupdate) q s' x /\ eq1=eq2.
Proof.
  intros. destruct H as [H1 H2]. inversion H2. split.
    rewrite <- update_updlst. change (vupdate s) with (update s). rewrite <- store_upd_eq by exact SV. apply H1.
    reflexivity.
Qed.

Lemma fexec_stmt_hypu:
  forall {EQT} a (eq1 eq2:EQT) h s v u l q s' x (SV: s v = u),
  exec_stmt h (updlst s (rev l) vupdate) q s' x /\ (eq1,a)=(eq2,u) ->
  exec_stmt h (updlst s (rev ((v,u)::l)) vupdate) q s' x /\ eq1=eq2.
Proof.
  intros. destruct H as [H1 H2]. inversion H2. split.
    rewrite <- update_updlst. change (vupdate s) with (update s). rewrite <- store_upd_eq by exact SV. apply H1.
    reflexivity.
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

Definition other_vars_read_exp (l: list (var * value)) e :=
  let old := List.map fst l in
  List.filter (fun v => negb (existsb (vareqb v) old)) (vars_read_by_exp e).

Lemma conjallT_Forall: forall l, Forall (fun a => a) l <-> conjallT l.
Proof.
  intros. rewrite Forall_fold_right. unfold conjallT. split; intro; assumption.
Qed.

Theorem fstore_init: forall s EQT (eq1 eq2: EQT),
  eq1 = eq2 ->
  (s = (updlst s (rev nil) update)) /\ eq1 = eq2.
Proof. intros. subst. split; reflexivity. Qed.

Theorem fstore_updu: forall {EQT} (eq1 eq2: EQT) s0 s v u l,
  (s0 = updlst (update s v u) (rev l) update /\ eq1 = eq2) ->
  (s0 = updlst s (rev ((v, u)::l)) update /\ eq1 = eq2).
Proof.
  intros. rewrite <- update_updlst. destruct H; subst; split; reflexivity.
Qed.

Theorem fstore_updn: forall {EQT} (eq1 eq2: EQT) s0 s v a w n l,
  (s0 = updlst (update s v (VaN n w)) (rev l) update /\ (eq1, a) = (eq2, n)) ->
  (s0 = updlst s (rev ((v, (VaN a w))::l)) update /\ eq1 = eq2).
Proof.
  intros. rewrite <- update_updlst. destruct H. inversion H0. subst.
  split; reflexivity.
Qed.

Theorem fstore_updm: forall {EQT} (eq1 eq2: EQT) s0 s v a w m l,
  (s0 = updlst (update s v (VaM m w)) (rev l) update /\ (eq1, a) = (eq2, m)) ->
  (s0 = updlst s (rev ((v, (VaM a w))::l)) update /\ eq1 = eq2).
Proof.
  intros. rewrite <- update_updlst. destruct H. inversion H0. subst.
  split; reflexivity.
Qed.

Theorem fstore_hypn: forall {EQT} {eq1 eq2: EQT} {s0 a s v n w l} (SV: s v = VaN n w),
  (s0 = updlst s (rev l) update /\ (eq1, a) = (eq2, n)) ->
  (s0 = updlst s (rev ((v, (VaN a w))::l)) update /\ eq1 = eq2).
Proof.
  intros. destruct H. inversion H0. subst.
  rewrite <- update_updlst, <- store_upd_eq by exact SV. split; reflexivity.
Qed.

Theorem fstore_hypm: forall {EQT} {eq1 eq2: EQT} {s0 a s v m w l} (SV: s v = VaM m w),
  (s0 = updlst s (rev l) update /\ (eq1, a) = (eq2, m)) ->
  (s0 = updlst s (rev ((v, (VaM a w))::l)) update /\ eq1 = eq2).
Proof.
  intros. destruct H. inversion H0. subst.
  rewrite <- update_updlst, <- store_upd_eq by exact SV. split; reflexivity.
Qed.

Theorem fstore_hypu: forall EQs s0 s v u l (SV: s v = u),
  (s0 = updlst s (rev l) update /\ EQs) <->
  (s0 = updlst s (rev ((v, u)::l)) update /\ EQs).
Proof.
  intros. rewrite <- update_updlst, <- store_upd_eq by exact SV.
  split; intros; destruct H; split; assumption.
Qed.

Theorem fstore_typ: forall {c s0 s t l EQs} v (MDL: models c s) (CV: c v = Some t),
  (s0 = updlst s (rev l) update /\ EQs) ->
  match t with
  | NumT w => exists a, s v = VaN a w /\ s0 =
      updlst s (rev ((v, VaN a w) :: l)) update /\ EQs
  | MemT w => exists a, s v = VaM a w /\ s0 =
      updlst s (rev ((v, VaM a w) :: l)) update /\ EQs
  end.
Proof.
  intros. einversion trivial (MDL v); eexists; split; try reflexivity;
  rewrite <- fstore_hypu; symmetry in H2; try assumption.
Qed.

Theorem fstore_fin: forall (h: hdomain) a_c a_h a_s0 a_s e c s0 s l t
  (MDL: models c s0) (TE: hastyp_exp c e t),
  (s0 = updlst s l update /\ (a_c, a_h, a_s0, a_s) = (c, h, s0, s)) ->
  (a_h, a_s0) = (a_h, updlst a_s l update) /\
    models a_c (updlst a_s l update) /\ hastyp_exp a_c e t.
Proof. intros. destruct H. inversion H0. subst. repeat split; trivial2. Qed.

Lemma feval_binop_eq_eval_binop: forall b n1 n2 w,
  of_uvalue (feval_binop b noe_setop w n1 n2) = eval_binop b w n1 n2.
Proof. intros. destruct b; reflexivity. Qed.

Lemma feval_unop_eq_eval_unop: forall op n1 w,
  of_uvalue (feval_unop op noe_setop n1 w) = eval_unop op n1 w.
Proof. intros. destruct op; reflexivity. Qed.

Lemma feval_cast_eq_cast: forall op n1 w w',
  feval_cast op noe_setop w w' n1 = cast op w w' n1.
Proof. intros. destruct op; reflexivity. Qed.

Theorem feval_width_sound2:
  forall h s e l ma unk z m n w w' (FW: feval_width l e = Some w)
    (FE: (feval_exp noe_setop noe_typop h s e unk l) = (VaU z m n w', ma)), w = w'.
Proof.
  induction e; intros; simpl in *.
  - (* Var *) rewrite FW in FE. unfold feval_varwidth, vwidth in *.
    destruct find eqn:Found; try discriminate. simpl in FW. destruct p as [v' u'].
    inversion FE. inversion FW. subst. clear FW FE.
    revert v' u' Found. induction l as [|[v'' u''] l]; intros.
    + discriminate.
    + simpl in Found. unfold vupdate in *. simpl. destruct (v == v'').
      * inversion Found. subst. rewrite update_updated. reflexivity.
      * rewrite update_frame by assumption. eapply IHl. eassumption.
  - (* Word *) inversion FW. inversion FE. subst. reflexivity.
  - (* Load *) inversion FW. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. reflexivity.
  - (* Store *) destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e3) as [ [z3 m3 n3 w3] ma3] eqn: E3.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. erewrite <- IHe1 by eassumption. reflexivity.
  - (* Binop *) destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    destruct b; inversion FE; subst;
    solve [einstantiate trivial IHe1|inversion FW; reflexivity].
  - (* Unop *) destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E.
    destruct u; inversion FE; subst; einstantiate trivial IHe.
  - (* Cast *) destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E.
    inversion FW. subst. destruct c; inversion FE; reflexivity.
  - (* Let *) destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. einstantiate IHe2; [|trivial2|trivial2]. simpl.
    simpl in E2. erewrite feval_width_mono; [reflexivity| |eassumption]. simpl.
    unfold feval_varwidth. intros v0 b LU1. destruct (v0 == v).
    + subst. destruct (feval_width _ e1) eqn: FW1.
      * simpl in *. vreflexivity v. simpl in *. inversion LU1. subst.
        einstantiate trivial IHe1. subst. destruct z1; reflexivity.
      * simpl in *. rewrite find_filter_none in LU1; try discriminate.
        intros. destruct (v == fst x); [reflexivity|discriminate].
    + destruct (feval_width _ e1) eqn: FW1; simpl in *.
      * vantisym v0 v by assumption.
        rewrite find_remlst; [|intros [? ?] ?; subst; simpl;
        vantisym v0 v1; solve [assumption|reflexivity]]. assumption.
      * rewrite find_filter in LU1. rewrite find_remlst. assumption.
        intros [? ?] ?. subst. simpl. vantisym v0 v1 by assumption.
        reflexivity. intros [? ?] ?. simpl in *. destruct (v == v1);
        try discriminate. subst. vantisym v0 v1 by assumption. reflexivity.
  - (* Unk *) inversion FE. inversion FW. subst. reflexivity.
  - (* Ite *) destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2'] ma2] eqn: E2.
    destruct (feval_exp _ _ _ _ e3) as [ [z3 m3 n3 w3'] ma3] eqn: E3.
    inversion FE. subst. clear FE.
    destruct feval_width as [w2|] eqn: FW2; try discriminate.
    destruct (feval_width _ e3) as [w3|] eqn: FW3; try discriminate.
    destruct (w2 =? w3) eqn: EQ; try discriminate.
    apply N.eqb_eq in EQ. subst. inversion FW. subst. clear FW.
    einstantiate trivial IHe2. einstantiate trivial IHe3. subst.
    inversion H0. subst. reflexivity.
  - (* Extract *) destruct feval_exp as [ [z0 m0 n0 w0] ma0] eqn: E0.
    inversion FE. inversion FW. reflexivity.
  - (* Concat *) destruct feval_exp as [ [z1 m1 n1 w1'] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2'] ma2] eqn: E2.
    destruct feval_width as [w1|] eqn: FW1; try discriminate.
    destruct (feval_width _ e2) as [w2|] eqn: FW2; try discriminate.
    inversion FE. inversion FW. reflexivity.
Qed.

Theorem preservation_feval_exp:
  forall h s e c t l u' ma unk
    (MDL: models c (updlst s l vupdate)) (TE: hastyp_exp c e t)
    (FE: (feval_exp noe_setop noe_typop h s e unk l) = (u', ma))
    (CONJ: conjallT ma),
    hastyp_val (of_uvalue u') t.
Proof.
  intros. subst. revert_all. induction e; intros; inversion TE; subst; clear TE.
  - (* Var *) simpl in FE. einversion trivial (MDL v); rewrite <- H1 in *;
    destruct feval_varwidth as [_|]; inversion FE; subst; simpl; constructor;
    assumption.
  - (* Word *) inversion FE. subst. simpl. constructor. assumption.
  - (* Load *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. unfold of_uvalue. constructor.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    inversion CONJ. subst. apply Forall_app in H2. destruct H2 as [MA1 MA2].
    rewrite conjallT_Forall in *.

    einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe2 as IHe2.
    destruct z1; inversion IHe1; subst. destruct z2; inversion IHe2; subst.

    apply getmem_bound. assumption.
  - (* Store *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e3) as [ [z3 m3 n3 w3] ma3] eqn: E3.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. unfold of_uvalue.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    inversion CONJ. subst. repeat rewrite Forall_app in H2.
    destruct H2 as [MA1 [MA2 MA3] ]. rewrite conjallT_Forall in *.

    einstantiate trivial IHe1 as IHe1. destruct z1; inversion IHe1.
    einstantiate trivial IHe3 as IHe3. destruct z3; inversion IHe3. subst.
    constructor. apply setmem_welltyped; assumption.
  - (* Binop *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. rewrite feval_binop_eq_eval_binop.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    repeat rewrite Forall_app in CONJ. destruct CONJ as [MA1 MA2].
    rewrite conjallT_Forall in *.

    einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe2 as IHe2.
    destruct z1; inversion IHe1; destruct z2; inversion IHe2; subst.

    apply typesafe_binop; assumption.
  - (* Unop *) simpl in FE. destruct feval_exp as [ [z m n w'] ma'] eqn: E.
    inversion FE. subst. rewrite feval_unop_eq_eval_unop.

    einstantiate trivial IHe as IHe. destruct z; inversion IHe. subst.
    apply typesafe_unop; assumption.
  - (* Cast *) simpl in FE. destruct feval_exp as [ [z m n w'] ma'] eqn: E.
    inversion FE. subst. rewrite feval_cast_eq_cast. simpl. constructor.
    einstantiate trivial IHe as IHe. destruct z; inversion IHe. subst.
    einversion trivial typesafe_cast.
  - (* Let *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    repeat rewrite Forall_app in CONJ. destruct CONJ as [MA1 MA2].
    rewrite conjallT_Forall in *.

    einstantiate trivial (IHe2 (c [v := Some t1])) as IHe2.
    unfold models. intros. destruct (v0 == v).
    + subst. unfold vupdate. simpl. rewrite update_updated.
      rewrite update_updated in CV. inversion CV. subst.
      einstantiate trivial IHe1 as IHe1.
    + unfold vupdate. simpl. rewrite updlst_remlst.
      rewrite update_frame in CV by assumption. rewrite update_frame by assumption.
      apply MDL. assumption.
  - (* Unknown *) simpl in FE. inversion FE. subst. simpl. constructor.
    apply N.mod_lt. destruct w; discriminate.
  - (* Ite *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2'] ma2] eqn: E2.
    destruct (feval_exp _ _ _ _ e3) as [ [z3 m3 n3 w3'] ma3] eqn: E3.
    inversion FE. subst.
    eassert (X: of_uvalue _ = of_uvalue (if n1 then VaU z3 m3 n3 w3' else
    VaU z2 m2 n2 w2')); [|rewrite X].
      destruct feval_width as [w2|] eqn: FW2; [|destruct n1; reflexivity].
      destruct (feval_width _ e3) as [w3|] eqn: FW3; [|destruct n1; reflexivity].
      destruct (w2 =? w3) eqn: EQ; [|destruct n1; reflexivity].
      apply N.eqb_eq in EQ. subst.
      einstantiate trivial feval_width_sound2.
      einstantiate trivial (feval_width_sound2 h s e2). subst.
      destruct Bool.eqb eqn: Beq; destruct n1; try reflexivity.
      apply Bool.eqb_prop in Beq. subst. reflexivity.
    assert (conjallT (ma1 ++ (if n1 then conjall ma3 else conjall ma2) :: nil)).
      destruct ma2, ma3; try solve [eapply eq_rect; trivial2].
      apply conjallT_app. assumption. simpl. split; destruct n1; exact I.
    rewrite <- conjallT_Forall, Forall_app in H. destruct H as [_ MA23].
    inversion MA23 as [|? ? MA23']. subst.
    destruct n1; rewrite <- conjall_iffT in MA23';
    solve [einstantiate trivial IHe2|einstantiate trivial IHe3].
  - (* Extract *) simpl in FE. destruct feval_exp as [ [z0 m0 n0 w0] ma0] eqn: E0.
    inversion FE. subst. simpl. constructor. apply N.mod_lt.
    destruct N.sub; discriminate.
  - (* Concat *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1''] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2''] ma2] eqn: E2.
    inversion FE; subst. clear FE.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    repeat rewrite Forall_app in CONJ. destruct CONJ as [MA1 MA2].
    rewrite conjallT_Forall in *.

    einversion trivial IHe1. einversion trivial IHe2.
    destruct z1; inversion H1. destruct z2; inversion H3.
    inversion H2. inversion H4. subst. clear H1 H2 H3 H4.

    assert (N.lor (N.shiftl n1 w2) n2 < 2 ^ (w1 + w2)).
      apply lor_bound. apply shiftl_bound. assumption.
      eapply N.lt_le_trans. eassumption. apply N.pow_le_mono_r. discriminate.
      rewrite N.add_comm. apply N.le_add_r.

    destruct feval_width as [w1'|] eqn: FW1; [|constructor; assumption].
    destruct (feval_width _ e2) as [w2'|] eqn: FW2; [|constructor; assumption].
    simpl. einstantiate trivial feval_width_sound2. clear FW2.
    einstantiate trivial feval_width_sound2. subst. constructor. assumption.
Qed.

Theorem do_eval_exp:
  forall h s e c t l noet noe u' ma (NU: forall_exps_in_exp not_unknown e)
    (MDL: models c (updlst s l vupdate)) (TE: hastyp_exp c e t)
    (FE: (feval_exp noe noet h s e (fun _ => 0) l) = (u', ma))
    (CONJ: conjallT ma), (noet = noe_typop) -> (noe = noe_setop) ->
    eval_exp h (updlst s l update) e (of_uvalue u').
Proof.
  intros. subst. remember (fun _ => 0) as unk. clear Hequnk. revert_all.
  induction e; intros; inversion TE; subst; clear TE.
  - (* Var *) inversion FE. subst. unfold of_uvalue.
    destruct feval_varwidth; simpl; destruct (updlst s l vupdate v) eqn: Upd;
    simpl; rewrite <- Upd; constructor.
  - (* Word *) inversion FE. subst. unfold of_uvalue. constructor.
  - (* Load *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. unfold of_uvalue.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    inversion CONJ. subst. apply Forall_app in H2. destruct H2 as [MA1 MA2].
    rewrite conjallT_Forall in *.
    (* Break apart not unknowns *) inversion NU as [_ [NU1 NU2] ].

    einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe2 as IHe2.
    einversion trivial preservation_feval_exp. clear T2.
    einversion trivial preservation_feval_exp. clear T1.
    inversion H3. inversion H5. destruct z2, z1; inversion H2; inversion H4.
    subst. clear H2 H3 H4 H5. econstructor; eassumption.
  - (* Store *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e3) as [ [z3 m3 n3 w3] ma3] eqn: E3.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. unfold of_uvalue.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    inversion CONJ. subst. repeat rewrite Forall_app in H2.
    destruct H2 as [MA1 [MA2 MA3]]. rewrite conjallT_Forall in *.
    (* Break apart not unknowns *) inversion NU as [_ [NU1 [NU2 NU3]]].

    einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe2 as IHe2.
    einstantiate trivial IHe3 as IHe3.

    einversion trivial preservation_feval_exp. clear T3.
    einversion trivial preservation_feval_exp. clear T2.
    einversion trivial preservation_feval_exp. clear T1.

    inversion H3. inversion H5. inversion H7.
    destruct z3, z2, z1; inversion H2; inversion H4; inversion H6.
    subst. clear H2 H3 H4 H5 H6 H7. econstructor; eassumption.
  - (* Binop *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst. rewrite feval_binop_eq_eval_binop.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    repeat rewrite Forall_app in CONJ. destruct CONJ as [MA1 MA2].
    rewrite conjallT_Forall in *.
    (* Break apart not unknowns *) inversion NU as [_ [NU1 NU2]].

    einstantiate trivial IHe1 as IHe1. einstantiate trivial IHe2 as IHe2.
    einversion trivial preservation_feval_exp. clear T2.
    einversion trivial preservation_feval_exp. clear T1.

    inversion H2. inversion H4. destruct z2, z1; inversion H1; inversion H3.
    subst. clear H1 H2 H3 H4. constructor; assumption.
  - (* Unop *) simpl in FE. destruct feval_exp as [ [z m n w'] ma'] eqn: E.
    inversion FE. subst. rewrite feval_unop_eq_eval_unop.

    (* Break apart not unknowns *) inversion NU as [_ NU1].

    einstantiate trivial IHe as IHe. einversion trivial preservation_feval_exp.
    destruct z; inversion H1. inversion H2. subst.
    constructor. assumption.
  - (* Cast *) simpl in FE. destruct feval_exp as [ [z m n w'] ma'] eqn: E.
    inversion FE. subst. rewrite feval_cast_eq_cast. simpl.
    (* Break apart not unknowns *) inversion NU as [_ NU1].
    einstantiate trivial IHe as IHe. einversion trivial preservation_feval_exp.
    destruct z; inversion H1. inversion H2. subst. constructor. assumption.
  - (* Let *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2] ma2] eqn: E2.
    inversion FE. subst.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    repeat rewrite Forall_app in CONJ. destruct CONJ as [MA1 MA2].
    rewrite conjallT_Forall in *.

    (* Break apart not unknowns *) inversion NU as [_ [NU1 NU2]].

    einstantiate trivial IHe1 as IHe1. econstructor. eassumption.
    einstantiate trivial (IHe2 (c [v := Some t1])) as IHe2;
    [| simpl in IHe2; rewrite updlst_remlst in IHe2; assumption].
    unfold models. intros. destruct (v0 == v).
    + subst. unfold vupdate. simpl. rewrite update_updated.
      rewrite update_updated in CV. inversion CV. subst.
      einstantiate trivial preservation_feval_exp.
    + unfold vupdate. simpl. rewrite updlst_remlst.
      rewrite update_frame in CV by assumption. rewrite update_frame by assumption.
      apply MDL. assumption.
  - (* Unknown *) inversion NU.
  - (* Ite *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2'] ma2] eqn: E2.
    destruct (feval_exp _ _ _ _ e3) as [ [z3 m3 n3 w3'] ma3] eqn: E3.
    inversion FE. subst. clear FE.
    eassert (X: of_uvalue _ = of_uvalue (if n1 then VaU z3 m3 n3 w3' else
    VaU z2 m2 n2 w2')); [|rewrite X].
      destruct feval_width as [w2|] eqn: FW2; [|destruct n1; reflexivity].
      destruct (feval_width _ e3) as [w3|] eqn: FW3; [|destruct n1; reflexivity].
      destruct (w2 =? w3) eqn: EQ; [|destruct n1; reflexivity].
      apply N.eqb_eq in EQ. subst.
      einstantiate trivial feval_width_sound2.
      einstantiate trivial (feval_width_sound2 h s e2). subst.
      destruct Bool.eqb eqn: Beq; destruct n1; try reflexivity.
      apply Bool.eqb_prop in Beq. subst. reflexivity.
    (* Conditionally break apart preconditions *)
    assert (conjallT (ma1 ++ (if n1 then conjall ma3 else conjall ma2) :: nil)).
      destruct ma2, ma3; try solve [eapply eq_rect; trivial2].
      apply conjallT_app. assumption. simpl. split; destruct n1; exact I.
    rewrite <- conjallT_Forall, Forall_app in H. destruct H as [MA1 MA23].
    inversion MA23 as [|? ? MA23']. subst. rewrite conjallT_Forall in *.
    (* Break apart not unknowns *) inversion NU as [_ [NU1 [NU2 NU3]]].

    einstantiate trivial IHe1 as IHe1.
    einversion trivial (preservation_feval_exp h s e1).
    destruct z1; inversion H2. inversion H3. subst.
    econstructor. eassumption. destruct n1; rewrite <- conjall_iffT in MA23';
    solve [einstantiate trivial IHe2|einstantiate trivial IHe3].
  - (* Extract *) simpl in FE. destruct feval_exp as [ [z0 m0 n0 w0] ma0] eqn: E0.
    inversion FE. subst. simpl.
    (* Break apart not unknowns *) inversion NU as [_ NU1].
    einstantiate trivial IHe. einversion trivial preservation_feval_exp.
    destruct z0; inversion H2. inversion H3. subst.
    econstructor. eassumption.
  - (* Concat *) simpl in FE. destruct feval_exp as [ [z1 m1 n1 w1''] ma1] eqn: E1.
    destruct (feval_exp _ _ _ _ e2) as [ [z2 m2 n2 w2''] ma2] eqn: E2.
    inversion FE; subst. clear FE.

    (* Break apart conjunctive preconditions *) apply conjallT_Forall in CONJ.
    repeat rewrite Forall_app in CONJ. destruct CONJ as [MA1 MA2].
    rewrite conjallT_Forall in *.

    (* Break apart not unknowns *) inversion NU as [_ [NU1 NU2]].

    einstantiate trivial IHe1. einstantiate trivial IHe2.
    einversion trivial preservation_feval_exp. clear T2.
    einversion trivial preservation_feval_exp. clear T1.
    inversion H4. inversion H6. destruct z2, z1; inversion H3; inversion H5. subst.

    destruct feval_width as [w1'|] eqn: FW1; [|constructor; assumption].
    destruct (feval_width _ e2) as [w2'|] eqn: FW2; [|constructor; assumption].
    simpl. einstantiate trivial feval_width_sound2. clear FW2.
    einstantiate trivial feval_width_sound2. subst. constructor. assumption.
    assumption.
Qed.

End PicinaeFInterp.

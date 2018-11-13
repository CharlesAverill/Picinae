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
   Then compile this module with menu option                MMMMMMMMMMM7..ZNOOMZ
   Compile->Compile_buffer.                                  MMMMMMMMMM$.$MOMO=7
                                                              MDMMMMMMMO.7MDM7M+
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

Definition uvalue_of (v:value) :=
  match v with
  | VaN n w => VaU true (fun _ => 0) n w
  | VaM m w => VaU false m 0 w
  end.


(* When the interpreter cannot determine an IL variable's type and/or value
   (e.g., because store s is a Coq variable), the interpreter returns an
   expression that contains the following accessor functions to refer to the
   unknown type/value. *)

Definition vtyp (u: option value) :=
  match u with Some (VaM _ _) => false | _ => true end.

Definition vnum (u: option value) :=
  match u with Some (VaN n _) => n | _ => N0 end.

Definition vmem (u: option value) :=
  match u with Some (VaM m _) => m | _ => (fun _ => N0) end.

Definition vwidth (u: option value) :=
  match u with Some (VaN _ w) | Some (VaM _ w) => w | None => N0 end.

Definition vget (u:option value) : uvalue :=
  match u with None => VaU true (fun _ => 0) 0 0
             | Some u => uvalue_of u
  end.

Lemma vtyp_num n w: vtyp (Some (VaN n w)) = true. Proof eq_refl.
Lemma vtyp_mem m w: vtyp (Some (VaM m w)) = false. Proof eq_refl.
Lemma vnum_num n w: vnum (Some (VaN n w)) = n. Proof eq_refl.
Lemma vmem_mem m w: vmem (Some (VaM m w)) = m. Proof eq_refl.
Lemma vwidth_num n w: vwidth (Some (VaN n w)) = w. Proof eq_refl.
Lemma vwidth_mem m w: vwidth (Some (VaM m w)) = w. Proof eq_refl.

Lemma fold_vget:
  forall u, VaU (vtyp u) (vmem u) (vnum u) (vwidth u) = vget u.
Proof. intro. destruct u as [u|]; [destruct u|]; reflexivity. Qed.


(* Unknowns are modeled as return values of an oracle function f that maps
   unknown-identifiers (binary positive numbers) to the values of each
   unknown.  In order to assign a unique unknown-identifier to each unknown
   appearing in the statement without preprocessing the statement to count
   them all, we use a trick from proofs about partitioning countably infinite
   domains into multiple countably infinite domains:  To assign mutually
   exclusive identifiers to two expressions e1 and e2, we assign only even
   identifiers to unknowns in e1 and only odd identifiers to unknowns in e2.
   When this strategy is followed recursively, all unknowns get unique ids. *)

Definition unknowns0 f i : N := f (xO i).
Definition unknowns1 f i : N := f (xI i).
Definition unknowns00 f i : N := f (xO (xO i)).
Definition unknowns01 f i : N := f (xI (xO i)).
Definition unknowns10 f i : N := f (xO (xI i)).


(* The interpreter accmulates memory access predicates as a separate list
   of propositions during interpretation.  This allows the proof to infer
   memory accessibility facts from successful executions.  The list of
   propositions is later assembled into a conjunction, which is then split
   off into separate hypotheses in the proof context.  Sometimes it is
   useful to end the conjunction with a prop of "True" (to signal the end)
   while other times it is more succinct to not include this end-prop.
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


(* For speed, the interpreter function is designed to be evaluated using
   vm_compute or native_compute.  However, those tactics perform uncontrolled
   expansion of every term, resulting in huge terms that are completely
   intractable for users (and very slow for Coq to manipulate).  To control
   and limit this expansion, we create a Module that hides the expansions of
   functions we don't want vm_compute to evaluate.  After vm_compute completes,
   we replace the opaque functions with the real ones (using autorewrite). *)

Module Type NOEXPAND.
  Parameter negb: bool -> bool.
  Parameter add: N -> N -> N.
  Parameter sub: N -> N -> N.
  Parameter mul: N -> N -> N.
  Parameter div: N -> N -> N.
  Parameter quot: Z -> Z -> Z.
  Parameter rem: Z -> Z -> Z.
  Parameter modulo: N -> N -> N.
  Parameter pow: N -> N -> N.
  Parameter shiftl: N -> N -> N.
  Parameter shiftr: N -> N -> N.
  Parameter ashiftr: bitwidth -> N -> N -> N.
  Parameter land: N -> N -> N.
  Parameter lor: N -> N -> N.
  Parameter lxor: N -> N -> N.
  Parameter lnot: N -> N -> N.
  Parameter eqb: N -> N -> bool.
  Parameter ltb: N -> N -> bool.
  Parameter leb: N -> N -> bool.
  Parameter slt: N -> N -> N -> bool.
  Parameter sle: N -> N -> N -> bool.
  Parameter sbop: (Z -> Z -> Z) -> bitwidth -> N -> N -> N.
  Parameter scast: bitwidth -> bitwidth -> N -> N.
  Parameter Niter: N -> forall {A}, (A -> A) -> A -> A.
  Parameter zstore: addr -> N.
  Parameter _vtyp: option value -> bool.
  Parameter _vnum: option value -> N.
  Parameter _vmem: option value -> addr -> N.
  Parameter _vwidth: option value -> N.

  Axiom negb_eq: negb = Coq.Init.Datatypes.negb.
  Axiom add_eq: add = N.add.
  Axiom sub_eq: sub = N.sub.
  Axiom mul_eq: mul = N.mul.
  Axiom div_eq: div = N.div.
  Axiom quot_eq: quot = Z.quot.
  Axiom rem_eq: rem = Z.rem.
  Axiom modulo_eq: modulo = N.modulo.
  Axiom pow_eq: pow = N.pow.
  Axiom shiftl_eq: shiftl = N.shiftl.
  Axiom shiftr_eq: shiftr = N.shiftr.
  Axiom ashiftr_eq: ashiftr = Picinae_core.ashiftr.
  Axiom land_eq: land = N.land.
  Axiom lor_eq: lor = N.lor.
  Axiom lxor_eq: lxor = N.lxor.
  Axiom lnot_eq: lnot = N.lnot.
  Axiom eqb_eq: eqb = N.eqb.
  Axiom ltb_eq: ltb = N.ltb.
  Axiom leb_eq: leb = N.leb.
  Axiom slt_eq: slt = Picinae_core.slt.
  Axiom sle_eq: sle = Picinae_core.sle.
  Axiom sbop_eq: sbop = Picinae_core.sbop.
  Axiom scast_eq: scast = Picinae_core.scast.
  Axiom Niter_eq: Niter = N.iter.
  Axiom vtyp_eq: _vtyp = vtyp.
  Axiom vnum_eq: _vnum = vnum.
  Axiom vmem_eq: _vmem = vmem.
  Axiom vwidth_eq: _vwidth = vwidth.
End NOEXPAND.

Module NoE : NOEXPAND.
  Definition negb := negb.
  Definition add := N.add.
  Definition sub := N.sub.
  Definition mul := N.mul.
  Definition div := N.div.
  Definition quot := Z.quot.
  Definition rem := Z.rem.
  Definition modulo := N.modulo.
  Definition pow := N.pow.
  Definition shiftl := N.shiftl.
  Definition shiftr := N.shiftr.
  Definition ashiftr := ashiftr.
  Definition land := N.land.
  Definition lor := N.lor.
  Definition lxor := N.lxor.
  Definition lnot := N.lnot.
  Definition eqb := N.eqb.
  Definition ltb := N.ltb.
  Definition leb := N.leb.
  Definition slt := slt.
  Definition sle := sle.
  Definition sbop := sbop.
  Definition scast := scast.
  Definition Niter := N.iter.
  Definition zstore (_:addr) := 0.
  Definition _vtyp := vtyp.
  Definition _vnum := vnum.
  Definition _vmem := vmem.
  Definition _vwidth := vwidth.

  Theorem negb_eq: negb = Coq.Init.Datatypes.negb. Proof eq_refl.
  Theorem add_eq: add = N.add. Proof eq_refl.
  Theorem sub_eq: sub = N.sub. Proof eq_refl.
  Theorem mul_eq: mul = N.mul. Proof eq_refl.
  Theorem div_eq: div = N.div. Proof eq_refl.
  Theorem quot_eq: quot = Z.quot. Proof eq_refl.
  Theorem rem_eq: rem = Z.rem. Proof eq_refl.
  Theorem modulo_eq: modulo = N.modulo. Proof eq_refl.
  Theorem pow_eq: pow = N.pow. Proof eq_refl.
  Theorem shiftl_eq: shiftl = N.shiftl. Proof eq_refl.
  Theorem shiftr_eq: shiftr = N.shiftr. Proof eq_refl.
  Theorem ashiftr_eq: ashiftr = Picinae_core.ashiftr. Proof eq_refl.
  Theorem land_eq: land = N.land. Proof eq_refl.
  Theorem lor_eq: lor = N.lor. Proof eq_refl.
  Theorem lxor_eq: lxor = N.lxor. Proof eq_refl.
  Theorem lnot_eq: lnot = N.lnot. Proof eq_refl.
  Theorem eqb_eq: eqb = N.eqb. Proof eq_refl.
  Theorem ltb_eq: ltb = N.ltb. Proof eq_refl.
  Theorem leb_eq: leb = N.leb. Proof eq_refl.
  Theorem slt_eq: slt = Picinae_core.slt. Proof eq_refl.
  Theorem sle_eq: sle = Picinae_core.sle. Proof eq_refl.
  Theorem sbop_eq: sbop = Picinae_core.sbop. Proof eq_refl.
  Theorem scast_eq: scast = Picinae_core.scast. Proof eq_refl.
  Theorem Niter_eq: Niter = N.iter. Proof eq_refl.
  Theorem vtyp_eq: _vtyp = vtyp. Proof eq_refl.
  Theorem vnum_eq: _vnum = vnum. Proof eq_refl.
  Theorem vmem_eq: _vmem = vmem. Proof eq_refl.
  Theorem vwidth_eq: _vwidth = vwidth. Proof eq_refl.
End NoE.

Create HintDb feval discriminated.
Global Hint Rewrite NoE.negb_eq : feval.
Global Hint Rewrite NoE.add_eq : feval.
Global Hint Rewrite NoE.sub_eq : feval.
Global Hint Rewrite NoE.mul_eq : feval.
Global Hint Rewrite NoE.div_eq : feval.
Global Hint Rewrite NoE.quot_eq : feval.
Global Hint Rewrite NoE.rem_eq : feval.
Global Hint Rewrite NoE.modulo_eq : feval.
Global Hint Rewrite NoE.pow_eq : feval.
Global Hint Rewrite NoE.shiftl_eq : feval.
Global Hint Rewrite NoE.shiftr_eq : feval.
Global Hint Rewrite NoE.ashiftr_eq : feval.
Global Hint Rewrite NoE.land_eq : feval.
Global Hint Rewrite NoE.lor_eq : feval.
Global Hint Rewrite NoE.lxor_eq : feval.
Global Hint Rewrite NoE.lnot_eq : feval.
Global Hint Rewrite NoE.eqb_eq : feval.
Global Hint Rewrite NoE.ltb_eq : feval.
Global Hint Rewrite NoE.leb_eq : feval.
Global Hint Rewrite NoE.slt_eq : feval.
Global Hint Rewrite NoE.sle_eq : feval.
Global Hint Rewrite NoE.sbop_eq : feval.
Global Hint Rewrite NoE.scast_eq : feval.
Global Hint Rewrite NoE.Niter_eq : feval.
Global Hint Rewrite NoE.vtyp_eq : feval.
Global Hint Rewrite NoE.vnum_eq : feval.
Global Hint Rewrite NoE.vmem_eq : feval.
Global Hint Rewrite NoE.vwidth_eq : feval.
Global Hint Rewrite vtyp_num : feval.
Global Hint Rewrite vtyp_mem : feval.
Global Hint Rewrite vnum_num : feval.
Global Hint Rewrite vmem_mem : feval.
Global Hint Rewrite vwidth_num : feval.
Global Hint Rewrite vwidth_mem : feval.
Global Hint Rewrite fold_vget : feval.


(* Functionally evaluate binary and unary operations using the opaque
   functions above. *)

Definition of_uvalue (u:uvalue) :=
  match u with VaU z m n w => if z then VaN n w else VaM m w end.

Definition utowidth (w n:N) : uvalue :=
  VaU true NoE.zstore (NoE.modulo n (NoE.pow 2 w)) w.

Definition utobit (b:bool) : uvalue :=
  VaU true NoE.zstore (if b then 1 else 0) 1.

Definition feval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : uvalue :=
  match bop with
  | OP_PLUS => utowidth w (NoE.add n1 n2)
  | OP_MINUS => utowidth w (NoE.sub (NoE.add (NoE.pow 2 w) n1) n2)
  | OP_TIMES => utowidth w (NoE.mul n1 n2)
  | OP_DIVIDE => VaU true NoE.zstore (NoE.div n1 n2) w
  | OP_SDIVIDE => VaU true NoE.zstore (NoE.sbop NoE.quot w n1 n2) w
  | OP_MOD => VaU true NoE.zstore (NoE.modulo n1 n2) w
  | OP_SMOD => VaU true NoE.zstore (NoE.sbop NoE.rem w n1 n2) w
  | OP_LSHIFT => utowidth w (NoE.shiftl n1 n2)
  | OP_RSHIFT => VaU true NoE.zstore (NoE.shiftr n1 n2) w
  | OP_ARSHIFT => VaU true NoE.zstore (NoE.ashiftr w n1 n2) w
  | OP_AND => VaU true NoE.zstore (NoE.land n1 n2) w
  | OP_OR => VaU true NoE.zstore (NoE.lor n1 n2) w
  | OP_XOR => VaU true NoE.zstore (NoE.lxor n1 n2) w
  | OP_EQ => utobit (NoE.eqb n1 n2)
  | OP_NEQ => utobit (NoE.negb (NoE.eqb n1 n2))
  | OP_LT => utobit (NoE.ltb n1 n2)
  | OP_LE => utobit (NoE.leb n1 n2)
  | OP_SLT => utobit (NoE.slt w n1 n2)
  | OP_SLE => utobit (NoE.sle w n1 n2)
  end.

Definition feval_unop (uop:unop_typ) (n:N) (w:bitwidth) : uvalue :=
  match uop with
  | OP_NEG => utowidth w (NoE.sub (NoE.pow 2 w) n)
  | OP_NOT => VaU true NoE.zstore (NoE.lnot n w) w
  end.

Definition feval_cast (c:cast_typ) (w w':bitwidth) (n:N) : N :=
  match c with
  | CAST_UNSIGNED => n
  | CAST_SIGNED => NoE.scast w w' n
  | CAST_HIGH => NoE.shiftr n (w - w')
  | CAST_LOW => NoE.modulo n (NoE.pow 2 w')
  end.


(* Functional interpretation of expressions and statements requires instantiating
   a functor that accepts the architecture-specific IL syntax and semantics. *)

Module Type PICINAE_FINTERP (IL: PICINAE_IL).

Import IL.
Module PTheory := PicinaeTheory IL.
Import PTheory.

Definition vupdate := @Picinae_core.update var (option value) VarEqDec.

(* Memory access propositions resulting from functional interpretation are
   encoded as (MemAcc (mem_readable|mem_writable) heap store addr length). *)
Definition MemAcc (P: store -> addr -> Prop) h s a len :=
  forall n, n < len -> h (a+n) = Some tt /\ P s (a+n).

Module Type NOEMEM.
  Parameter getmem: endianness -> bitwidth -> (addr -> N) -> addr -> N.
  Parameter setmem: endianness -> bitwidth -> (addr -> N) -> addr -> N -> addr -> N.
  Parameter vupdate: store -> var -> option value -> store.
  Parameter memaccr: hdomain -> store -> N -> N -> Prop.
  Parameter memaccw: hdomain -> store -> N -> N -> Prop.
  Axiom getmem_eq: getmem = IL.getmem.
  Axiom setmem_eq: setmem = IL.setmem.
  Axiom vupdate_eq: vupdate = @Picinae_core.update var (option value) VarEqDec.
  Axiom memaccr_eq: memaccr = MemAcc mem_readable.
  Axiom memaccw_eq: memaccw = MemAcc mem_writable.
End NOEMEM.

Module NoEMem : NOEMEM.
  Definition getmem := IL.getmem.
  Definition setmem := IL.setmem.
  Definition vupdate := @update var (option value) VarEqDec.
  Definition memaccr := MemAcc mem_readable.
  Definition memaccw := MemAcc mem_writable.
  Theorem getmem_eq: getmem = IL.getmem. Proof eq_refl.
  Theorem setmem_eq: setmem = IL.setmem. Proof eq_refl.
  Theorem vupdate_eq: vupdate = PICINAE_FINTERP.vupdate. Proof eq_refl.
  Theorem memaccr_eq: memaccr = MemAcc mem_readable. Proof eq_refl.
  Theorem memaccw_eq: memaccw = MemAcc mem_writable. Proof eq_refl.
End NoEMem.

Global Hint Rewrite NoEMem.getmem_eq : feval.
Global Hint Rewrite NoEMem.setmem_eq : feval.
Global Hint Rewrite NoEMem.vupdate_eq : feval.
Global Hint Rewrite NoEMem.memaccr_eq : feval.
Global Hint Rewrite NoEMem.memaccw_eq : feval.

Definition bits_of_mem len := N.mul Mb len.

(* Functionally evaluate an expression.  Parameter unk is an oracle function
   that returns values of unknown expressions. *)
Fixpoint feval_exp e h s unk :=
  match e with
  | Var v => (VaU (NoE._vtyp (s vupdate v))
                  (NoE._vmem (s vupdate v))
                  (NoE._vnum (s vupdate v))
                  (NoE._vwidth (s vupdate v)), nil)
  | Word n w => (VaU true NoE.zstore n w, nil)
  | Load e1 e2 en len =>
      match feval_exp e1 h s (unknowns0 unk), feval_exp e2 h s (unknowns1 unk) with
      | (VaU _ m _ _, ma1), (VaU _ _ n _, ma2) =>
        (VaU true NoE.zstore (NoEMem.getmem en len m n) (bits_of_mem len),
         NoEMem.memaccr h (s NoEMem.vupdate) n len :: ma1++ma2)
      end
  | Store e1 e2 e3 en len =>
      match feval_exp e1 h s (unknowns00 unk), feval_exp e2 h s (unknowns01 unk), feval_exp e3 h s (unknowns10 unk) with
      | (VaU _ m _ mw, ma1), (VaU _ _ a _, ma2), (VaU _ _ v _, ma3) =>
        (VaU false (NoEMem.setmem en len m a v) 0 mw,
         NoEMem.memaccw h (s NoEMem.vupdate) a len :: ma1++ma2++ma3)
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
        (VaU true NoE.zstore (feval_cast c w w' n) w', ma)
      end
  | Let v e1 e2 =>
      match feval_exp e1 h s (unknowns0 unk) with (u,ma1) =>
        match feval_exp e2 h (fun upd => upd (s upd) v (Some (of_uvalue u))) (unknowns1 unk) with
        | (u',ma2) => (u', ma1++ma2)
        end
      end
  | Unknown w => (VaU true NoE.zstore (NoE.modulo (unk xH) (NoE.pow 2 w)) w, nil)
  | Ite e1 e2 e3 =>
      match feval_exp e1 h s (unknowns0 unk), feval_exp e2 h s (unknowns1 unk), feval_exp e3 h s (unknowns1 unk) with
      | (VaU _ _ n1 _, ma1), (VaU b2 m2 n2 w2, ma2), (VaU b3 m3 n3 w3, ma3) =>
        (VaU (if n1 then b3 else b2) (if n1 then m3 else m2) (if n1 then n3 else n2) (if n1 then w3 else w2),
         match ma2,ma3 with nil,nil => ma1 | _,_ => ma1++(if n1 then conjall ma3 else conjall ma2)::nil end)
      end
  | Extract n1 n2 e1 =>
      match feval_exp e1 h s unk with
      | (VaU _ _ n w, ma) => (VaU true NoE.zstore (feval_cast CAST_HIGH (N.succ n1) (N.succ (n1-n2))
                                                  (feval_cast CAST_LOW w (N.succ n1) n)) (N.succ (n1-n2)), ma)
      end
  | Concat e1 e2 =>
      match feval_exp e1 h s (unknowns0 unk), feval_exp e2 h s (unknowns1 unk) with
      | (VaU _ _ n1 w1, ma1), (VaU _ _ n2 w2, ma2) =>
        (VaU true NoE.zstore (NoE.lor (NoE.shiftl n1 w2) n2) (w1+w2), ma1++ma2)
      end
  end.


(* Convert a list of variables and their values to a store function. *)
Fixpoint updlst s (l: list (var * option value)) upd : store :=
  match l with nil => s | (v,u)::t => upd (updlst s t upd) v u end.

(* Remove a variable from a list of variables and their values. *)
Fixpoint remlst v l : list (var * option value) :=
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
| FIS (l: list (var * option value)) (xq: finterp_cont) (ma: list Prop).

Fixpoint fexec_stmt q h s unk l :=
  match q with
  | Nop => FIS l (FIExit None) nil
  | Move v e => match feval_exp e h (updlst s l) unk with
                | (u,ma) => FIS ((v, Some (of_uvalue u))::remlst v l) (FIExit None) ma
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
        FIS l (FIStmt (NoE.Niter n (Seq q1) Nop)) ma0
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
    simpl. rewrite SV. autorewrite with feval. destruct u; reflexivity.
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
  autorewrite with feval. split.
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
  autorewrite with feval. split.
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
    destruct b; simpl; autorewrite with feval; reflexivity.
    apply conjallT_app; assumption.

  (* UnOp *)
  apply IHe in E1. clear IHe.
  destruct E1 as [unk1 E1].
  exists unk1.
  unfold feval_exp; fold feval_exp.
  destruct (feval_exp e _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  split.
    destruct u; simpl; autorewrite with feval; reflexivity.
    assumption.

  (* Cast *)
  apply IHe in E1. clear IHe.
  destruct E1 as [unk1 E1].
  exists unk1.
  unfold feval_exp; fold feval_exp.
  destruct (feval_exp e _ _ _) as (u1,ma1). destruct u1. destruct E1 as [U1 M1].
  simpl in U1. destruct z; try discriminate. injection U1; intros; subst.
  split.
    destruct c; simpl; autorewrite with feval; reflexivity.
    assumption.

  (* Let *)
  change (s vupdate [v:=Some u1]) with ((fun upd => upd (s upd) v (Some u1)) vupdate) in E2.
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
  simpl. autorewrite with feval. split.
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
    simpl. autorewrite with feval. reflexivity.
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
    simpl. autorewrite with feval. reflexivity.
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
              | FIS l' (FIExit x') ma => (s' = updlst s l' NoEMem.vupdate /\ x = x') /\ conjallT ma
              | FIS l' (FIStmt q') ma => exec_stmt h (updlst s l' NoEMem.vupdate) q' s' x /\ conjallT ma
              end.
Proof.
  rewrite NoEMem.vupdate_eq.
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
  rewrite NoE.Niter_eq. split; assumption.
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
   by the user (e.g., using "simpl") if desired.  Call-by-value strategy is
   used here, since our goal is usually to reduce as much as possible of the
   target expression, which might include arguments of an enclosing unexpandable
   function. *)

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
  repeat first [ rewrite update_updated in H | rewrite update_frame in H; [|discriminate 1] ];
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
   "s[var:=value]" to the expression. *)

Ltac stock_store :=
  lazymatch goal with |- exec_stmt _ _ ?Q _ _ => repeat
    match Q with context [ Var ?V ] =>
      lazymatch goal with |- exec_stmt _ ?S _ _ _ =>
        lazymatch S with context [ update _ V _ ] => fail | _ =>
          erewrite (store_upd_eq S V) by (simpl_stores; eassumption)
        end
      end
    end
  | _ => fail "Goal is not of the form (exec_stmt ...)"
  end.

Tactic Notation "stock_store" "in" hyp(XS) :=
  lazymatch type of XS with exec_stmt _ _ ?Q _ _ => repeat
    match Q with context [ Var ?V ] =>
      lazymatch type of XS with exec_stmt _ ?S _ _ _ =>
        lazymatch S with context [ update _ V _ ] => fail | _ =>
          erewrite (store_upd_eq S V) in XS by (simpl_stores; eassumption)
        end
      end
    end
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.


(* To prevent vm_compute from expanding symbolic expressions that the user
   already has in a desired form, the following lemmas introduce symbolic
   constants for those expressions that are set equal to the original terms.
   The "destruct" tactic can then be used to separate those terms out into
   a different hypothesis to which vm_compute is not applied, and then
   use "subst" to substitute them back into the evaluated term after vm_compute
   is done. *)

Lemma fexec_stmt_init:
  forall h s q s' x (XS: exec_stmt h s q s' x),
  exec_stmt h (updlst s (rev nil) vupdate) q s' x /\ True.
Proof. split. assumption. exact I. Qed.

Lemma fexec_stmt_updn:
  forall h s v n w l q s' x EQs,
  exec_stmt h (updlst (vupdate s v (Some (VaN n w))) (rev l) vupdate) q s' x /\ EQs ->
  exists a, exec_stmt h (updlst s (rev ((v, Some (VaN a w))::l)) vupdate) q s' x /\ (a=n /\ EQs).
Proof.
  intros. exists n. split.
    rewrite <- update_updlst. apply H.
    split. reflexivity. apply H.
Qed.

Lemma fexec_stmt_updm:
  forall h s v m w l q s' x EQs,
  exec_stmt h (updlst (vupdate s v (Some (VaM m w))) (rev l) vupdate) q s' x /\ EQs ->
  exists a, exec_stmt h (updlst s (rev ((v, Some (VaM a w))::l)) vupdate) q s' x /\ (a=m /\ EQs).
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


(* Finally, simplifying a hypothesis H of the form (exec_stmt ...) entails first
   removing any user-supplied expressions in H that we don't want expanded, then
   applying the reduce_stmt theorem to convert it into an fexec_stmt expression,
   launching vm_compute on it, then abstracting any unknowns as unique proof
   context variables, and finally substituting any removed or opaque expressions
   back in to the evaluated expression. *)

Ltac step_stmt XS :=
  lazymatch type of XS with exec_stmt ?h _ _ ?s' ?x =>
    apply fexec_stmt_init in XS;
    repeat first [ apply fexec_stmt_updn in XS; let _n := fresh "_n" in destruct XS as [_n XS]
                 | apply fexec_stmt_updm in XS; let _m := fresh "_m" in destruct XS as [_m XS]
                 | apply fexec_stmt_updu in XS; let _u := fresh "_u" in destruct XS as [_u XS] ];
    let EQs := fresh in (
      destruct XS as [XS EQs];
      let _h := fresh "_h" in let _s := fresh "_s" in let _s' := fresh "_s'" in let _x := fresh "_x" in (
        lazymatch type of XS with exec_stmt _ (updlst ?s _ _) _ _ _ =>
          remember h as _h; remember s as _s; remember s' as _s'; remember x as _x
        end;
        apply reduce_stmt in XS; let unk := fresh "unknown" in (
          destruct XS as [unk XS];
          vm_compute in XS;
          revert XS; repeat lazymatch goal with |- context [ unk ?i ] =>
            generalize (unk i); let u := fresh "u" in intro u
          end; intro XS; try clear unk
        );
        autorewrite with feval in XS;
        subst _h _s _s' _x
      );
      repeat lazymatch type of EQs with (?_nmu = _) /\ _ =>
        let H1 := fresh in destruct EQs as [H1 EQs]; subst _nmu
      end;
      clear EQs
    )
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.


(* We can then break the memory access part of XS resulting from step_stmt into
   separate hypotheses.  This is provided as a separate tactic because often
   the user may want to perform some sort of simplification before splitting. *)

Ltac destruct_memaccs XS :=
  let ACCs := fresh "ACCs" in
    destruct XS as [XS ACCs];
    repeat lazymatch type of ACCs with ?H1 /\ _ =>
      lazymatch goal with [ H0:H1 |- _ ] => apply proj2 in ACCs
      | _ => let ACC := fresh "ACC" in destruct ACCs as [ACC ACCs]
      end
    | True => clear ACCs
    end.

End PICINAE_FINTERP.


Module PicinaeFInterp (IL: PICINAE_IL) <: PICINAE_FINTERP IL.
  Include PICINAE_FINTERP IL.
End PicinaeFInterp.

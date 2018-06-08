(* BIL Interpreter for Binary Analysis Platform (BAP)
 *
 * Copyright (c) 2018 Kevin W. Hamlen
 * Computer Science Department
 * The University of Texas at Dallas
 *
 * Any use, commercial or otherwise, requires the express permission of
 * the author.
 *
 * To compile this module, first load the BapSyntax module and compile
 * it with menu option Compile->Compile buffer.
 *)

Require Export BapSyntax.
Require Import ZArith.
Require Import NArith.
Require Import Structures.Equalities.
Require Import Program.Equality.
Require Import FunctionalExtensionality.
Require Setoid.


(* The interpreter module takes a machine architecture as input, expressed as
   a module that defines a type for IL variables along with the bitwidth of
   memory contents (usually 8 for bytes).  The bitwidth can be any nonzero N. *)
Module Type Architecture.
  Declare Module Var : UsualDecidableType.
  Parameter Mb : N.
  Axiom Mb_nonzero : Mb <> N0.
End Architecture.



Module BAPInterp (Arch : Architecture).

Export Arch.
Module Syntax := BAPSyntax Var.
Export Syntax.
Open Scope N.

(* Different machine architectures use different datatypes to represent
   variable identifiers at the IL level.  The representation can be almost
   anything, but the interpreter at least needs a way to decide whether
   arbitrary variable instances denote the same variable.  To facilitate this,
   we use Coq's UsualDecidableType module from Structures.Equalities. *)
Definition vareq := Var.eq_dec.

(* Runtime values are integers or memory states. *)
Inductive value : Type :=
| VaN (n:word)
| VaM (m:addr->N) (w:bitwidth).

(* Memory is well-typed if every address holds a byte. *)
Definition welltyped_memory (m:addr->N) : Prop :=
  forall a, m a < 2^Mb.

(* A constant's type is its bitwidth, and a memory's type is the
   bitwidth of its addresses. *)
Inductive typof_val: value -> typ -> Prop :=
| TVN (n:N) (w:bitwidth) (LT: n < 2^w): typof_val (VaN (n,w)) (NumT w)
| TVM (m:addr->N) (w:bitwidth) (WTM: welltyped_memory m): typof_val (VaM m w) (MemT w).

(* A store is a partial function from variables to values. *)
Definition store := varid -> option value.

(* Reinterpret an unsigned integer as a 2's complement signed integer. *)
Definition of_twoscomp (i:word) : Z :=
  match i with (_,N0) => Z0 | (n,Npos w) =>
    if (2^(Pos.pred_N w)) <=? n then Z.sub (Z.of_N n) (Z.of_N (2^Npos w)) else Z.of_N n
  end.

(* Convert an integer back to 2's complement form. *)
Definition to_twoscomp (z:Z) (w:N) : N :=
  match z with Z0 => N0
             | Z.pos p => Npos p
             | Z.neg p => 2^w - Npos p
  end.

(* Perform a signed operation by converting the unsigned operands to signed
   operands, applying the signed operation, and then converting the signed
   result back to unsigned. *)
Definition signed_op (op:Z->Z->Z) (w n1 n2:N) : N :=
  to_twoscomp (op (of_twoscomp (n1,w)) (of_twoscomp (n2,w))) w.

(* Compute an arithmetic shift-right (sign-extending shift-right). *)
Definition ashiftr (w n1 n2:N) : N :=
  match w with N0 => n1 | Npos sb =>
    if N.testbit n1 (Pos.pred_N sb) then
      N.shiftr (N.lor (N.shiftl (N.ones n2) w) n1) n2
    else N.shiftr n1 n2
  end.

(* Force a result to a given width by dropping the high bits. *)
Definition towidth (w n:N) : value :=
  VaN (N.modulo n (2^w), w).
Global Arguments towidth / w n.

(* Force a result to a boolean value (1-bit integer). *)
Definition tobit (b:bool) : value :=
  VaN (N.b2n b, 1).
Global Arguments tobit / b.

(* Perform signed less-than comparison. *)
Definition signed_lt (w n1 n2:N) : bool :=
  Z.ltb (of_twoscomp (n1,w)) (of_twoscomp (n2,w)).

(* Perform signed less-or-equal comparison. *)
Definition signed_le (w n1 n2:N) : bool :=
  Z.leb (of_twoscomp (n1,w)) (of_twoscomp (n2,w)).

(* Perform a binary operation (using the above as helper functions). *)
Definition eval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : value :=
  match bop with
  | OP_PLUS => towidth w (n1+n2)
  | OP_MINUS => towidth w (2^w + n1 - n2)
  | OP_TIMES => towidth w (n1*n2)
  | OP_DIVIDE => VaN (n1/n2, w)
  | OP_SDIVIDE => towidth w (signed_op Z.quot w n1 n2) (* need towidth since -2^w/-1 >= 2^w *)
  | OP_MOD => VaN (N.modulo n1 n2, w)
  | OP_SMOD => VaN (signed_op Z.rem w n1 n2, w)
  | OP_LSHIFT => towidth w (N.shiftl n1 n2)
  | OP_RSHIFT => VaN (N.shiftr n1 n2, w)
  | OP_ARSHIFT => VaN (ashiftr w n1 n2, w)
  | OP_AND => VaN (N.land n1 n2, w)
  | OP_OR => VaN (N.lor n1 n2, w)
  | OP_XOR => VaN (N.lxor n1 n2, w)
  | OP_EQ => tobit (n1 =? n2)
  | OP_NEQ => tobit (negb (n1 =? n2))
  | OP_LT => tobit (n1 <? n2)
  | OP_LE => tobit (n1 <=? n2)
  | OP_SLT => tobit (signed_lt w n1 n2)
  | OP_SLE => tobit (signed_le w n1 n2)
  end.

(* Perform a unary operation. *)
Definition eval_unop (uop:unop_typ) (n:N) (w:bitwidth) : value :=
  match uop with
  | OP_NEG => VaN (match n with N0 => N0 | _ => 2^w - n end, w)
  | OP_NOT => VaN (N.lnot n w, w)
  end.

(* Return a new store that is like store f except with variable x
   remapped to value y. *)
Definition update {A B:Type} (eq:forall (a b:A), {a=b}+{a<>b}) (f:A->B) (x:A) (y:B) (z:A) : B :=
  if eq z x then y else f z.

Notation "f [ x := y ]" := (update vareq f x y) (at level 50, left associativity).


(* Perform a cast operation. *)
Definition signed_cast (p:positive) (w':bitwidth) (n:N) : N :=
  if N.testbit n (Pos.pred_N p) then N.lor (N.shiftl (N.ones (w'-Npos p)) (Npos p)) n else n.

Definition cast (c:cast_typ) (w w':bitwidth) (n:N) : N :=
  match c with
  | CAST_UNSIGNED => n
  | CAST_SIGNED => match w with N0 => N0 | Npos p => signed_cast p w' n end
  | CAST_HIGH => N.shiftr n (w-w')
  | CAST_LOW => N.modulo n (2^w')
  end.

(* We next define memory accessor functions getmem and setmem, which read/store w-bit numbers
   to/from memory.  Since w could be large on some architectures, we express both as recursions
   over N, using Peano recursion (P w -> P (N.succ w)).  Proofs must therefore typically use
   the N.peano_ind inductive principle to reason about them.  (We later provide some machinery
   for doing so.)  These functions are also carefully defined to behave reasonably when the
   value being read/stored is not well-typed (i.e., larger than 2^w).  In particular, the extra
   bits are stored into the most significant byte (violating memory well-typedness), except
   that when w=0, the value argument is ignored and 0 is returned/stored.  This behavior is
   useful because it facilitates theorems whose correctness are independent of type-safety. *)

(* Interpret len bytes at address a of memory m as an e-endian number. *)
Definition getmem_big mem len rec a := N.lor (rec (N.succ a)) (N.shiftl (mem a) (Mb*len)).
Definition getmem_little mem (len:bitwidth) rec a := N.lor (mem a) (N.shiftl (rec (N.succ a)) Mb).
Definition getmem (e:endianness) (w:bitwidth) (mem:addr->N) : addr -> N :=
  N.recursion (fun _ => N0) (match e with BigE => getmem_big | LittleE => getmem_little end mem) (w/Mb).

(* Store v as a len-byte, e-endian number at address a of memory m. *)
Definition setmem_big len rec mem a v : addr -> N :=
  rec (update N.eq_dec mem a (N.shiftr v (Mb*len))) (N.succ a) (v mod 2^(Mb*len)).
Definition setmem_little len rec mem a v : addr -> N :=
  rec (update N.eq_dec mem a (match len with N0 => v | Npos _ => v mod 2^Mb end)) (N.succ a) (N.shiftr v Mb).
Definition setmem (e:endianness) (w:bitwidth) : (addr->N) -> addr -> N -> (addr -> N) :=
  N.recursion (fun m _ _ => m) (match e with BigE => setmem_big | LittleE => setmem_little end) (w/Mb).



(* A program exits by hitting a computation limit (Unfinished), jumping to an address
   outside the program (Exit), or throwing an exception (Exn). *)
Inductive exit : Type := Unfinished | Exit (a:addr) | Exn (i:N).

Section InterpreterEngine.

(* User-defined proposition "accessible b m w a" specifies whether address a
   of memory m (where addresses of m have width w) is readable (if b=false)
   or writable (if b=true) on whatever architecture is being modeled.  If
   input a is greater than or equal to memory limit 2^w, then this function
   should return False (neither readable nor writable).  This can happen if a
   memory access request spans the limit imposed by the address bitwidth.
   For example, the following expression is considered well-typed by our
   static semantics, but accesses memory out of bounds at runtime:
       Load mem (Int (2^32-1, 32)) endianness (Int (16, w))
   where mem is a memory operand with 32-bit addresses.  Here, address 2^32-1
   is a legitimate 32-bit integer operand, but the request for 16 bits of
   memory effectively also accesses address 2^32, which is not representable
   as a 32-bit number.  Since the width argument to Load and Store cannot be
   statically predicted, type-checking cannot statically preclude this. *)
Definition acctyp := bool -> (addr->N) -> bitwidth -> addr -> Prop.
Variable accessible : acctyp.

(* Evaluate an expression in the context of a store, returning a value.  Note
   that the semantics of EUnknown are non-deterministic: an EUnknown expression
   evaluates to any well-typed value.  Thus, eval_exp and the other interpreter
   semantic definitions that follow should be considered statements of
   possibility in an alethic modal logic. *)
Inductive eval_exp (s:store): exp -> value -> Prop :=
| EVar (id:varid) (t:typ) (u:value) (SV: s id = Some u):
       eval_exp s (Var (Va id t)) u
| EImm (n:N) (w:bitwidth): eval_exp s (Word (n,w)) (VaN (n,w))
| ELoad (e1 e2:exp) (en:endianness) (w' mw:bitwidth) (m:addr->N) (a:addr)
        (E1: eval_exp s e1 (VaM m mw)) (E2: eval_exp s e2 (VaN (a,mw)))
        (R: forall n, n < w'/Mb -> accessible false m mw (a+n)):
        eval_exp s (Load e1 e2 en w') (VaN (getmem en w' m a, w'))
| EStore (e1 e2 e3:exp) (en:endianness) (w mw:bitwidth) (m:addr->N) (a:addr)
         (v:N) (E1: eval_exp s e1 (VaM m mw))
         (E2: eval_exp s e2 (VaN (a,mw))) (E3: eval_exp s e3 (VaN (v, w)))
         (W: forall n, n < w/Mb -> accessible true m mw (a+n)):
         eval_exp s (Store e1 e2 e3 en w) (VaM (setmem en w m a v) mw)
| EBinOp (bop:binop_typ) (e1 e2:exp) (n1 n2:N) (w:bitwidth)
         (E1: eval_exp s e1 (VaN (n1,w))) (E2: eval_exp s e2 (VaN (n2,w))):
         eval_exp s (BinOp bop e1 e2) (eval_binop bop w n1 n2)
| EUnOp (uop:unop_typ) (e1:exp) (n1:N) (w1:bitwidth)
        (E1: eval_exp s e1 (VaN (n1,w1))):
        eval_exp s (UnOp uop e1) (eval_unop uop n1 w1)
| ECast (c:cast_typ) (w w':bitwidth) (e1:exp) (n:N)
        (E1: eval_exp s e1 (VaN (n,w))):
        eval_exp s (Cast c w' e1) (VaN (cast c w w' n, w'))
| ELet (id:varid) (t:typ) (e1 e2:exp) (u1 u2:value)
       (E1: eval_exp s e1 u1) (E2: eval_exp (update vareq s id (Some u1)) e2 u2):
       eval_exp s (Let (Va id t) e1 e2) u2
| EUnknown (t:typ) (u:value)
           (TV: typof_val u t):
           eval_exp s (Unknown t) u
| EIte (e1 e2 e3:exp) (n1:N) (w1:bitwidth) (u':value)
       (E1: eval_exp s e1 (VaN (n1,w1)))
       (E': eval_exp s (match n1 with N0 => e3 | _ => e2 end) u'):
       eval_exp s (Ite e1 e2 e3) u'
| EExtract (w n1 n2:bitwidth) (e1:exp) (n:N)
           (E1: eval_exp s e1 (VaN (n,w))):
           eval_exp s (Extract n1 n2 e1) (VaN (cast CAST_HIGH (N.succ n1) (N.succ (n1-n2))
                                                 (cast CAST_LOW w (N.succ n1) n), N.succ (n1-n2)))
| EConcat (e1 e2:exp) (n1 w1 n2 w2:N)
          (E1: eval_exp s e1 (VaN (n1,w1))) (E2: eval_exp s e2 (VaN (n2,w2))):
          eval_exp s (Concat e1 e2) (VaN (N.land (N.shiftl n1 w2) n2, w1+w2)).

(* Execute an IL statement with recursion depth limit n, returning a new store
   and possibly an exit (if the statement exited prematurely).  "None" is
   returned if the statement finishes and falls through.  "Some Unfinished"
   is returned if the statement requires more than n steps of computation
   to complete. *)
Inductive exec_stmt (s:store): stmt -> nat -> store -> option exit -> Prop :=
| XZero q: exec_stmt s q O s (Some Unfinished)
| XNop n: exec_stmt s Nop (S n) s None
| XMove n id t e u (E: eval_exp s e u):
    exec_stmt s (Move (Va id t) e) (S n) (update vareq s id (Some u)) None
| XJmp n e a w (E: eval_exp s e (VaN (a,w))):
    exec_stmt s (Jmp e) (S n) s (Some (Exit a))
| XExn n i: exec_stmt s (CpuExn i) (S n) s (Some (Exn i))
| XSeq1 n q1 q2 s' x (XS: exec_stmt s q1 n s' (Some x)):
    exec_stmt s (Seq q1 q2) (S n) s' (Some x)
| XSeq2 n q1 q2 s2 s' x' (XS1: exec_stmt s q1 n s2 None) (XS1: exec_stmt s2 q2 n s' x'):
    exec_stmt s (Seq q1 q2) (S n) s' x'
| XWhile n e q s' x (XS: exec_stmt s (If e (Seq q (While e q)) Nop) n s' x):
    exec_stmt s (While e q) (S n) s' x
| XIf n e q1 q2 c s' x
      (E: eval_exp s e (VaN (c,1)))
      (XS: exec_stmt s (match c with N0 => q2 | _ => q1 end) n s' x):
    exec_stmt s (If e q1 q2) (S n) s' x.

(* Helper function to compute the address of the next assembly code
   instruction to execute: *)
Definition exitaddr (a:addr) (x:option exit) : option addr :=
  match x with None => Some a
             | Some (Exit a') => Some a'
             | _ => None
  end.

(* Execute exactly n machine instructions of a program p starting at address a,
   imposing a recursion depth limit of m for each instruction's encoding, and
   returning a store and exit condition.  Exit condition "Unfinished" means
   depth limit m was exceeded during execution of one of the instructions. *)
Inductive exec_prog (p:program) (a:addr) (s:store) (m:nat) : nat -> store -> exit -> Prop :=
| XPZero: exec_prog p a s m O s (Exit a)
| XPStep n sz q s2 x1 a' s' x' (LU: p a = Some (sz,q))
         (XS: exec_stmt s q m s2 x1) (EX: exitaddr (a+sz) x1 = Some a')
         (XP: exec_prog p a' s2 m n s' x'):
    exec_prog p a s m (S n) s' x'
| XPDone sz q s' x (LU: p a = Some (sz,q))
         (XS: exec_stmt s q m s' (Some x)) (EX: exitaddr (a+sz) (Some x) = None):
    exec_prog p a s m (S O) s' x.

End InterpreterEngine.



(* Everything after this point comprises a (machine-checked) theory of the
   interpreter semantics defined above. *)


Section PartialOrders.

(* This section proves some generally useful facts about the partial order
   consisting of A-to-B partial functions ordered by subset. *)

Definition po_subset {A B:Type} (f g: A -> option B) : Prop :=
  forall x y, f x = Some y -> g x = Some y.

Theorem po_subset_reflexive {A B}:
  forall (f:A->option B), po_subset f f.
Proof.
  unfold po_subset. intros. assumption.
Qed.

Theorem po_subset_antisymmetric {A B}:
  forall (f g:A->option B), po_subset f g -> po_subset g f ->
  f = g.
Proof.
  unfold po_subset. intros f g FG GF. extensionality v.
  specialize (FG v). specialize (GF v). destruct (f v) as [b|].
    symmetry. apply FG. reflexivity.
    destruct (g v). apply GF. reflexivity. reflexivity.
Qed.

Theorem po_subset_transitive {A B}:
  forall (f g h:A->option B), po_subset f g -> po_subset g h -> po_subset f h.
Proof.
  unfold po_subset. intros f g h FG GH x y FX. apply GH,FG. assumption.
Qed.

Theorem po_subset_contrapos {A B}:
  forall (f g: A -> option B) x, po_subset f g -> g x = None -> f x = None.
Proof.
  unfold po_subset. intros f g x SS H. specialize (SS x). destruct (f x).
    symmetry. rewrite <- H. apply SS. reflexivity.
    reflexivity.
Qed.

Theorem po_subset_update {A B} {eq: forall (a b:A), {a=b}+{a<>b}}:
  forall (f g: A -> option B) (SS: po_subset f g) (x:A) (y:option B),
  po_subset (update eq f x y) (update eq g x y).
Proof.
  intros. unfold update. intros z y' H. destruct (eq z x).
    assumption.
    apply SS. assumption. 
Qed.

Definition updateall {A B:Type} (f g: A -> option B) (x:A) : option B :=
  match g x with None => f x | Some y => Some y end.

Theorem updateall_subset {A B}:
  forall (f g: A->option B), po_subset f g -> updateall g f = g.
Proof.
  unfold po_subset,updateall. intros.
  apply functional_extensionality. intro x. specialize H with (x:=x). destruct (f x).
    symmetry. apply H. reflexivity.
    reflexivity.
Qed.

Theorem subset_updateall {A B}:
  forall (f g: A->option B), po_subset f (updateall g f).
Proof.
  unfold po_subset,updateall. intros. rewrite H. reflexivity.
Qed.

End PartialOrders.

Add Parametric Relation {A B:Type}: (A -> option B) po_subset
reflexivity proved by po_subset_reflexive
transitivity proved by po_subset_transitive
as poss.


(* Recursive quantification of sub-expressions and sub-statements: *)

Fixpoint exps_in_exp {T:Type} (C:T->T->T) (P:exp->T) (e:exp) : T :=
  match e with
  | Var _ | Word _ | Unknown _ => P e
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => C (P e) (exps_in_exp C P e1)
  | BinOp _ e1 e2 | Let _ e1 e2 | Concat e1 e2 | Load e1 e2 _ _ =>
      C (P e) (C (exps_in_exp C P e1) (exps_in_exp C P e2))
  | Ite e1 e2 e3 | Store e1 e2 e3 _ _ =>
      C (P e) (C (exps_in_exp C P e1) (C (exps_in_exp C P e2) (exps_in_exp C P e3)))
  end.

Fixpoint exps_in_stmt {T:Type} (C:T->T->T) (d:T) (P:exp->T) (q:stmt) : T :=
  match q with
  | Nop | CpuExn _ => d
  | Move _ e | Jmp e => exps_in_exp C P e
  | Seq q1 q2 => C (exps_in_stmt C d P q1) (exps_in_stmt C d P q2)
  | While e q0 => C (exps_in_exp C P e) (exps_in_stmt C d P q0)
  | If e q1 q2 => C (exps_in_exp C P e) (C (exps_in_stmt C d P q1) (exps_in_stmt C d P q2))
  end.

Fixpoint stmts_in_stmt {T:Type} (C:T->T->T) (P:stmt->T) (q:stmt) : T :=
  match q with
  | Nop | CpuExn _ | Move _ _ | Jmp _ => P q
  | While _ q0 => C (P q) (stmts_in_stmt C P q0)
  | Seq q1 q2 | If _ q1 q2 => C (P q) (C (stmts_in_stmt C P q1) (stmts_in_stmt C P q2))
  end.

Definition forall_exps_in_exp := exps_in_exp and.
Definition forall_exps_in_stmt := exps_in_stmt and True.
Definition exists_exp_in_exp := exps_in_exp or.
Definition exists_exp_in_stmt := exps_in_stmt or False.
Definition forall_stmts_in_stmt := stmts_in_stmt and.
Definition exists_stmt_in_stmt := stmts_in_stmt or.



Section InterpTheory.

(* The getmem/setmem memory accessors are defined as Peano recursions over N,
   rather than natural number recursions.  This is important for keeping proof
   terms small, but can make it more difficult to write inductive proofs.  To
   ease this burden, we here define machinery for inductively reasoning about
   getmem/setmem.

   Proofs that inductively expand getmem/setmem should typically perform the
   following steps:

   (1) Express bitwidth argument w as a product of the form (Mb*n).  If w does
       not already have this form, try doing this:
         rewrite (getmem_div_mul w). rewrite (setmem_div_mul w).
         generalize (w/Mb) as n.

   (2) Use Peano induction to induct over n:
         induction n using N.peano_ind.

   (3) Within the proof, unfold the base case (where w=0) using the getmem_0
       or setmem_0 theorems.

   (4) Unfold inductive cases (where w = N.succ w') using the getmem_succ_r
       or setmem_succ_r theorems. *)

(* Base cases for getmem/setmem *)
Theorem getmem_0: forall e m a, getmem e N0 m a = N0.
Proof. reflexivity. Qed.

Theorem setmem_0: forall e m a v, setmem e N0 m a v = m.
Proof. reflexivity. Qed.

(* Convert getmem/setmem bitwidth arguments into a multiple of bytes. *)
Theorem getmem_div_mul:
  forall w e, getmem e w = getmem e (Mb*(w/Mb)).
Proof.
  intros. unfold getmem.
  rewrite N.mul_comm. rewrite N.div_mul by apply Mb_nonzero.
  reflexivity.
Qed.

Theorem setmem_div_mul:
  forall w e, setmem e w = setmem e (Mb*(w/Mb)).
Proof.
  intros. unfold setmem.
  rewrite N.mul_comm. rewrite N.div_mul by apply Mb_nonzero.
  reflexivity.
Qed.

(* Unfold getmem/setmem by one byte (for inductive cases of proofs). *)
Theorem getmem_succ_r:
  forall e w m a, getmem e (Mb * N.succ w) m a =
    match e with BigE => N.lor (getmem e (Mb*w) m (N.succ a)) (N.shiftl (m a) (Mb*w))
               | LittleE => N.lor (m a) (N.shiftl (getmem e (Mb*w) m (N.succ a)) Mb)
    end.
Proof.
  intros. unfold getmem.
  do 2 (rewrite N.mul_comm; rewrite N.div_mul by apply Mb_nonzero). rewrite N.mul_comm.
  rewrite (N.recursion_succ (@eq (addr->N))).
  destruct e; reflexivity.
  reflexivity.
  intros x y H1 f g H2. rewrite H1,H2. reflexivity.
Qed.

Theorem setmem_succ_r:
  forall e w m a v, setmem e (Mb * N.succ w) m a v =
    match e with BigE => setmem e (Mb*w) (update N.eq_dec m a (N.shiftr v (Mb*w))) (N.succ a) (v mod 2^(Mb*w))
               | LittleE => setmem e (Mb*w) (update N.eq_dec m a match w with N0 => v | Npos _ => v mod 2^Mb end) (N.succ a) (N.shiftr v Mb)
    end.
Proof.
  intros. unfold setmem.
  do 2 (rewrite N.mul_comm; rewrite N.div_mul by apply Mb_nonzero). rewrite N.mul_comm.
  rewrite (N.recursion_succ (@eq ((addr->N)->addr->N->(addr->N)))).
  destruct e; reflexivity.
  reflexivity.
  intros x y H1 f g H2. rewrite H1,H2. reflexivity.
Qed.

Corollary getmem_succ_l:
  forall e w m a, getmem e (N.succ w * Mb) m a =
    match e with BigE => N.lor (getmem e (w*Mb) m (N.succ a)) (N.shiftl (m a) (w*Mb))
               | LittleE => N.lor (m a) (N.shiftl (getmem e (w*Mb) m (N.succ a)) Mb)
    end.
Proof. intros. rewrite N.mul_comm, (N.mul_comm w). apply getmem_succ_r. Qed.

Theorem setmem_succ_l:
  forall e w m a v, setmem e (N.succ w * Mb) m a v =
    match e with BigE => setmem e (w*Mb) (update N.eq_dec m a (N.shiftr v (w*Mb))) (N.succ a) (v mod 2^(w*Mb))
               | LittleE => setmem e (w*Mb) (update N.eq_dec m a match w with N0 => v | Npos _ => v mod 2^Mb end) (N.succ a) (N.shiftr v Mb)
    end.
Proof. intros. rewrite N.mul_comm, (N.mul_comm w). apply setmem_succ_r. Qed.

Corollary getmem_mul:
  forall e w m a, getmem e (Mb * w) m a =
    match w with N0 => N0 | Npos _ =>
      match e with BigE => N.lor (getmem e (Mb * N.pred w) m (N.succ a)) (N.shiftl (m a) (Mb * N.pred w))
                 | LittleE => N.lor (m a) (N.shiftl (getmem e (Mb * N.pred w) m (N.succ a)) Mb)
    end
  end.
Proof.
  intros. destruct w as [|w]. rewrite N.mul_0_r. apply getmem_0.
  rewrite <- (N.succ_pred (Npos w)) by discriminate 1.
  rewrite N.pred_succ.
  apply getmem_succ_r.
Qed.

Theorem setmem_mul:
  forall e w m a v, setmem e (Mb * w) m a v =
    match w with N0 => m | Npos _ =>
      match e with BigE => setmem e (Mb * N.pred w) (update N.eq_dec m a (N.shiftr v (Mb * N.pred w))) (N.succ a) (v mod 2^(Mb * N.pred w))
                 | LittleE => setmem e (Mb * N.pred w) (update N.eq_dec m a match N.pred w with N0 => v | Npos _ => v mod 2^Mb end) (N.succ a) (N.shiftr v Mb)
      end
    end.
Proof.
  intros. destruct w as [|w]. rewrite N.mul_0_r. apply setmem_0.
  rewrite <- (N.succ_pred (Npos w)) by discriminate 1.
  rewrite N.pred_succ.
  apply setmem_succ_r.
Qed.

Remark sub_div_mul: forall w, (w-Mb)/Mb*Mb = Mb * N.pred (w/Mb).
Proof.
  intros. destruct (N.le_gt_cases Mb w) as [H|H].

  rewrite (N.div_mod' w Mb) at 1.
  rewrite N.add_comm, (N.mul_comm _ (_/_)).
  rewrite <- N.add_sub_assoc.
  rewrite <- (N.mul_1_l Mb) at 4.
  rewrite <- N.mul_sub_distr_r.
  rewrite N.div_add by apply Mb_nonzero.
  rewrite (N.div_small (_ mod _)) by apply N.mod_lt, Mb_nonzero.
  rewrite N.add_0_l, N.sub_1_r. apply N.mul_comm.

  rewrite <- N.mul_1_l at 1.
  apply N.mul_le_mono_r.
  apply N.div_le_lower_bound. apply Mb_nonzero. rewrite N.mul_1_r. assumption.

  rewrite (N.div_small w) by assumption.
  rewrite N.mul_0_r.
  replace (w - Mb) with 0. reflexivity.
  symmetry. apply N.sub_0_le, N.lt_le_incl. assumption.
Qed.

Corollary getmem_byte:
  forall e w m a, getmem e w m a =
    match w/Mb with N0 => N0 | Npos _ =>
      match e with BigE => N.lor (getmem e (w-Mb) m (N.succ a)) (N.shiftl (m a) (Mb * N.pred (w/Mb)))
                 | LittleE => N.lor (m a) (N.shiftl (getmem e (w-Mb) m (N.succ a)) Mb)
      end
    end.
Proof.
  intros.
  rewrite (getmem_div_mul (_-_)), N.mul_comm, sub_div_mul, getmem_div_mul.
  apply getmem_mul.
Qed.

Corollary setmem_byte:
  forall e w m a v, setmem e w m a v =
    match w/Mb with N0 => m | Npos _ =>
      match e with BigE => setmem e (w-Mb) (update N.eq_dec m a (N.shiftr v (Mb*N.pred(w/Mb)))) (N.succ a) (v mod 2^(Mb*N.pred(w/Mb)))
                 | LittleE => setmem e (w-Mb) (update N.eq_dec m a match N.pred(w/Mb) with N0 => v | Npos _ => v mod 2^Mb end) (N.succ a) (N.shiftr v Mb)
      end
    end.
Proof.
  intros.
  rewrite (setmem_div_mul (_-_)), N.mul_comm, sub_div_mul, setmem_div_mul.
  apply setmem_mul.
Qed.

(* special cases for when getmem/setmem are applied to access a single memory byte *)
Corollary getmem_Mb: forall e m a, getmem e Mb m a = m a.
Proof.
  intros.
  rewrite getmem_byte, N.div_same, N.sub_diag, getmem_0 by apply Mb_nonzero.
  destruct e.
    rewrite N.mul_0_r, N.shiftl_0_r. apply N.lor_0_l.
    rewrite N.shiftl_0_l. apply N.lor_0_r.
Qed.

Corollary setmem_Mb: forall e, setmem e Mb = update N.eq_dec.
Proof.
  intros. extensionality m. extensionality a. extensionality v.
  rewrite setmem_byte, N.div_same, N.sub_diag, setmem_0, setmem_0 by apply Mb_nonzero.
  destruct e.
    rewrite N.mul_0_r, N.shiftr_0_r. reflexivity.
    reflexivity.
Qed.


(* Break an (i+j)-byte number read/stored to/from memory into two numbers of size i and j. *)
Theorem getmem_split:
  forall e i j m a, getmem e (Mb*(i+j)) m a =
    match e with BigE => N.lor (getmem e (Mb*j) m (a+i)) (N.shiftl (getmem e (Mb*i) m a) (Mb*j))
               | LittleE => N.lor (getmem e (Mb*i) m a) (N.shiftl (getmem e (Mb*j) m (a+i)) (Mb*i))
    end.
Proof.
  induction i using N.peano_ind; intros.
    rewrite N.add_0_l, N.add_0_r, N.mul_0_r, getmem_0, N.shiftl_0_l, N.shiftl_0_r, N.lor_0_r, N.lor_0_l. destruct e; reflexivity.
    rewrite <- N.add_succ_comm, getmem_succ_r, N.add_succ_l. destruct e.
      rewrite N.shiftl_lor, N.shiftl_shiftl, N.lor_assoc, <- IHi, <- N.mul_add_distr_l. apply getmem_succ_r.
      rewrite (N.mul_succ_r _ i), <- N.shiftl_shiftl, <- N.lor_assoc, <- N.shiftl_lor, <- IHi. apply getmem_succ_r.
Qed.

Theorem setmem_split:
  forall e i j m a v, setmem e (Mb*(i+j)) m a v =
    match e with BigE => setmem e (Mb*j) (setmem e (Mb*i) m a (N.shiftr v (Mb*j))) (a+i) match i with N0 => v | Npos _ => v mod 2^(Mb*j) end
               | LittleE => setmem e (Mb*j) (setmem e (Mb*i) m a match j with N0 => v | Npos _ => v mod 2^(Mb*i) end) (a+i) (N.shiftr v (Mb*i))
    end.
Proof.
  induction i using N.peano_ind; intros.
    rewrite N.add_0_l, N.add_0_r, N.mul_0_r, N.shiftr_0_r, setmem_0, setmem_0. destruct e; reflexivity.
    rewrite <- N.add_succ_comm, setmem_succ_r, setmem_succ_r, N.add_succ_l. destruct e.

      rewrite <- (N.succ_pos_spec i), N.shiftr_shiftr, <- N.mul_add_distr_l, (N.add_comm j), setmem_succ_r, IHi.
      rewrite <- N.land_ones, <- N.land_ones, N.shiftr_land, (N.shiftr_div_pow2 (N.ones _)).
      rewrite N.ones_div_pow2 by (rewrite N.mul_add_distr_l, N.add_comm; apply N.le_add_r).
      rewrite N.mul_add_distr_l at 2. rewrite N.add_sub, N.land_ones, <- N.land_assoc, N.land_ones, N.land_ones.
      rewrite N.ones_mod_pow2 by (rewrite N.mul_add_distr_l, N.add_comm; apply N.le_add_r).
      rewrite N.land_ones. destruct i; reflexivity.

      rewrite setmem_succ_r, IHi. destruct j.
        rewrite N.mul_0_r, N.add_0_r, setmem_0, setmem_0. reflexivity.
        destruct i.
          rewrite N.mul_0_r, N.add_0_l, setmem_0, setmem_0, N.mul_1_r, N.shiftr_0_r. reflexivity.
          destruct (N.pos _ + N.pos _) eqn:H.
            apply N.eq_add_0 in H. destruct H. discriminate H.

            rewrite N.shiftr_shiftr.
            rewrite <- (N.land_ones _ (_*N.succ _)), <- (N.land_ones (N.land _ _)), <- N.land_assoc.
            rewrite N.shiftr_land, (N.shiftr_div_pow2 (N.ones _)).
            rewrite N.land_ones.
            rewrite N.ones_mod_pow2, N.ones_div_pow2 by (rewrite N.mul_succ_r, N.add_comm; apply N.le_add_r).
            rewrite N.land_ones, N.land_ones, N.mul_succ_r, N.add_sub, (N.add_comm (_*_)).
            reflexivity.
Qed.



(* Frame property: Updating variable x does not affect the value of any other variable z. *)
Theorem update_frame:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y}) (s:A->B) x y z (NE: z<>x),
  update eq s x y z = s z.
Proof.
  intros. unfold update. destruct (eq z x).
    exfalso. apply NE. assumption.
    reflexivity.
Qed.

(* Updating x and then reading it returns its new value. *)
Theorem update_updated:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y}) (s:A->B) x y,
  update eq s x y x = y.
Proof.
  intros. unfold update. destruct (eq x x).
    reflexivity.
    exfalso. apply n. reflexivity.
Qed.

(* Reversing the order of assignments to two different variables yields the same store. *)
Theorem update_swap:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y})
         (s:A->B) x1 x2 y1 y2 (NE:x1<>x2),
  update eq (update eq s x1 y1) x2 y2 = update eq (update eq s x2 y2) x1 y1.
Proof.
  intros. extensionality z. unfold update.
  destruct (eq z x2).
    subst z. destruct (eq x2 x1).
      exfalso. apply NE. symmetry. assumption.
      reflexivity.
    destruct (eq z x1); reflexivity.
Qed.

(* Overwriting a store value discards the earlier update. *)
Theorem update_cancel:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y}) (s:A->B) x y1 y2,
  update eq (update eq s x y1) x y2 = update eq s x y2.
Proof.
  intros. apply functional_extensionality. intro z. unfold update.
  destruct (eq z x); reflexivity.
Qed.

(* Equivalent updates within a sequence of updates can be disregarded when searching
   for updates that cancel each other via update_cancel. *)
Theorem update_inner_same:
  forall {A B} (eq:forall (x y:A), {x=y}+{x<>y}) (s1 s2:A->B) x1 y1 x2 y2,
    update eq s1 x2 y2 = update eq s2 x2 y2 ->
  update eq (update eq s1 x1 y1) x2 y2 = update eq (update eq s2 x1 y1) x2 y2.
Proof.
  intros. destruct (eq x1 x2).
    subst x2. do 2 rewrite update_cancel. assumption.
    rewrite (update_swap eq s1), (update_swap eq s2) by assumption. rewrite H. reflexivity.
Qed.

(* If variable id's value u is known for store s, then s[id:=u] is the same as s.
   This fact is useful for "stocking" store expressions with explicit updates that
   reveal the values of known variables, allowing tactics to use that information to
   make progress without searching the rest of the proof context. *)
Theorem store_upd_eq {s:store} {id u}:
  forall (SV: s id = u), s = update vareq s id u.
Proof.
  intro.
  extensionality v.
  destruct (vareq v id).
    subst v. rewrite update_updated. exact SV.
    rewrite update_frame. reflexivity. assumption.
Qed.

(* setmem doesn't modify addresses below a, or address at or above a+w. *)
Theorem setmem_frame_low:
  forall e w m a v a' (LT: a' < a),
  setmem e w m a v a' = m a'.
Proof.
  intros. rewrite setmem_div_mul. generalize (w/Mb) as n. intro.
  revert m a v LT. induction n using N.peano_ind; intros.
    rewrite N.mul_0_r. reflexivity.
    rewrite setmem_succ_r. destruct e;
      rewrite IHn by apply N.lt_lt_succ_r, LT; apply update_frame, N.lt_neq, LT.
Qed.

Theorem setmem_frame_high:
  forall e w m a v a' (LE: a + w/Mb*Mb <= a'),
  setmem e w m a v a' = m a'.
Proof.
  intros until a'. rewrite setmem_div_mul. generalize (w/Mb) as n. intro.
  revert m a v. induction n using N.peano_ind; intros.
    rewrite N.mul_0_r. reflexivity.

    assert (LT: a < a'). eapply N.lt_le_trans; [|exact LE].
      apply N.lt_add_pos_r, N.mul_pos_pos. apply N.lt_0_succ. apply N.neq_0_lt_0, Mb_nonzero.
    rewrite setmem_succ_r. destruct e; (rewrite IHn;
    [ apply update_frame, not_eq_sym, N.lt_neq, LT
    | rewrite N.add_succ_l; apply N.le_succ_l; (eapply N.lt_le_trans; [|exact LE]); apply N.add_lt_mono_l, N.mul_lt_mono_pos_r;
      [ apply N.neq_0_lt_0, Mb_nonzero
      | apply N.lt_succ_diag_r ] ] ).
Qed.

(* to_twoscomp inverts of_twoscomp *)
Theorem twoscomp_inv:
  forall n w (LT: n < 2^w),
  to_twoscomp (of_twoscomp (n,w)) w = n.
Proof.
  assert (EXNEG: forall z, (z<0)%Z -> exists p, z = Z.neg p).
    intros. apply Z.lt_gt in H. destruct z; try discriminate. exists p. reflexivity.

  intros.
  destruct w. destruct n. reflexivity. apply N.lt_gt in LT. destruct p; discriminate LT.
  simpl. unfold to_twoscomp. destruct (2^Pos.pred_N p <=? n) eqn:P.

  apply N2Z.inj_lt in LT. simpl in LT.
  apply (Z.sub_lt_le_mono _ _ (Z.pos(2^p)) (Z.pos(2^p))) in LT; [|reflexivity].
  rewrite Z.sub_diag in LT. apply EXNEG in LT. destruct LT as [p' LT]. rewrite LT.
  apply N.add_sub_eq_r, N2Z.inj. rewrite N2Z.inj_add. simpl.
  apply Z.sub_cancel_r with (p:=Z.pos p').
  rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, <- (Pos2Z.opp_neg p'), Z.sub_opp_r, <- LT.
  symmetry. apply Zplus_minus.

  destruct (Z.of_N n) eqn:H.
    apply N2Z.inj_iff. symmetry. assumption.
    apply N2Z.inj. rewrite positive_N_Z. symmetry. assumption.
    destruct n; discriminate H.
Qed.

(* getmem inverts setmem *)
Lemma recompose_bytes:
  forall w v, N.lor (v mod 2^w) (N.shiftl (N.shiftr v w) w) = v.
Proof.
  intros.
  rewrite <- N.ldiff_ones_r, <- N.land_ones, N.lor_comm.
  apply N.lor_ldiff_and.
Qed.

Theorem getmem_setmem:
  forall e w m a v,
  getmem e w (setmem e w m a v) a = match w/Mb with N0 => N0 | Npos _ => v end.
Proof.
  intros. rewrite setmem_div_mul, getmem_div_mul. generalize (w/Mb) as n. intro.
  revert m a v. clear w. induction n using N.peano_ind; intros.
    rewrite N.mul_0_r. apply getmem_0.
    rewrite <- N.succ_pos_spec at 3. rewrite getmem_succ_r, setmem_succ_r. destruct e.
      rewrite IHn. destruct n.
        rewrite N.lor_0_l, N.mul_0_r, setmem_0, N.shiftl_0_r, N.shiftr_0_r. apply update_updated.
        rewrite setmem_frame_low by apply N.lt_succ_diag_r. rewrite update_updated. apply recompose_bytes.
      rewrite IHn. destruct n.
        rewrite N.mul_0_r, setmem_0, N.shiftl_0_l, N.lor_0_r. apply update_updated.
        rewrite setmem_frame_low by apply N.lt_succ_diag_r. rewrite update_updated. apply recompose_bytes.
Qed.



(* The semantics of eval_exp, exec_stmt, and exec_prog are deterministic
   as long as there are no Unknown expressions. *)

Definition not_unknown e := match e with Unknown _ => False | _ => True end.

Theorem eval_exp_deterministic:
  forall {RW e s v1 v2} (NU: forall_exps_in_exp not_unknown e)
         (E1: eval_exp RW s e v1) (E2: eval_exp RW s e v2), v1=v2.
Proof.
  induction e; intros; inversion E1; inversion E2; clear E1 E2; subst;
  unfold forall_exps_in_exp in NU; simpl in NU;
    repeat match type of NU with _ /\ _ => let H := fresh NU in destruct NU as [H NU] end;
  try match goal with [ H: Va _ _ = Va _ _ |- _] => injection H; clear H; intros; subst end;
  try (remember (match n0 with N0 => e3 | _ => e2 end) as e);
  repeat match goal with [ IH: forall _ _ _, _ -> eval_exp _ _ ?E _ -> eval_exp _ _ ?E _ -> _=_,
                           H0: exps_in_exp and not_unknown ?E,
                           H1: eval_exp _ ?S ?E ?V1,
                           H2: eval_exp _ ?S ?E ?V2 |- _ ] =>
           specialize (IH S V1 V2 H0 H1 H2); clear H0 H1 H2;
           try (injection IH; clear IH; intros); subst;
           try match type of E' with
             eval_exp _ _ (match ?N with N0 => _ | _ => _ end) _ => destruct N
           end
         end;
  try reflexivity.

  rewrite SV in SV0. injection SV0. intro. assumption.
  rewrite H2. reflexivity.
  exfalso. assumption.
Qed.

Theorem exec_stmt_deterministic:
  forall {RW s q n s1 x1 s2 x2} (NU: forall_exps_in_stmt not_unknown q)
         (X1: exec_stmt RW s q n s1 x1) (X2: exec_stmt RW s q n s2 x2),
  s1 = s2 /\ x1 = x2.
Proof.
  intros. revert s2 x2 X2.
  dependent induction X1; intros; inversion X2; subst;
  try solve [ split;reflexivity ];
  try destruct NU as [NU1 NU2].

  replace u0 with u.
    split; reflexivity.
    apply (eval_exp_deterministic NU E E0).

  assert (H:=eval_exp_deterministic NU E E0).
  injection H. intros. subst. split; reflexivity.

  apply IHX1; assumption.

  apply (IHX1 NU1) in XS1. destruct XS1. discriminate.

  apply (IHX1_1 NU1) in XS. destruct XS. discriminate.

  apply (IHX1_1 NU1),proj1 in XS1. subst. apply (IHX1_2 NU2) in XS0. assumption.

  apply IHX1; repeat first [ assumption | split ].

  apply IHX1.
    destruct NU2. destruct c; assumption.
    assert (H:=eval_exp_deterministic NU1 E E0). injection H; intros; subst. assumption.
Qed.

Theorem exec_prog_deterministic:
  forall {RW p a s m n s1 x1 s2 x2}
  (NU: forall a', match p a' with None => True | Some (_,q) => forall_exps_in_stmt not_unknown q end)
  (XP1: exec_prog RW p a s m n s1 x1) (XP2: exec_prog RW p a s m n s2 x2),
  s1 = s2 /\ x1 = x2.
Proof.
  intros. revert s2 x2 XP2. dependent induction XP1; intros; inversion XP2; subst;
  assert (NUa:=NU a);
  try (rewrite LU0 in LU; first [ discriminate LU
                                | injection LU; clear LU; intros; subst; rewrite LU0 in NUa ]);
  try solve [ split;reflexivity ];
  assert (ESD:=exec_stmt_deterministic NUa XS XS0);
  destruct ESD as [ESD1 ESD2]; try (injection ESD2; clear ESD2; intro); subst.

  replace a'0 with a' in XP.
    apply IHXP1. assumption.
    destruct x0 as [x0|]; [destruct x0|]; first
    [ discriminate
    | injection EX; injection EX0; intros; subst; subst; reflexivity ].

  destruct x2; discriminate.

  destruct x; discriminate.

  split; reflexivity.
Qed.


(* Some monotonicity properties: *)

(* exec_stmt and exec_prog are monotonic with respect to their input and output
   stores (i.e., there is no "delete variable" operation). *)

Theorem exec_stmt_nodelete:
  forall {RW s q n s' x} (XS: exec_stmt RW s q n s' x) v (V': s' v = None),
  s v = None.
Proof.
  intros. dependent induction XS; try apply IHXS; try assumption.
  unfold update in V'. destruct (vareq v id). discriminate. assumption.
  apply IHXS1,IHXS2. assumption.
Qed.

Theorem exec_prog_nodelete:
  forall {RW p a s m n s' x} (XP: exec_prog RW p a s m n s' x)
         v (V': s' v = None),
  s v = None.
Proof.
  intros. dependent induction XP; try assumption;
  apply (exec_stmt_nodelete XS); try apply IHXP; assumption.
Qed.

Theorem eval_exp_mono:
  forall {RW e v s1} s2 (E: eval_exp RW s1 e v) (SS: po_subset s1 s2),
  eval_exp RW s2 e v.
Proof.
  induction e; intros; inversion E; clear E; subst;
  repeat match goal with [ IH: forall _ _ _, eval_exp _ _ ?E _ -> _ -> eval_exp _ _ ?E _,
                           H: eval_exp _ _ ?E _ |- _ ] =>
    let H':=fresh "IH" H in assert (H':=IH _ _ _ H SS); clear IH
  end;
  try (econstructor; eassumption).

  apply EVar. apply SS. assumption.

  apply ELet with (u1:=u1). assumption.
    apply IHe2 with (s1:=update vareq s1 id (Some u1)); [assumption|].
    intros x y. unfold update. intro. destruct (vareq x id). assumption.
    apply SS. assumption.

  apply EIte with (n1:=n1) (w1:=w1). assumption. destruct n1.
    apply (IHe3 _ s1); assumption.
    apply (IHe2 _ s1); assumption.
Qed.

Theorem exec_stmt_mono:
  forall {RW s1 q m s1' x} s2 (XS: exec_stmt RW s1 q m s1' x) (PO: po_subset s1 s2),
  exec_stmt RW s2 q m (updateall s2 s1') x.
Proof.
  intros. revert s2 PO. dependent induction XS; intros;
  try (rewrite updateall_subset; [ try constructor | assumption ]).

  replace (updateall s2 (s[id:=Some u])) with (s2[id:=Some u]).
    apply XMove. apply (eval_exp_mono _ E PO).
    extensionality x. unfold update,updateall. destruct (vareq x id).
      reflexivity.
      unfold po_subset in PO. specialize PO with (x:=x). destruct (s x).
        apply PO. reflexivity.
        reflexivity.

  apply XJmp with (w:=w). apply (eval_exp_mono _ E PO).

  apply XSeq1. apply IHXS. assumption.

  apply XSeq2 with (s2:=updateall s0 s2).
    apply IHXS1. assumption.
    replace (updateall s0 s') with (updateall (updateall s0 s2) s').
      apply IHXS2. apply subset_updateall.
      extensionality z. unfold updateall. assert (H:=exec_stmt_nodelete XS2 z). destruct (s' z).
        reflexivity.
        rewrite H. reflexivity. reflexivity.

  apply XWhile. apply IHXS. assumption.

  apply XIf with (c:=c). apply (eval_exp_mono _ E PO). apply IHXS. assumption.
Qed.

Theorem exec_prog_mono:
  forall {RW p a s1 m n s1' x} s2 (XP: exec_prog RW p a s1 m n s1' x) (PO: po_subset s1 s2),
  exec_prog RW p a s2 m n (updateall s2 s1') x.
Proof.
  intros. revert s2 PO. dependent induction XP; intros.

  replace (updateall s2 s) with s2.
    constructor.
    symmetry. apply updateall_subset. assumption.

  apply XPStep with (sz:=sz) (q:=q) (s2:=updateall s0 s2) (x1:=x1) (a':=a'); try assumption.
    apply (exec_stmt_mono _ XS PO).
    replace (updateall s0 s') with (updateall (updateall s0 s2) s').
      apply IHXP. apply subset_updateall.
      extensionality z. unfold updateall. assert (H:=exec_prog_nodelete XP z). destruct (s' z).
        reflexivity.
        rewrite H. reflexivity. reflexivity.

  apply XPDone with (sz:=sz) (q:=q); try assumption.
    apply (exec_stmt_mono _ XS PO).
Qed.



(* If there are no while-loops, we can compute a necessary and sufficient recursion bound to
   avoid an Unfinished condition for execution of any statement. *)

Fixpoint step_bound (q:stmt) : option nat :=
  match q with
  | Nop | Move _ _ | Jmp _ | CpuExn _ => Some 1%nat
  | Seq q1 q2 | If _ q1 q2 => match step_bound q1, step_bound q2 with
                              | Some n1, Some n2 => Some (S (max n1 n2))
                              | _, _ => None
                              end
  | While _ _ => None
  end.

Theorem step_bound_pos:
  forall q n (SB: step_bound q = Some n), (0<n)%nat.
Proof.
  induction q; intros.
  all: simpl in SB; try (injection SB; clear SB; intro; subst n).
  1-4: exact Nat.lt_0_1.
  2: discriminate.
  all: destruct (step_bound q1); destruct (step_bound q2); try discriminate.
  all: injection SB; clear SB; intro; subst n.
  all: apply Nat.lt_0_succ.
Qed.

Theorem stmt_finish:
  forall RW s q n n' s' x
         (SB: step_bound q = Some n) (LT: (n <= n')%nat)
         (XS: exec_stmt RW s q n' s' x),
  x <> Some Unfinished.
Proof.
  intros.
  revert n SB LT. dependent induction XS; intros; try discriminate.

  exfalso. apply le_not_lt in LT. apply LT. revert SB. apply step_bound_pos.

  3: destruct c.
  all: simpl in SB; destruct (step_bound q1); destruct (step_bound q2); try discriminate.
  all: injection SB; clear SB; intro; subst n0.
  2: rename IHXS2 into IHXS.
  all: eapply IHXS; [reflexivity|].
  all: transitivity (max n1 n2); [ first [ apply Max.le_max_l | apply Max.le_max_r ]
                                 | apply le_S_n; assumption ].
Qed.

(* A stmt that finishes within n steps will also finish within (S n) steps. *)
Theorem exec_stmt_incbound:
  forall RW m s q s' x (FIN: x <> Some Unfinished) (XS: exec_stmt RW s q m s' x),
  exec_stmt RW s q (S m) s' x.
Proof.
  induction m; intros; inversion XS; clear XS; subst.
    contradict FIN. reflexivity.
    apply XNop.
    apply XMove. exact E.
    eapply XJmp. exact E.
    apply XExn.
    apply XSeq1. apply IHm. exact FIN. exact XS0.
    eapply XSeq2.
      apply IHm. discriminate 1. exact XS1.
      apply IHm. exact FIN. exact XS0.
    apply XWhile. apply IHm. exact FIN. exact XS0.
    eapply XIf. exact E. apply IHm. exact FIN. exact XS0.
Qed.

Corollary exec_stmt_raisebound:
  forall RW m' m s q s' x (LE: (m <= m')%nat) (FIN: x <> Some Unfinished) (XS: exec_stmt RW s q m s' x),
  exec_stmt RW s q m' s' x.
Proof.
  intros. pattern m'. revert m' LE. apply le_ind.
    exact XS.
    intros. apply exec_stmt_incbound. exact FIN. assumption.
Qed.

(* To prove properties of while-loops, it suffices to prove that each loop iteration
   preserves the property.  This is equivalent to stepping the loop three small-steps
   at a time (to unfold the While->If->Seq expansion of the loop). *)
Theorem while_inv:
  forall (P: store -> Prop)
         RW s e q m s' x (XS: exec_stmt RW s (While e q) m s' x) (PRE: P s)
         (INV: forall s c m s' x (PRE: P s)
                      (EX: eval_exp RW s e (VaN (Npos c, 1)))
                      (XS: exec_stmt RW s q m s' x), P s'),
  P s'.
Proof.
  intros. revert s s' x XS PRE.
  rewrite (Nat.div_mod m 3); [|discriminate].
  induction (Nat.div m 3) as [|m'].

  simpl. destruct (snd _); intros.
    inversion XS; inversion XS0; inversion XS1; subst. exact PRE.
    destruct y.
      inversion XS; inversion XS0; subst. exact PRE.
      inversion XS; subst. exact PRE.

  rewrite Nat.mul_succ_r. rewrite (plus_comm _ 3). rewrite <- plus_assoc. intros.
  inversion XS; inversion XS0; subst. destruct c; inversion XS1; subst.
    exact PRE.
    eapply INV. exact PRE. exact E. exact XS2.
    eapply IHm'.
      exact XS3.
      eapply INV. exact PRE. exact E. exact XS2.
Qed.

(* Append a step to an exec_prog computation. *)
Theorem exec_prog_append:
  forall RW p n a s m sz q s2 a1 s' x'
         (XP: exec_prog RW p a s m n s2 (Exit a1))
         (LU: p a1 = Some (sz,q))
         (XS: exec_stmt RW s2 q m s' x'),
    exec_prog RW p a s m (S n) s' (match x' with None => Exit (a1+sz)
                                               | Some x' => x' end).
Proof.
  induction n; intros.
    inversion XP; subst. destruct x'; [destruct e|].
      eapply XPDone. exact LU. exact XS. reflexivity.
      eapply XPStep. exact LU. exact XS. reflexivity. apply XPZero.
      eapply XPDone. exact LU. exact XS. reflexivity.
      eapply XPStep. exact LU. exact XS. reflexivity. apply XPZero.
    inversion XP; subst.
      eapply XPStep. exact LU0. exact XS0. exact EX. eapply IHn. exact XP0. exact LU. exact XS.
      discriminate.
Qed.

(* Split an exec_prog computation into two parts. *)
Theorem exec_prog_split:
  forall RW p a s m n1 n2 s' x'
         (XP: exec_prog RW p a s m (n1 + S n2)%nat s' x'),
  exists s1 a1, exec_prog RW p a s m n1 s1 (Exit a1) /\ exec_prog RW p a1 s1 m (S n2) s' x'.
Proof.
  intros. revert n2 XP. induction n1; intros.
    exists s,a. split. apply XPZero. exact XP.
    rewrite Nat.add_succ_comm in XP. destruct (IHn1 _ XP) as [s1 [a1 [XP1 XP2]]]. inversion XP2; subst. exists s2,a'. split.
      eapply exec_prog_append in XP1; [|exact LU | exact XS]. destruct x1 as [e|]; [destruct e|].
        discriminate EX.
        injection EX as; subst. exact XP1.
        discriminate EX.
        injection EX as; subst. exact XP1.
      assumption.
Qed.

(* Concatenate two exec_prog comptations into one whole. *)
Theorem exec_prog_concat:
  forall RW p a s m n1 n2 s1 a1 s' x'
         (XP1: exec_prog RW p a s m n1 s1 (Exit a1)) (XP2: exec_prog RW p a1 s1 m (S n2) s' x'),
  exec_prog RW p a s m (n1 + S n2)%nat s' x'.
Proof.
  intros. revert n2 s1 a1 XP1 XP2. induction n1; intros.
    inversion XP1; subst. exact XP2.
    rewrite <- Nat.add_1_r in XP1. apply exec_prog_split in XP1. destruct XP1 as [s2 [a2 [XP0 XP1]]]. rewrite Nat.add_succ_comm. eapply IHn1.
     exact XP0.
     inversion XP1; subst.
       eapply XPStep. exact LU. exact XS. exact EX. inversion XP; subst. exact XP2.
       discriminate EX.
Qed.

(* To prove that a property holds at the conclusion of a program's execution, it suffices
   to prove that the property is preserved by every statement in the program. *)
Theorem prog_inv_universal:
  forall (P: exit -> store -> Prop)
         RW (p:program) a0 s0 m n s' x' (XP: exec_prog RW p a0 s0 m n s' x') (PRE: P (Exit a0) s0)
         (INV: forall a1 s1 sz q s1' x1 (IL: p a1 = Some (sz,q)) (PRE: P (Exit a1) s1)
                      (XS: exec_stmt RW s1 q m s1' x1),
               P (match x1 with None => Exit (a1 + sz)
                              | Some x => x end) s1'),
  P x' s'.
Proof.
  intros. revert a0 s0 XP PRE. induction n; intros; inversion XP; subst.
    exact PRE.
    apply (IHn a' s2).
      exact XP0.
      specialize (INV a0 s0 sz q s2 x1 LU PRE XS). destruct x1; [destruct e|].
        1,3: discriminate.
        1,2: injection EX; intro; subst a'; exact INV.
    specialize (INV a0 s0 sz q s' (Some x') LU PRE XS). exact INV.
Qed.

(* Alternatively, one may prove that the property is preserved by all the reachable statements.
   (The user's invariant may adopt a precondition of False for unreachable statements.) *)
Theorem prog_inv_reachable:
  forall (P: exit -> store -> nat -> Prop)
         RW (p:program) a0 s0 m n s' x' (XP: exec_prog RW p a0 s0 m n s' x') (PRE: P (Exit a0) s0 O)
         (INV: forall a1 s1 n1 sz q s1' x1 (IL: p a1 = Some (sz,q)) (PRE: P (Exit a1) s1 n1) (LT: (n1 < n)%nat)
                      (XP: exec_prog RW p a0 s0 m n1 s1 (Exit a1))
                      (XS: exec_stmt RW s1 q m s1' x1)
                      (XP': match x1 with None => exec_prog RW p (a1+sz) s1' m (n - S n1) s' x'
                                        | Some (Exit a2) => exec_prog RW p a2 s1' m (n - S n1) s' x'
                                        | Some x2 => x'=x2 end),
               P (match x1 with None => Exit (a1 + sz)
                              | Some x => x end) s1' (S n1)),
  P x' s' n.
Proof.
  intros.
  assert (H: exists a1 s1 n2, (n2 <= n)%nat /\ exec_prog RW p a0 s0 m (n - n2) s1 (Exit a1) /\ P (Exit a1) s1 (n - n2)%nat /\ exec_prog RW p a1 s1 m n2 s' x').
    exists a0,s0,n. rewrite Nat.sub_diag. repeat split.
      apply le_n.
      apply XPZero.
      exact PRE.
      exact XP.
  destruct H as [a1 [s1 [n2 [LE [XP1 [PRE1 XP2]]]]]].
  clear XP. revert a1 s1 LE PRE1 XP1 XP2. induction n2; intros.
    inversion XP2; clear XP2; subst. rewrite Nat.sub_0_r in PRE1. exact PRE1.
    inversion XP2; clear XP2; subst.
      apply (IHn2 a' s2).
        transitivity (S n2). apply le_S, le_n. assumption.

        specialize (INV a1 s1 (n - S n2)%nat sz q s2 x1 LU PRE1 (Nat.sub_lt n (S n2) LE (Nat.lt_0_succ n2)) XP1 XS).
        rewrite minus_Sn_m, Nat.sub_succ in INV by exact LE.
        replace (n - (n - n2))%nat with n2 in INV by (apply plus_minus; symmetry; apply Nat.sub_add, le_Sn_le, LE).
        destruct x1; [destruct e|].
          discriminate EX.
          injection EX. intro. subst a'. apply INV. exact XP.
          discriminate EX.
          injection EX. intro. subst a'. apply INV. exact XP.

        destruct n. inversion LE. apply le_S_n in LE. rewrite Nat.sub_succ_l; [|exact LE].
        replace (Exit a') with (match x1 with None => Exit (a1 + sz)
                                            | Some x => x end).
          eapply exec_prog_append. exact XP1. exact LU. exact XS.
          destruct x1; [destruct e|]; first [ discriminate EX | injection EX; intro; subst; reflexivity ].

        exact XP.
      specialize (INV a1 s1 (n-1)%nat sz q s' (Some x') LU PRE1 (Nat.sub_lt n 1 LE Nat.lt_0_1) XP1 XS).
      rewrite minus_Sn_m, Nat.sub_succ, Nat.sub_0_r in INV by exact LE.
      apply INV. destruct x'.
        reflexivity.
        discriminate EX.
        reflexivity.
Qed.

(* Rather than assigning and proving an invariant at every machine instruction, we can generalize
   the above to allow users to assign invariants to only a few machine instructions.  To prove that
   all the invariants are satisfied, the user can prove that any execution that starts in an
   invariant-satisfying state and that reaches another invariant always satisfies the latter. *)

(* The "next invariant satisfied" property is true if we're at an invariant point and the state
   satisfies that invariant, or we're not at an invariant point and (inductively) taking one
   exec_prog step leads to a "next invariant satisfied" state. *)
Inductive next_inv_sat (PS: exit -> store -> nat -> option Prop):
            bool -> exit -> acctyp -> program -> store -> nat -> nat -> nat -> store -> exit -> Prop :=
| NISHere x RW p s m n n' s' x' (TRU: match PS x s n with None => False | Some P => P end):
    next_inv_sat PS true x RW p s m n n' s' x'
| NISStep RW p s m n n' s' x' a
          (STEP: forall sz q s1 x1 (LT: (n < n')%nat)
                        (IL: p a = Some (sz,q)) (XS: exec_stmt RW s q m s1 x1)
                        (XP': match x1 with None => exec_prog RW p (a+sz) s1 m (n' - S n) s' x'
                              | Some (Exit a2) => exec_prog RW p a2 s1 m (n' - S n) s' x'
                              | Some x2 => x'=x2 end),
                 next_inv_sat PS (match PS match x1 with None => Exit (a+sz) | Some x1 => x1 end s1 (S n) with
                                  | Some _ => true | None => false end)
                              match x1 with None => Exit (a+sz) | Some x1 => x1 end
                              RW p s1 m (S n) n' s' x'):
    next_inv_sat PS false (Exit a) RW p s m n n' s' x'.

(* Proving the "next invariant satisfied" property for all invariant points proves partial
   correctness of the program. *)
Theorem prog_inv:
  forall (PS: exit -> store -> nat -> option Prop) RW (p:program) a0 s0 m n s' x'
         (XP: exec_prog RW p a0 s0 m n s' x')
         (PRE: match PS (Exit a0) s0 O with Some P => P | None => False end)
         (INV: forall a1 s1 n1
                      (XP: exec_prog RW p a0 s0 m n1 s1 (Exit a1))
                      (PRE: match PS (Exit a1) s1 n1 with Some P => P | None => False end),
               next_inv_sat PS false (Exit a1) RW p s1 m n1 n s' x'),
  match PS x' s' n with Some P => P | None => True end.
Proof.
  intros.
  assert (NIS: next_inv_sat PS (match PS x' s' n with Some _ => true | None => false end) x' RW p s' m n n s' x').
    pattern x' at -3, s' at -3, n at -3. eapply prog_inv_reachable.
      exact XP.
      destruct (PS (Exit a0) s0 O) eqn:PS0.
        apply NISHere. rewrite PS0. exact PRE.
        exfalso. exact PRE.
      intros. specialize (INV a1 s1 n1 XP0). destruct (PS (Exit a1) s1 n1) eqn:PS1.

        inversion PRE0; subst. rewrite PS1 in TRU. specialize (INV TRU).
        inversion INV; subst. eapply STEP. exact LT. exact IL. exact XS. exact XP'.

        inversion PRE0; subst. eapply STEP. exact LT. exact IL. exact XS. exact XP'.
  destruct (PS x' s' n) eqn:PS'.
    inversion NIS. rewrite PS' in TRU. exact TRU.
    exact I.
Qed.


(* Statements and programs that contain no assignments to some IL variable v
   leave that variable unchanged in the output store. *)
Fixpoint noassign v q :=
  match q with
  | Nop | Jmp _ | CpuExn _ => True
  | Seq q1 q2 | If _ q1 q2 => noassign v q1 /\ noassign v q2
  | While _ q' => noassign v q'
  | Move (Va v1 _) q => v<>v1
  end.

Theorem noassign_inv:
  forall v q (H:noassign v q) RW m (s s':store) x,
  exec_stmt RW s q m s' x -> s' v = s v.
Proof.
  induction q; intros; inversion H0; subst; try reflexivity.
    destruct (vareq id v).
      exfalso. subst. apply H. reflexivity.
      apply update_frame. apply H.
    eapply IHq1. exact (proj1 H). exact XS.
    transitivity (s2 v).
      eapply IHq2. exact (proj2 H). exact XS0.
      eapply IHq1. exact (proj1 H). exact XS1.

    pattern s'. eapply while_inv.
      exact H0.
      reflexivity.
      intros. rewrite <- PRE. eapply IHq. exact H. exact XS0.

    destruct c.
      eapply IHq2. exact (proj2 H). exact XS.
      eapply IHq1. exact (proj1 H). exact XS.
Qed.

Definition prog_noassign v (p:program) :=
  forall a, match p a with None => True | Some (_,q) => noassign v q end.

Theorem prog_noassign_inv:
  forall v RW p (NP: prog_noassign v p) m s' x
         n a s (EP: exec_prog RW p a s m n s' x),
  s' v = s v.
Proof.
  intros. pattern x, s'. eapply prog_inv_universal.
    exact EP.
    reflexivity.
    intros. rewrite <- PRE. apply (noassign_inv v) in XS.
      exact XS.
      specialize (NP a1). rewrite IL in NP. exact NP.
Qed.

End InterpTheory.



Section FInterp.

(* Functional Interpretation of Programs:
   In this section we define an interpreter that is purely functional instead of inductive.  Since programs
   can be non-deterministic (if there are Unknown expressions), this interpreter only computes one possible
   value of each variable.  We then prove that this result is correct according to the operational semantics.
   When there are no unknowns, determinism of the semantics (proved above) proves that the result is precise.
   This facilitates a series of tactics that can interpret common-case expressions and statements in proofs
   to automatically infer the resulting store after execution of each assembly language instruction.

   In order to help Coq expression simplification to infer a value for each symbolic expression, we define
   our interpreter in terms of "untyped values" (uvalues), which always contain both a memory value and a
   numeric value.  This allows the interpreter to progress even when Coq can't automatically infer an
   expression's type. *)

Inductive uvalue := VaU (z:bool) (m:addr->N) (n:N) (w:N).

Definition zstore (_:addr) := 0.

Definition uvalue_of (v:value) :=
  match v with
  | VaN (n,w) => VaU true zstore n w
  | VaM m w => VaU false m 0 w
  end.

Definition of_uvalue (v:uvalue) :=
  match v with VaU z m n w => if z then VaN (n,w) else VaM m w end.

Definition utowidth (w n:N) : uvalue :=
  VaU true zstore (N.modulo n (2^w)) w.

Definition utobit (b:bool) : uvalue :=
  VaU true zstore (if b then 1 else 0) 1.

Definition feval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : uvalue :=
  match bop with
  | OP_PLUS => utowidth w (n1+n2)
  | OP_MINUS => utowidth w (2^w + n1 - n2)
  | OP_TIMES => utowidth w (n1*n2)
  | OP_DIVIDE => VaU true zstore (n1/n2) w
  | OP_SDIVIDE => utowidth w (signed_op Z.quot w n1 n2)
  | OP_MOD => VaU true zstore (N.modulo n1 n2) w
  | OP_SMOD => VaU true zstore (signed_op Z.rem w n1 n2) w
  | OP_LSHIFT => utowidth w (N.shiftl n1 n2)
  | OP_RSHIFT => VaU true zstore (N.shiftr n1 n2) w
  | OP_ARSHIFT => VaU true zstore (ashiftr w n1 n2) w
  | OP_AND => VaU true zstore (N.land n1 n2) w
  | OP_OR => VaU true zstore (N.lor n1 n2) w
  | OP_XOR => VaU true zstore (N.lxor n1 n2) w
  | OP_EQ => utobit (n1 =? n2)
  | OP_NEQ => utobit (negb (n1 =? n2))
  | OP_LT => utobit (n1 <? n2)
  | OP_LE => utobit (n1 <=? n2)
  | OP_SLT => utobit (signed_lt w n1 n2)
  | OP_SLE => utobit (signed_le w n1 n2)
  end.

Definition feval_unop (uop:unop_typ) (n:N) (w:bitwidth) : uvalue :=
  match uop with
  | OP_NEG => VaU true zstore (match n with N0 => N0 | _ => (2^w) - n end) w
  | OP_NOT => VaU true zstore (N.lnot n w) w
  end.

Definition uget (v:option value) : uvalue :=
  match v with None => VaU true zstore 0 0
             | Some u => uvalue_of u
  end.

Lemma fold_uget:
  forall v, match v with None => VaU true zstore 0 0
                       | Some u => uvalue_of u
            end = uget v.
Proof. intros. reflexivity. Qed.

Fixpoint feval_exp (e:exp) (s:store) : uvalue :=
  match e with
  | Var (Va id _) => uget (s id)
  | Word (n,w) => VaU true zstore n w
  | Load e1 e2 en w =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ _, VaU _ _ n _ => VaU true zstore (getmem en w m n) w
      end
  | Store e1 e2 e3 en w =>
      match feval_exp e1 s, feval_exp e2 s, feval_exp e3 s with
      | VaU _ m _ mw, VaU _ _ a _, VaU _ _ v _ => VaU false (setmem en w m a v) 0 mw
      end
  | BinOp bop e1 e2 =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ _ n1 w, VaU _ _ n2 _ => feval_binop bop w n1 n2
      end
  | UnOp uop e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => feval_unop uop n w
      end
  | Cast c w' e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => VaU true zstore (cast c w w' n) w'
      end
  | Let (Va id t) e1 e2 => feval_exp e2 (update vareq s id (Some (of_uvalue (feval_exp e1 s))))
  | Unknown _ => VaU true zstore 0 0
  | Ite e1 e2 e3 =>
      match feval_exp e1 s, feval_exp e2 s, feval_exp e3 s with
      | VaU _ _ n1 _, VaU b2 m2 n2 w2, VaU b3 m3 n3 w3 =>
          VaU (if n1 then b3 else b2) (if n1 then m3 else m2) (if n1 then n3 else n2) (if n1 then w3 else w2)
      end
  | Extract n1 n2 e1 =>
      match feval_exp e1 s with
      | VaU _ _ n w => VaU true zstore (cast CAST_HIGH (N.succ n1) (N.succ (n1-n2))
                                             (cast CAST_LOW w (N.succ n1) n)) (N.succ (n1-n2))
      end
  | Concat e1 e2 =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ _ n1 w1, VaU _ _ n2 w2 => VaU true zstore (N.land (N.shiftl n1 w2) n2) (w1+w2)
      end
  end.

Definition NoMemAcc := True.
Definition MemAcc (RW:acctyp) rw m mw a w := forall n, n < w/Mb -> RW rw m mw (a+n).

Fixpoint memacc_exp (e:exp) (RW:acctyp) (s:store) : Prop :=
  match e with
  | Load e1 e2 _ w =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ mw, VaU _ _ a _ => MemAcc RW false m mw a w
      end
  | Store e1 e2 _ _ w =>
      match feval_exp e1 s, feval_exp e2 s with
      | VaU _ m _ mw, VaU _ _ a _ => MemAcc RW true m mw a w
      end
  | Var _ | Word _ | Unknown _ => NoMemAcc
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => memacc_exp e1 RW s
  | BinOp _ e1 e2 | Concat e1 e2 => memacc_exp e1 RW s /\ memacc_exp e2 RW s
  | Let (Va id _) e1 e2 => memacc_exp e1 RW s /\ memacc_exp e2 RW (update vareq s id (Some (of_uvalue (feval_exp e1 s))))
  | Ite e1 e2 e3 =>
      match feval_exp e1 s with
      | VaU _ _ n w => if n then memacc_exp e3 RW s else memacc_exp e2 RW s
      end
  end.

Fixpoint exp_known (e:exp) :=
  match e with
  | Var _ | Word _ => true
  | Unknown _ => false
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => exp_known e1
  | BinOp _ e1 e2 | Let _ e1 e2 | Concat e1 e2 | Load e1 e2 _ _ => if exp_known e1 then exp_known e2 else false
  | Ite e1 e2 e3 | Store e1 e2 e3 _ _ => if exp_known e1 then (if exp_known e2 then exp_known e3 else false) else false
  end.

Lemma uvalue_inv: forall u, of_uvalue (uvalue_of u) = u.
Proof.
  intros. destruct u.
    destruct n. reflexivity.
    reflexivity.
Qed.

Definition canonical_uvalue (u:uvalue) :=
  match u with VaU z m n w => if z then m = zstore else n = 0 end.

Lemma can_uvalue_inv: forall u (C: canonical_uvalue u), uvalue_of (of_uvalue u) = u.
Proof.
  intros. destruct u. destruct z.
    simpl in C. subst m. reflexivity.
    simpl in C. subst n. reflexivity.
Qed.

Lemma canonical_conv:
  forall v, canonical_uvalue (uvalue_of v).
Proof.
  intro. destruct v. destruct n. reflexivity. reflexivity.
Qed.

Lemma canonical_uget:
  forall v, canonical_uvalue (uget v).
Proof.
  intros. destruct v.
    apply canonical_conv.
    reflexivity.
Qed.

Lemma canonical_feval:
   forall e s, canonical_uvalue (feval_exp e s).
Proof.
  induction e; intros.
    simpl. destruct v. apply canonical_uget.
    destruct n. reflexivity.
    simpl. do 2 destruct (feval_exp _ _). reflexivity.
    simpl. do 3 destruct (feval_exp _ _). reflexivity.
    simpl. do 2 destruct (feval_exp _ _). destruct b; reflexivity.
    simpl. destruct (feval_exp _ _). destruct u; reflexivity.
    simpl. destruct (feval_exp _ _). reflexivity.
    simpl. destruct v. apply IHe2.
    reflexivity.
    simpl. destruct (feval_exp e1 s). destruct (feval_exp e2 s) eqn:FE2. destruct (feval_exp e3 s) eqn:FE3. destruct n.
      rewrite <- FE3. apply IHe3.
      rewrite <- FE2. apply IHe2.
    simpl. destruct (feval_exp _ _). reflexivity.
    simpl. do 2 destruct (feval_exp _ _). reflexivity.
Qed.

Theorem reduce_binop:
  forall bop w n1 n2, eval_binop bop w n1 n2 = of_uvalue (feval_binop bop w n1 n2).
Proof.
  intros. destruct bop; reflexivity.
Qed.

Theorem reduce_unop:
  forall uop w n, eval_unop uop w n = of_uvalue (feval_unop uop w n).
Proof.
  intros. destruct uop; reflexivity.
Qed.

Theorem reduce_exp:
  forall RW e s u (K: exp_known e = true) (E: eval_exp RW s e u), u = of_uvalue (feval_exp e s).
Proof.
  induction e; intros; inversion E; clear E; subst.
    simpl. rewrite SV. symmetry. apply uvalue_inv.
    reflexivity.

    simpl. simpl in K. apply andb_prop in K. destruct K as [K1 K2].
    apply (IHe1 _ _ K1) in E1. destruct (feval_exp e1 _). simpl in E1. destruct z. discriminate E1. injection E1 as; subst.
    apply (IHe2 _ _ K2) in E2. destruct (feval_exp e2 _). simpl in E2. destruct z; [|discriminate E2]. injection E2 as; subst.
    reflexivity.

    simpl. simpl in K. apply andb_prop in K. destruct K as [K1 K]. apply andb_prop in K. destruct K as [K2 K3].
    apply (IHe1 _ _ K1) in E1. destruct (feval_exp e1 _). simpl in E1. destruct z. discriminate E1. injection E1 as; subst.
    apply (IHe2 _ _ K2) in E2. destruct (feval_exp e2 _). simpl in E2. destruct z; [|discriminate E2]. injection E2 as; subst.
    apply (IHe3 _ _ K3) in E3. destruct (feval_exp e3 _). simpl in E3. destruct z; [|discriminate E3]. injection E3 as; subst.
    reflexivity.

    simpl. simpl in K. apply andb_prop in K. destruct K as [K1 K2].
    apply (IHe1 _ _ K1) in E1. destruct (feval_exp e1 _). simpl in E1. destruct z; [|discriminate E1]. injection E1 as; subst.
    apply (IHe2 _ _ K2) in E2. destruct (feval_exp e2 _). simpl in E2. destruct z; [|discriminate E2]. injection E2 as; subst.
    apply reduce_binop.

    simpl.
    apply (IHe _ _ K) in E1. destruct (feval_exp e _). simpl in E1. destruct z; [|discriminate E1]. injection E1 as; subst.
    apply reduce_unop.

    simpl.
    apply (IHe _ _ K) in E1. destruct (feval_exp e _). simpl in E1. destruct z; [|discriminate E1]. injection E1 as; subst.
    reflexivity.

    simpl. simpl in K. apply andb_prop in K. destruct K as [K1 K2].
    apply (IHe1 _ _ K1) in E1. subst u1.
    apply (IHe2 _ _ K2) in E2. subst u.
    reflexivity.

    discriminate K.

    simpl. simpl in K. apply andb_prop in K. destruct K as [K1 K]. simpl in K. apply andb_prop in K. destruct K as [K2 K3].
    apply (IHe1 _ _ K1) in E1. destruct (feval_exp e1 _). simpl in E1. destruct z; [|discriminate E1]. injection E1 as; subst.
    destruct n.
      apply (IHe3 _ _ K3) in E'. destruct (feval_exp e2 s). destruct (feval_exp e3 _). subst u. reflexivity.
      apply (IHe2 _ _ K2) in E'. destruct (feval_exp e2 _). destruct (feval_exp e3 _). subst u. reflexivity.

    simpl.
    apply (IHe _ _ K) in E1. destruct (feval_exp e _). simpl in E1. destruct z; [|discriminate E1]. injection E1 as; subst.
    reflexivity.

    simpl. simpl in K. apply andb_prop in K. destruct K as [K1 K2].
    apply (IHe1 _ _ K1) in E1. destruct (feval_exp e1 _). simpl in E1. destruct z; [|discriminate E1]. injection E1 as; subst.
    apply (IHe2 _ _ K2) in E2. destruct (feval_exp e2 _). simpl in E2. destruct z; [|discriminate E2]. injection E2 as; subst.
    reflexivity.
Qed.

Theorem memacc_exp_true:
  forall RW e s u (K: exp_known e = true) (E: eval_exp RW s e u),
  memacc_exp e RW s.
Proof.
  induction e; intros; try exact I;
    try (unfold exp_known in K; fold exp_known in K; apply andb_prop in K; destruct K as [K1 K2]);
    inversion E; subst;
    unfold memacc_exp; fold memacc_exp;
    try first [ eapply IHe; [ exact K | exact E1 ]
              | split; [ eapply IHe1; [ exact K1 | exact E1 ]
                       | eapply IHe2; [ exact K2 | exact E2 ] ] ].

  (* Load *)
  apply reduce_exp in E1; [|exact K1]. apply reduce_exp in E2; [|exact K2].
  apply (f_equal uvalue_of) in E1. apply (f_equal uvalue_of) in E2. rewrite can_uvalue_inv in E1,E2 by apply canonical_feval.
  unfold uvalue_of in E1,E2. rewrite <- E1, <- E2. exact R.

  (* Store *)
  apply andb_prop, proj1 in K2.
  apply reduce_exp in E1; [|exact K1]. apply reduce_exp in E2; [|exact K2].
  apply (f_equal uvalue_of) in E1. apply (f_equal uvalue_of) in E2. rewrite can_uvalue_inv in E1,E2 by apply canonical_feval.
  unfold uvalue_of in E1,E2. unfold memacc_exp. rewrite <- E1, <- E2. exact W.

  (* Let *)
  split.
    eapply IHe1. exact K1. exact E1.
    eapply IHe2. exact K2. apply reduce_exp in E1; [|exact K1]. rewrite <- E1. exact E2.

  (* Ite *)
  apply reduce_exp in E1; [|exact K1]. apply (f_equal uvalue_of) in E1. rewrite can_uvalue_inv in E1 by apply canonical_feval.
  rewrite <- E1. simpl. apply andb_prop in K2. destruct n1.
    eapply IHe3. exact (proj2 K2). exact E'.
    eapply IHe2. exact (proj1 K2). exact E'.
Qed.


(* With the above, we can now reduce common-case exec_stmt hypotheses into hypotheses of the
   form s' = ... /\ x' = ..., which allows us to infer the final store s' and exit state x'
   and substitute them away throughout the proof context. *)

Lemma reduce_seq_move:
  forall x1 (FIN: x1 <> Some Unfinished)
         RW s1 id t e q m s1' (XS: exec_stmt RW s1 (Seq (Move (Va id t) e) q) m s1' x1),
  if exp_known e then
    (let u := of_uvalue (feval_exp e s1) in exec_stmt RW (s1[id:=Some u]) q (pred m) s1' x1) /\
    memacc_exp e RW s1
  else
    exists u, exec_stmt RW (s1[id:=Some u]) q (pred m) s1' x1.
Proof.
  intros. inversion XS; subst. contradict FIN. reflexivity.
  inversion XS0; subst. contradict FIN. reflexivity.
  inversion XS1; subst.
  destruct (exp_known e) eqn:K.
    split.
      eapply reduce_exp in E. subst u. exact XS0. exact K.
      eapply memacc_exp_true. exact K. exact E.
    eexists. exact XS0.
Qed.

Lemma reduce_nop:
  forall x1 (FIN: x1 <> Some Unfinished)
         RW s1 m s1' (XS: exec_stmt RW s1 Nop m s1' x1),
  s1' = s1 /\ x1 = None.
Proof.
  intros. inversion XS; subst.
  contradict FIN. reflexivity.
  split; reflexivity.
Qed.

Lemma reduce_move:
  forall x1 (FIN: x1 <> Some Unfinished)
         RW s1 id t e m s1' (XS: exec_stmt RW s1 (Move (Va id t) e) m s1' x1),
  if exp_known e then
    ((let u := of_uvalue (feval_exp e s1) in s1' = s1[id:=Some u]) /\ x1 = None) /\
    memacc_exp e RW s1
  else exists u, (s1' = s1[id:=Some u] /\ x1 = None).
Proof.
  intros.
  inversion XS; subst. contradict FIN. reflexivity.
  destruct (exp_known e) eqn:K.
    split.
      eapply reduce_exp in E. rewrite E. split; reflexivity. exact K.
      eapply memacc_exp_true. exact K. exact E.
    exists u. split; reflexivity.
Qed.

Lemma reduce_jmp:
  forall x1 (FIN: x1 <> Some Unfinished)
         RW s1 e m s1' (XS: exec_stmt RW s1 (Jmp e) m s1' x1),
  if exp_known e then
    (s1' = s1 /\ x1 = Some (Exit (match feval_exp e s1 with VaU _ _ a _ => a end))) /\
    memacc_exp e RW s1
  else exists a, (s1' = s1 /\ x1 = Some (Exit a)).
Proof.
  intros. inversion XS; subst. contradict FIN. reflexivity.
  destruct (exp_known e) eqn:K.
    split.
      split. reflexivity.
      eapply reduce_exp in E; [|exact K].
      apply (f_equal uvalue_of) in E.
      rewrite can_uvalue_inv in E; [|apply canonical_feval].
      simpl in E. rewrite <- E. reflexivity.

      eapply memacc_exp_true. exact K. exact E.

    exists a. split; reflexivity.
Qed.

Lemma reduce_if:
  forall x1 (FIN: x1 <> Some Unfinished)
         RW s1 e q1 q2 m s1' (XS: exec_stmt RW s1 (If e q1 q2) m s1' x1),
  if exp_known e then
    (exec_stmt RW s1 (match feval_exp e s1 with VaU _ _ c _ => if c then q2 else q1 end) (pred m) s1' x1) /\
    memacc_exp e RW s1
  else
    exists (c:N), exec_stmt RW s1 (if c then q2 else q1) (pred m) s1' x1.
Proof.
  intros. inversion XS; subst. contradict FIN. reflexivity.
  destruct (exp_known e) eqn:K.
    split.
      eapply reduce_exp in E; [|exact K].
      apply (f_equal uvalue_of) in E.
      rewrite can_uvalue_inv in E; [|apply canonical_feval].
      rewrite <- E. simpl. destruct c; assumption.

      eapply memacc_exp_true. exact K. exact E.

    eexists. exact XS0.
Qed.

End FInterp.


(* Using the functional interpreter, we now define a set of tactics that reduce expressions to values,
   and statements to stores & exits.  These tactics are carefully implemented to avoid simplifying
   anything other than the machinery of the functional interpreter, so that Coq does not spin out of
   control attempting to execute the entire program.  Our objective is to infer a reasonably small,
   well-formed symbolic expression that captures the result of executing each assembly instruction.
   This result can be further reduced by the user (e.g., using "simpl") if desired.  Call-by-value
   strategy is used here, since our goal is usually to reduce as much as possible of the target
   expression, which might include arguments of an enclosing unexpandable function. *)

Ltac simpl_exp :=
  cbv beta iota zeta delta [ exp_known feval_exp feval_binop feval_unop memacc_exp
                             utowidth utobit uget of_uvalue uvalue_of ].

Tactic Notation "simpl_exp" "in" hyp(H) :=
  cbv beta iota zeta delta [ exp_known feval_exp feval_binop feval_unop memacc_exp
                             utowidth utobit uget of_uvalue uvalue_of ] in H.


(* Statement simplification most often gets stuck at variable-reads, since the full content of the
   store is generally not known (s is a symbolic expression).  We can often push past this obstacle
   by applying the update_updated and update_frame theorems to automatically infer that the values
   of variables not being read are irrelevant.  The "simpl_stores" tactic does so. *)

Remark if_N_same: forall A (n:N) (a:A), (if n then a else a) = a.
Proof. intros. destruct n; reflexivity. Qed.

Ltac simpl_stores :=
  repeat first [ rewrite update_updated | rewrite update_frame; [|discriminate 1] ];
  repeat rewrite if_N_same;
  repeat match goal with |- context [ update vareq ?S ?V ?U ] =>
    match S with context c [ update vareq ?T V _ ] => let r := context c[T] in
      replace (update vareq S V U) with (update vareq r V U) by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.

Tactic Notation "simpl_stores" "in" hyp(H) :=
  repeat first [ rewrite update_updated in H | rewrite update_frame in H; [|discriminate 1] ];
  repeat rewrite if_N_same in H;
  repeat match type of H with context [ update vareq ?S ?V ?U ] =>
    match S with context c [ update vareq ?T V _ ] => let r := context c[T] in
      replace (update vareq S V U) with (update vareq r V U) in H by
        (symmetry; repeat apply update_inner_same; apply update_cancel)
    end
  end.


(* To facilitate expression simplification, it is often convenient to first consolidate all information
   about known variable values into the expression to be simplified.  The "stock_store" tactic searches the
   proof context for hypotheses of the form "s var = value", where "var" is some variable appearing in the
   expression to be reduced and "s" is the store, and adds "s[var:=value]" to the expression. *)

Ltac stock_store :=
  lazymatch goal with |- exec_stmt _ _ ?Q _ _ _ => repeat
    match Q with context [ Va ?V ] =>
      lazymatch goal with |- exec_stmt _ ?S _ _ _ _ =>
        lazymatch S with context [ update vareq _ V _ ] => fail | _ =>
          erewrite (@store_upd_eq _ V) by (simpl_stores; eassumption)
        end
      end
    end
  | _ => fail "Goal is not of the form (exec_stmt ...)"
  end.

Tactic Notation "stock_store" "in" hyp(XS) :=
  lazymatch type of XS with exec_stmt _ _ ?Q _ _ _ => repeat
    match Q with context [ Va ?V ] =>
      lazymatch type of XS with exec_stmt _ ?S _ _ _ _ =>
        lazymatch S with context [ update vareq _ V _ ] => fail | _ =>
          erewrite (@store_upd_eq _ V) in XS by (simpl_stores; eassumption)
        end
      end
    end
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.


(* Replace any unresolved variable lookups as fresh Coq variables after functional evaluation. *)

Ltac destr_ugets H :=
  try (rewrite fold_uget in H; repeat rewrite fold_uget in H;
       repeat match type of H with context [ uget ?X ] =>
         let UGET := fresh "UGET" in
         let utyp := fresh "utyp" in let mem := fresh "mem" in let n := fresh "n" in let w := fresh "w" in
         destruct (uget X) as [utyp mem n w] eqn:UGET
       end).


(* Finally, simplifying a hypothesis of the form (exec_stmt ...) entails applying the functional
   interpreter to each statement in the sequence (usually a Move), using simpl_stores to try to
   infer any unresolved variable-reads, and repeating this until we reach a conditional or the
   end of the sequence.  (We don't attempt to break conditionals into cases, since often the user
   wants to decide which case distinction is best.) *)

Ltac nomemaccs T :=
  lazymatch T with NoMemAcc => idtac
  | if _ then ?E1 else ?E2 => nomemaccs E1; nomemaccs E2
  | ?E1 /\ ?E2 => nomemaccs E1; nomemaccs E2
  | _ => fail
  end.

Ltac destruct_memacc H :=
  lazymatch type of H with
  | _=_ /\ _=_ => idtac
  | exists _, _ => let u := fresh "u" in destruct H as [u H]; simpl_exp in H; simpl_stores in H
  | ?H1 /\ ?H1 =>
    lazymatch goal with
    | [ _:H1 |- _ ] => clear H
    | _ => apply proj1 in H; destruct_memacc H
    end
  | ?H1 /\ ?H2 =>
    lazymatch goal with
    | [ _:H1, _:H2 |- _ ] => clear H
    | [ _:H1 |- _ ] => apply proj2 in H; destruct_memacc H
    | [ _:H2 |- _ ] => apply proj1 in H; destruct_memacc H
    | _ => let H' := fresh "ACC" in destruct H as [H H']; destruct_memacc H; destruct_memacc H'
    end
  | ?T => try (nomemaccs T; clear H)
  end.

Ltac finish_simpl_stmt H :=
  simpl_exp in H; simpl_stores in H; destr_ugets H; unfold cast in H; destruct_memacc H.

Tactic Notation "simpl_stmt" "in" hyp(H) :=
  lazymatch type of H with exec_stmt _ _ _ _ _ ?X =>
    let K := fresh "FIN" in enough (K: X <> Some Unfinished); [
    repeat (apply reduce_seq_move in H; [|exact K]; finish_simpl_stmt H);
    first [ apply reduce_nop in H; [|exact K]; unfold cast in H
          | apply reduce_move in H; [|exact K]; finish_simpl_stmt H
          | apply reduce_jmp in H; [|exact K]; finish_simpl_stmt H
          | apply reduce_if in H; [|exact K];
            simpl_exp in H; simpl_stores in H; destr_ugets H; unfold cast in H;
            match type of H with
            | exists _, _ => let c := fresh "c" in
                             destruct H as [c H]; simpl_exp in H; simpl_stores in H; destr_ugets H
            | _ => destruct_memacc H
            end ];
    clear K |]
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.

(* Combining all of the above, our most typical simplification regimen first stocks the store
   of the exec_stmt with any known variable values from the context, then applies the functional
   interpreter, and then unfolds a few basic constants. *)

Tactic Notation "bsimpl" "in" hyp(H) := stock_store in H; simpl_stmt in H; unfold tobit in H.

End BAPInterp.

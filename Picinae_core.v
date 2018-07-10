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
   Core module:                                      MMMMMMMMMMMZMDMD77$.ZMZMM78
   * defines BAP IL syntax,                           MMMMMMMMMMMMMMMMMMMZOMMM+Z
   * core datatypes,                                   MMMMMMMMMMMMMMMMM^NZMMN+Z
   * and operational semantics.                         MMMMMMMMMMMMMMM/.$MZM8O+
                                                         MMMMMMMMMMMMMM7..$MNDM+
                                                          MMDMMMMMMMMMZ7..$DM$77
                                                           MMMMMMM+MMMZ7..7ZM~++
                                                            MMMMMMMMMMM7..ZNOOMZ
                                                             MMMMMMMMMM$.$MOMO=7
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

Require Import NArith.
Require Import ZArith.
Require Import FunctionalExtensionality.
Require Import Structures.Equalities.
Require Setoid.


(* First define the partial order of A-to-B partial functions ordered by subset. *)

Definition pfsub {A B:Type} (f g: A -> option B) : Prop :=
  forall x y, f x = Some y -> g x = Some y.

Notation "f ⊆ g" := (pfsub f g) (at level 70, right associativity).

Theorem pfsub_refl {A B}: forall (f:A->option B), f ⊆ f.
Proof. unfold pfsub. intros. assumption. Qed.

Theorem pfsub_antisym {A B}:
  forall (f g:A->option B), f ⊆ g -> g ⊆ f -> f = g.
Proof.
  unfold pfsub. intros f g FG GF. extensionality v.
  specialize (FG v). specialize (GF v). destruct (f v) as [b|].
    symmetry. apply FG. reflexivity.
    destruct (g v). apply GF. reflexivity. reflexivity.
Qed.

Theorem pfsub_trans {A B}:
  forall (f g h:A->option B), f ⊆ g -> g ⊆ h -> f ⊆ h.
Proof. unfold pfsub. intros f g h FG GH x y FX. apply GH,FG. assumption. Qed.

Theorem pfsub_contrapos {A B}:
  forall (f g: A -> option B) x, f ⊆ g -> g x = None -> f x = None.
Proof.
  unfold pfsub. intros f g x SS H. specialize (SS x). destruct (f x).
    symmetry. rewrite <- H. apply SS. reflexivity.
    reflexivity.
Qed.

Add Parametric Relation {A B:Type}: (A -> option B) pfsub
  reflexivity proved by pfsub_refl
  transitivity proved by pfsub_trans
as pfsubset.



(* Bitwidths are expressed as natural numbers. *)
Definition bitwidth := N.
Bind Scope N_scope with bitwidth.

(* Memory addresses are expressed as natural numbers. *)
Definition addr := N.
Bind Scope N_scope with addr.

(* Runtime values are integers or memory states. *)
Inductive value : Type :=
| VaN (n:N) (w:bitwidth)
| VaM (m:addr->N) (w:bitwidth).



(* Each Picinae instantiation takes a machine architecture as input, expressed as
   a module that defines a type for IL variables, the bitwidth of memory contents
   (usually 8 for bytes), and two propositions that express the CPU's memory
   access model. Specifically, mem_readable and mem_writable must be propositions
   that are satisfied when an address is readable/writable in the context of a
   given store.  The definitions of these propositions can be mostly arbitrary,
   but they must reason monotonically about store content (e.g., access must be
   denied if the store variables that are the basis for the decision are
   undefined).  This ensures that learning more information about a computation
   state never invalidates conclusions proved using less knowledge. *)
Module Type Architecture.
  Declare Module Var : UsualDecidableType.
  Definition var := Var.t.
  Definition store := var -> option value.

  Parameter mem_bits: positive.
  Parameter mem_readable: store -> addr -> Prop.
  Parameter mem_writable: store -> addr -> Prop.

  Axiom mem_readable_mono:
    forall s1 s2 a, s1 ⊆ s2 -> mem_readable s1 a -> mem_readable s2 a.
  Axiom mem_writable_mono:
    forall s1 s2 a, s1 ⊆ s2 -> mem_writable s1 a -> mem_writable s2 a.
End Architecture.


Module PicinaeCore (Arch: Architecture).

Export Arch.
Open Scope N.
Definition vareq := Var.eq_dec.
Definition Mb := Npos mem_bits.

(* An IL expression type is a number of bitwidth w, or a memory state with
   addresses of bitwidth w.  (The bitwidth of memory contents is architecture-
   specific, but is usually bitwidth 8.) *)
Inductive typ : Type :=
| NumT (w:bitwidth)
| MemT (w:bitwidth).

(* Endianness: *)
Inductive endianness : Type :=
| BigE
| LittleE.

(* IL binary operators *)
Inductive binop_typ : Type :=
| OP_PLUS (* Integer addition (commutative, associative) *)
| OP_MINUS (* Subtract second integer from first. *)
| OP_TIMES (* Integer multiplication (commutative, associative)*)
| OP_DIVIDE (* Unsigned integer division *)
| OP_SDIVIDE (* Signed integer division *)
| OP_MOD (* Unsigned modulus *)
| OP_SMOD (* Signed modulus *)
| OP_LSHIFT (* Left shift *)
| OP_RSHIFT (* Right shift, fill with 0 *)
| OP_ARSHIFT (* Right shift, sign extend *)
| OP_AND (* Bitwise and (commutative, associative) *)
| OP_OR (* Bitwise or (commutative, associative) *)
| OP_XOR (* Bitwise xor (commutative, associative) *)
| OP_EQ (* Equals (commutative) (associative on booleans) *)
| OP_NEQ (* Not equals (commutative) (associative on booleans) *)
| OP_LT (* Unsigned less than *)
| OP_LE (* Unsigned less than or equal to *)
| OP_SLT (* Signed less than *)
| OP_SLE (* Signed less than or equal to *).

(* IL unary operators *)
Inductive unop_typ : Type :=
| OP_NEG (* Negate (2's complement) *)
| OP_NOT (* Bitwise not *).

(* IL cast operators *)
Inductive cast_typ : Type :=
| CAST_LOW (* Narrowing cast. Keeps the low bits. *)
| CAST_HIGH (* Narrowing cast. Keeps the high bits. *)
| CAST_SIGNED (* Sign-extending widening cast. *)
| CAST_UNSIGNED (* 0-padding widening cast. *).

(* IL expression syntax *)
Inductive exp : Type :=
| Var (v:var)
| Word (n:N) (w:bitwidth)
| Load (e1 e2:exp) (en:endianness) (w:bitwidth)  (* Load(mem,addr,endian,BYTEwidth) *)
| Store (e1 e2 e3:exp) (en:endianness) (w:bitwidth)  (* Store(mem,addr,val,endian,BYTEwidth) *)
| BinOp (b:binop_typ) (e1 e2:exp)
| UnOp (u:unop_typ) (e:exp)
| Cast (c:cast_typ) (w:bitwidth) (e:exp) (* Cast to a new width. *)
| Let (v:var) (e1 e2:exp)
| Unknown (t:typ)
(* Expression types below here are just syntactic sugar for the above. *)
| Ite (e1 e2 e3:exp)
| Extract (n1 n2:N) (e:exp) (* Extract hbits to lbits of e (NumT type). *)
| Concat (e1 e2:exp) (* Concat two NumT expressions together. *).

(* The BIL specification formalizes statement sequences as statement lists;
   however, that approach makes Coq proofs very cumbersome because it forces
   reasoning about mutually recursive datatypes (statements that contain lists
   that contain statements).  To avoid this, we here instead define statements
   to include binary sequences (Seq) and nullary sequences (Nop).  Together
   these are equivalent to lists, but keep everything within one datatype. *)

Inductive stmt : Type :=
| Nop (* Do nothing. *)
| Move (v:var) (e:exp)  (* Assign a value to a var. *)
| Jmp (e:exp) (* Jump to a label/address. *)
| CpuExn (i:N) (* CPU Exception (numbered) *)
| Seq (q1 q2:stmt) (* sequence: q1 then q2 *)
| While (e:exp) (q:stmt) (* While e<>0 do q *)
| If (e:exp) (q1 q2:stmt) (* If e<>0 then q1 else q2 *).

(* Convenient notation for sequence:
   Note that the sequence infix operator $; is RIGHT-associative.  This is critical
   because it allows sequences to be easily analyzed in forward order, which is the
   natural order in which most proofs progress. *)
Delimit Scope stmt_scope with stmt.
Bind Scope stmt_scope with stmt.
Notation " s1 $; s2 " := (Seq s1 s2) (at level 75, right associativity) : stmt_scope.

(* Programs map addresses to an instruction size sz and an IL statement q
   that encodes the instruction.  If q falls through, control flows to
   address a+sz.  We express programs as functions instead of lists in order
   to correctly model architectures and programs with unaligned instructions
   (or those whose alignments are unknown prior to the analysis). *)
Definition program := addr -> option (N * stmt).

(* Memory is well-typed if every address holds a byte. *)
Definition welltyped_memory (m:addr->N) : Prop :=
  forall a, m a < 2^Mb.

(* A constant's type is its bitwidth, and a memory's type is the
   bitwidth of its addresses. *)
Inductive typof_val: value -> typ -> Prop :=
| TVN (n:N) (w:bitwidth) (LT: n < 2^w): typof_val (VaN n w) (NumT w)
| TVM (m:addr->N) (w:bitwidth) (WTM: welltyped_memory m): typof_val (VaM m w) (MemT w).

(* Reinterpret an unsigned integer as a 2's complement signed integer. *)
Definition toZ (w:bitwidth) (n:N) : Z :=
  if N.testbit n (N.pred w) then Z.of_N n - Z.of_N (2^w) else Z.of_N n.

(* Convert an integer back to 2's complement form. *)
Definition ofZ (w:bitwidth) (z:Z) : N :=
  Z.to_N (z mod (Z.of_N (2^w))).

(* Perform a signed operation by converting the unsigned operands to signed
   operands, applying the signed operation, and then converting the signed
   result back to unsigned. *)
Definition sbop (bop:Z->Z->Z) (w:bitwidth) (n1 n2:N) : N :=
  ofZ w (bop (toZ w n1) (toZ w n2)).

(* Compute an arithmetic shift-right (sign-extending shift-right). *)
Definition ashiftr (w:bitwidth) := sbop Z.shiftr w.

(* Force a result to a given width by dropping the high bits. *)
Definition towidth (w:bitwidth) (n:N) : value := VaN (n mod (2^w)) w.
Global Arguments towidth / w n.

(* Force a result to a boolean value (1-bit integer). *)
Definition tobit (b:bool) : value := VaN (N.b2n b) 1.
Global Arguments tobit / b.

(* Perform signed less-than comparison. *)
Definition slt (w n1 n2:N) : bool :=
  Z.ltb (toZ w n1) (toZ w n2).

(* Perform signed less-or-equal comparison. *)
Definition sle (w n1 n2:N) : bool :=
  Z.leb (toZ w n1) (toZ w n2).

(* Perform a binary operation (using the above as helper functions). *)
Definition eval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : value :=
  match bop with
  | OP_PLUS => towidth w (n1+n2)
  | OP_MINUS => towidth w (2^w + n1 - n2)
  | OP_TIMES => towidth w (n1*n2)
  | OP_DIVIDE => VaN (n1/n2) w
  | OP_SDIVIDE => VaN (sbop Z.quot w n1 n2) w
  | OP_MOD => VaN (N.modulo n1 n2) w
  | OP_SMOD => VaN (sbop Z.rem w n1 n2) w
  | OP_LSHIFT => towidth w (N.shiftl n1 n2)
  | OP_RSHIFT => VaN (N.shiftr n1 n2) w
  | OP_ARSHIFT => VaN (ashiftr w n1 n2) w
  | OP_AND => VaN (N.land n1 n2) w
  | OP_OR => VaN (N.lor n1 n2) w
  | OP_XOR => VaN (N.lxor n1 n2) w
  | OP_EQ => tobit (n1 =? n2)
  | OP_NEQ => tobit (negb (n1 =? n2))
  | OP_LT => tobit (n1 <? n2)
  | OP_LE => tobit (n1 <=? n2)
  | OP_SLT => tobit (slt w n1 n2)
  | OP_SLE => tobit (sle w n1 n2)
  end.

(* Perform a unary operation. *)
Definition eval_unop (uop:unop_typ) (n:N) (w:bitwidth) : value :=
  match uop with
  | OP_NEG => towidth w (2^w - n)
  | OP_NOT => VaN (N.lnot n w) w
  end.

(* Return a new store that is like store f except with variable x
   remapped to value y. *)
Definition update {A B:Type} (eq:forall (a b:A), {a=b}+{a<>b}) (f:A->B) (x:A) (y:B) (z:A) : B :=
  if eq z x then y else f z.

Notation "f [ x := y ]" := (update vareq f x y) (at level 50, left associativity).


(* Perform a cast operation. *)
Definition scast (w w':bitwidth) (n:N) : N :=
  ofZ w' (toZ w n).

Definition cast (c:cast_typ) (w w':bitwidth) (n:N) : N :=
  match c with
  | CAST_UNSIGNED => n
  | CAST_SIGNED => scast w w' n
  | CAST_HIGH => N.shiftr n (w - w')
  | CAST_LOW => n mod 2^w'
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
Definition getmem (e:endianness) (len:bitwidth) (mem:addr->N) : addr -> N :=
  N.recursion (fun _ => N0) (match e with BigE => getmem_big | LittleE => getmem_little end mem) len.

(* Store v as a len-byte, e-endian number at address a of memory m. *)
Definition setmem_big len rec mem a v : addr -> N :=
  rec (update N.eq_dec mem a (N.shiftr v (Mb*len))) (N.succ a) (v mod 2^(Mb*len)).
Definition setmem_little len rec mem a v : addr -> N :=
  rec (update N.eq_dec mem a (match len with N0 => v | Npos _ => v mod 2^Mb end)) (N.succ a) (N.shiftr v Mb).
Definition setmem (e:endianness) (len:bitwidth) : (addr->N) -> addr -> N -> (addr -> N) :=
  N.recursion (fun m _ _ => m) (match e with BigE => setmem_big | LittleE => setmem_little end) len.



Section InterpreterEngine.

(* A program exits by hitting a computation limit (Unfinished), jumping to an address
   outside the program (Exit), or throwing an exception (Exn). *)
Inductive exit : Type := Unfinished | Exit (a:addr) | Exn (i:N).

(* Evaluate an expression in the context of a store, returning a value.  Note
   that the semantics of EUnknown are non-deterministic: an EUnknown expression
   evaluates to any well-typed value.  Thus, eval_exp and the other interpreter
   semantic definitions that follow should be considered statements of
   possibility in an alethic modal logic. *)
Inductive eval_exp (s:store): exp -> value -> Prop :=
| EVar (v:var) (u:value) (SV: s v = Some u):
       eval_exp s (Var v) u
| EWord (n:N) (w:bitwidth): eval_exp s (Word n w) (VaN n w)
| ELoad (e1 e2:exp) (en:endianness) (len mw:bitwidth) (m:addr->N) (a:addr)
        (E1: eval_exp s e1 (VaM m mw)) (E2: eval_exp s e2 (VaN a mw))
        (R: forall n, n < len -> mem_readable s (a+n)):
        eval_exp s (Load e1 e2 en len) (VaN (getmem en len m a) (Mb*len))
| EStore (e1 e2 e3:exp) (en:endianness) (len mw:bitwidth) (m:addr->N) (a:addr)
         (v:N) (E1: eval_exp s e1 (VaM m mw))
         (E2: eval_exp s e2 (VaN a mw)) (E3: eval_exp s e3 (VaN v (Mb*len)))
         (W: forall n, n < len -> mem_writable s (a+n)):
         eval_exp s (Store e1 e2 e3 en len) (VaM (setmem en len m a v) mw)
| EBinOp (bop:binop_typ) (e1 e2:exp) (n1 n2:N) (w:bitwidth)
         (E1: eval_exp s e1 (VaN n1 w)) (E2: eval_exp s e2 (VaN n2 w)):
         eval_exp s (BinOp bop e1 e2) (eval_binop bop w n1 n2)
| EUnOp (uop:unop_typ) (e1:exp) (n1:N) (w1:bitwidth)
        (E1: eval_exp s e1 (VaN n1 w1)):
        eval_exp s (UnOp uop e1) (eval_unop uop n1 w1)
| ECast (c:cast_typ) (w w':bitwidth) (e1:exp) (n:N)
        (E1: eval_exp s e1 (VaN n w)):
        eval_exp s (Cast c w' e1) (VaN (cast c w w' n) w')
| ELet (v:var) (e1 e2:exp) (u1 u2:value)
       (E1: eval_exp s e1 u1) (E2: eval_exp (update vareq s v (Some u1)) e2 u2):
       eval_exp s (Let v e1 e2) u2
| EUnknown (t:typ) (u:value)
           (TV: typof_val u t):
           eval_exp s (Unknown t) u
| EIte (e1 e2 e3:exp) (n1:N) (w1:bitwidth) (u':value)
       (E1: eval_exp s e1 (VaN n1 w1))
       (E': eval_exp s (match n1 with N0 => e3 | _ => e2 end) u'):
       eval_exp s (Ite e1 e2 e3) u'
| EExtract (w n1 n2:bitwidth) (e1:exp) (n:N)
           (E1: eval_exp s e1 (VaN n w)):
           eval_exp s (Extract n1 n2 e1) (VaN (cast CAST_HIGH (N.succ n1) (N.succ (n1-n2))
                                                 (cast CAST_LOW w (N.succ n1) n)) (N.succ (n1-n2)))
| EConcat (e1 e2:exp) (n1 w1 n2 w2:N)
          (E1: eval_exp s e1 (VaN n1 w1)) (E2: eval_exp s e2 (VaN n2 w2)):
          eval_exp s (Concat e1 e2) (VaN (N.lor (N.shiftl n1 w2) n2) (w1+w2)).

(* Execute an IL statement with recursion depth limit n, returning a new store
   and possibly an exit (if the statement exited prematurely).  "None" is
   returned if the statement finishes and falls through.  "Some Unfinished"
   is returned if the statement requires more than n steps of computation
   to complete. *)
Inductive exec_stmt (s:store): stmt -> nat -> store -> option exit -> Prop :=
| XZero q: exec_stmt s q O s (Some Unfinished)
| XNop n: exec_stmt s Nop (S n) s None
| XMove n v e u (E: eval_exp s e u):
    exec_stmt s (Move v e) (S n) (update vareq s v (Some u)) None
| XJmp n e a w (E: eval_exp s e (VaN a w)):
    exec_stmt s (Jmp e) (S n) s (Some (Exit a))
| XExn n i: exec_stmt s (CpuExn i) (S n) s (Some (Exn i))
| XSeq1 n q1 q2 s' x (XS: exec_stmt s q1 n s' (Some x)):
    exec_stmt s (Seq q1 q2) (S n) s' (Some x)
| XSeq2 n q1 q2 s2 s' x' (XS1: exec_stmt s q1 n s2 None) (XS1: exec_stmt s2 q2 n s' x'):
    exec_stmt s (Seq q1 q2) (S n) s' x'
| XWhile n e q s' x (XS: exec_stmt s (If e (Seq q (While e q)) Nop) n s' x):
    exec_stmt s (While e q) (S n) s' x
| XIf n e q1 q2 c s' x
      (E: eval_exp s e (VaN c 1))
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

End PicinaeCore.

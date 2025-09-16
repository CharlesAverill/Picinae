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
   Core module:                                      MMMMMMMMMMMZMDMD77$.ZMZMM78
   * defines Picinae IL syntax,                       MMMMMMMMMMMMMMMMMMMZOMMM+Z
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
Require Import List.
Require Import Structures.Equalities.
Open Scope N.


(* Bitwidths, addresses, and the entire memory state are each expressed as
   Coq unsigned binary numbers. *)
Definition bitwidth := N.
Definition addr := N.
Definition memory := N.

(* Introduce a typeclass for equality decision procedures, so that we can
   henceforth refer to instances of types that instantiate the typeclass
   as "equal" without explicitly supplying the equality decision procedure. *)
Class EqDec A : Type := { iseq: forall (a b:A), {a=b}+{a<>b} }.
Arguments iseq {A EqDec} a b : simpl never.
Notation "x == y" := (iseq x y) (at level 70, no associativity).
#[export] Instance NEqDec : EqDec N := { iseq := N.eq_dec }.

(* When there is an equality decision procedure for a function f's domain,
   we can "update" f by remapping a domain element x to a new co-domain
   element y. *)
Definition update {A B:Type} {_: EqDec A} (f:A->B) (x:A) (y:B) (x0:A) : B :=
  if x0 == x then y else f x0.

(* Notation f[x:=y] means (update f x y) *)
Notation "f [ x := y ]" := (update f x y) (at level 50, left associativity, format "f '/' [ x  :=  y ]").

(* Define w-bit modular subtraction. *)
Definition msub w x y := (x + (2^w - y mod 2^w)) mod 2^w.

(* Reinterpret an unsigned integer as a two's complement signed integer. *)
Definition canonicalZ w z := ((z + 2^Z.pred w) mod 2^w - 2^Z.pred w)%Z.
Definition toZ (w:bitwidth) (n:N) : Z := canonicalZ (Z.of_N w) (Z.of_N n).

(* Convert an integer back to two's complement form. *)
Definition ofZ (w:bitwidth) (z:Z) := Z.to_N (z mod (2^Z.of_N w)).

(* Two's complement numbers of width w have values within the interval
   [ -2^(w-1), 2^(w-1) ), except that we adopt the convention that
   zero-bitwidth numbers always have value zero.  (Zero-bitwidth numbers
   occasionally appear in the context of bitwidth-subtraction, which can
   yield a difference of zero bits holding a value of zero.) *)
Definition signed_range w z :=
  (-(2^Z.pred (Z.of_N w)) <= z < 2^Z.of_N (N.pred w))%Z.

(* Perform a signed operation by converting the unsigned operands to signed
   operands, applying the signed operation, and then converting the signed
   result back to unsigned. *)
Definition sbop1 bop w n1 n2 := ofZ w (bop (toZ w n1) (Z.of_N n2)).
Definition sbop2 bop w n1 n2 := ofZ w (bop (toZ w n1) (toZ w n2)).

(* Compute an arithmetic shift-right (sign-extending shift-right). *)
Definition ashiftr w := sbop1 Z.shiftr w.

(* Perform signed less-than comparison. *)
Definition slt w n1 n2 := Z.ltb (toZ w n1) (toZ w n2).

(* Perform signed less-or-equal comparison. *)
Definition sle w n1 n2 := Z.leb (toZ w n1) (toZ w n2).

(* Unsigned cast: extract bits i to i+j-1 of an unsigned binary number. *)
Definition xbits n i j := (N.shiftr n i) mod 2^(j - i).
Arguments xbits / !n !i !j.

(* Concatenate high bits n1 onto width-i low bits n2 *)
Definition cbits n1 i n2 := N.lor (N.shiftl n1 i) n2.
Arguments cbits / !n1 !i !n2.

(* Signed cast: extract the low w' bits of a w-width signed number, preserving sign *)
Definition scast w w' n := ofZ w' (toZ w n).

(* Endianness: *)
Inductive endianness : Type := BigE | LittleE.

(* Memory accessor functions getmem and setmem read/store w-bit numbers to/from
   memory.  Since w could be large on some architectures, we express both as
   recursions over N, using Peano recursion (P w -> P (N.succ w)).  Proofs must
   therefore typically use the N.peano_ind inductive principle to reason about
   them.  (Picinae_theory provides machinery for doing so.)  These functions
   are also carefully defined to behave reasonably when the value being read/
   stored wraps around the end of the virtual address space.  In that case,
   the extra bytes are stored into low memory.  This behavior is useful because
   it facilitates theorems involving modular arithmetic on addresses. *)

(* Interpret a number N as an entire virtual address space. *)
Definition getbyte (m:memory) (a:addr) (w:bitwidth) :=
  xbits m ((a mod 2^w)*8) (N.succ (a mod 2^w) * 8).
Definition setbyte (m:memory) (a:addr) (n:N) (w:bitwidth) :=
  N.lor (N.ldiff m (N.shiftl (N.ones 8) ((a mod 2^w) * 8)))
        (N.shiftl (n mod 2^8) ((a mod 2^w)*8)).

(* Interpret len bytes at address a of memory m as an e-endian number. *)
Definition getmem_big w m len rec a := N.lor (rec (N.succ a)) (N.shiftl (getbyte m a w) (len*8)).
Definition getmem_little w m (len:bitwidth) rec a := N.lor (getbyte m a w) (N.shiftl (rec (N.succ a)) 8).
Definition getmem (w:bitwidth) (e:endianness) (len:bitwidth) (m:memory) : addr -> N :=
  N.recursion (fun _ => N0) (match e with BigE => getmem_big | LittleE => getmem_little end w m) len.

(* Store v as a len-byte, e-endian number at address a of memory m. *)
Definition setmem_big w len rec m a v : N :=
  rec (setbyte m a (N.shiftr v (len*8)) w) (N.succ a) (v mod 2^(len*8)).
Definition setmem_little w (len:N) rec m a v : N :=
  rec (setbyte m a v w) (N.succ a) (N.shiftr v 8).
Definition setmem (w:bitwidth) (e:endianness) (len:bitwidth) : memory -> addr -> N -> memory :=
  N.recursion (fun m _ _ => m) (match e with BigE => setmem_big | LittleE => setmem_little end w) len.

(* IL binary operators *)
Inductive binop_typ : Type :=
| OP_PLUS (* Integer addition *)
| OP_MINUS (* Subtract second integer from first. *)
| OP_TIMES (* Integer multiplication *)
| OP_DIVIDE (* Unsigned integer division *)
| OP_SDIVIDE (* Signed integer division *)
| OP_MOD (* Unsigned modulus *)
| OP_SMOD (* Signed modulus *)
| OP_LSHIFT (* Left shift *)
| OP_RSHIFT (* Right shift, fill with 0 *)
| OP_ARSHIFT (* Right shift, sign extend *)
| OP_AND (* Bitwise and *)
| OP_OR (* Bitwise or *)
| OP_XOR (* Bitwise xor *)
| OP_EQ (* Equals *)
| OP_NEQ (* Not equals *)
| OP_LT (* Unsigned less than *)
| OP_LE (* Unsigned less than or equal to *)
| OP_SLT (* Signed less than *)
| OP_SLE (* Signed less than or equal to *).

(* IL unary operators *)
Inductive unop_typ : Type :=
| OP_NEG (* Negate (2's complement) *)
| OP_NOT (* Bitwise not *)
| OP_POPCOUNT (* Count 1 bits *)
| OP_BITWIDTH (* Log2 rounded up *).

(* IL bitwidth cast operators *)
Inductive cast_typ : Type :=
| CAST_LOW (* Narrowing cast. Keeps the low bits. *)
| CAST_HIGH (* Narrowing cast. Keeps the high bits. *)
| CAST_SIGNED (* Sign-extending widening cast. *)
| CAST_UNSIGNED (* 0-padding widening cast. *).

(* Perform a binary operation. *)
Definition eval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : N :=
  match bop with
  | OP_PLUS => (n1+n2) mod 2^w
  | OP_MINUS => msub w n1 n2
  | OP_TIMES => (n1*n2) mod 2^w
  | OP_DIVIDE => n1/n2
  | OP_SDIVIDE => sbop2 Z.quot w n1 n2
  | OP_MOD => N.modulo n1 n2
  | OP_SMOD => sbop2 Z.rem w n1 n2
  | OP_LSHIFT => (N.shiftl n1 n2) mod 2^w
  | OP_RSHIFT => N.shiftr n1 n2
  | OP_ARSHIFT => ashiftr w n1 n2
  | OP_AND => N.land n1 n2
  | OP_OR => N.lor n1 n2
  | OP_XOR => N.lxor n1 n2
  | OP_EQ => N.b2n (n1 =? n2)
  | OP_NEQ => N.b2n (negb (n1 =? n2))
  | OP_LT => N.b2n (n1 <? n2)
  | OP_LE => N.b2n (n1 <=? n2)
  | OP_SLT => N.b2n (slt w n1 n2)
  | OP_SLE => N.b2n (sle w n1 n2)
  end.

(* The bitwidth of the result of a binary operation *)
Definition widthof_binop (bop:binop_typ) (w:bitwidth) : bitwidth :=
  match bop with
  | OP_PLUS | OP_MINUS | OP_TIMES | OP_DIVIDE | OP_SDIVIDE | OP_MOD | OP_SMOD
  | OP_LSHIFT | OP_RSHIFT | OP_ARSHIFT | OP_AND | OP_OR | OP_XOR => w
  | OP_EQ | OP_NEQ | OP_LT | OP_LE | OP_SLT | OP_SLE => 1
  end.

(* Count 1-bits *)
Fixpoint Pos_popcount p := match p with
| xH => xH | xO q => Pos_popcount q | xI q => Pos.succ (Pos_popcount q) end.
Definition popcount n := match n with N0 => N0 | N.pos p => N.pos (Pos_popcount p) end.

(* Perform a unary operation. *)
Definition eval_unop (uop:unop_typ) (n:N) (w:bitwidth) : N :=
  match uop with
  | OP_NEG => msub w 0 n
  | OP_NOT => N.lnot n w
  | OP_POPCOUNT => popcount n
  | OP_BITWIDTH => N.size n
  end.

(* Cast a numeric value to a new bitwidth. *)
Definition cast (c:cast_typ) (w w':bitwidth) (n:N) : N :=
  match c with
  | CAST_UNSIGNED => n
  | CAST_SIGNED => scast w w' n
  | CAST_HIGH => N.shiftr n (w - w')
  | CAST_LOW => n mod 2^w'
  end.



(* An execution exits an instruction by jumping to an address (Addr),
   or raising an exception (Raise). *)
Inductive exit : Type := Addr (a:addr) | Raise (i:N).

(* Helper function to convert fall-throughs to exits: *)
Definition exitof (a:addr) (sx:option exit) : exit :=
  match sx with None => Addr a | Some x => x end.

(* Convert a list of states into a list of adjecent state-pairs. *)
Definition stepsof {A} (l:list A) := List.combine l (List.tl l).
Arguments stepsof {A} / !l.

(* Starts of traces are last elements of lists. *)
Definition startof {A} := @List.last A.
Definition ostartof {A} (l:list A) := match l with nil => None | a::t => Some (startof t a) end.
Definition start_state {A} t (xs: exit * A) := snd (startof t xs).


(* Each Picinae instantiation takes a machine architecture as input, expressed as
   a module that defines a type "var" for IL variables, a typing context "typctx"
   that defines the type of each IL variable, the bitwidth mem_bits of memory reads
   (usually 8 for byte-granularity), and the CPU's memory access model expressed as
   propositions mem_readable and mem_writable that are satisfied when an address is
   readable/writable in the context of a given store. *)
Module Type Architecture.
  Declare Module Var : UsualDecidableType.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.

  Parameter archtyps : typctx.
  Parameter mem_readable: store -> addr -> Prop.
  Parameter mem_writable: store -> addr -> Prop.
End Architecture.


(* A PicinaeCore module builds the syntax and operational semantics of an IL
   described by an Architecture. *)
Module Type PICINAE_CORE (Arch: Architecture).

Import Arch.
Definition vareq := Var.eq_dec.
Definition vareqb v1 v2 := if vareq v1 v2 then true else false.
#[export] Instance VarEqDec : EqDec var := { iseq := vareq }.

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
| Unknown (w:bitwidth)
| Ite (e1 e2 e3:exp)
| Extract (n1 n2:N) (e:exp) (* Extract hbits to lbits of e (NumT type). *)
| Concat (e1 e2:exp) (* Bit-concat two NumT expressions together. *).

(* The BIL specification formalizes statement sequences as statement lists;
   however, that approach makes Coq proofs very cumbersome because it forces
   reasoning about mutually recursive datatypes (statements that contain lists
   that contain statements).  To avoid this, we here instead define statements
   to include binary sequences (Seq) and nullary sequences (Nop).  Together
   these are equivalent to lists, but keep everything within one datatype.

   BIL's while-loops are encoded as repeat (Rep) loops, which enforce loop
   boundedness.  A BIL "while e do q" loop that has a bound n on the number
   of iterations can therefore be encoded as (Rep n (If e q Nop)). *)

Inductive stmt : Type :=
| Nop (* Do nothing. *)
| Move (v:var) (e:exp)  (* Assign a value to a var. *)
| Jmp (e:exp) (* Jump to a label/address. *)
| Exn (i:N) (* CPU Exception (numbered) *)
| Seq (q1 q2:stmt) (* sequence: q1 then q2 *)
| If (e:exp) (q1 q2:stmt) (* If e<>0 then q1 else q2 *)
| Rep (e:exp) (q:stmt) (* Repeat q for e iterations *).

(* Programs map addresses to an instruction size sz and an IL statement q
   that encodes the instruction.  If q falls through, control flows to
   address a+sz.  We express programs as functions instead of lists in order
   to correctly model architectures and programs with unaligned instructions
   (or those whose alignments are unknown prior to the analysis).  Program
   functions additionally accept a store as input, in order to (optionally)
   support self-modifying code. *)
Definition program := store -> addr -> option (N * stmt).


Section InterpreterEngine.

(* Evaluate an expression in the context of a store, returning a value and its type.
   The semantics of EUnknown are non-deterministic: an EUnknown expression
   evaluates to any well-typed number.  Thus, eval_exp and the other interpreter
   semantic definitions that follow formalize statements of possibility in an
   alethic modal logic. *)
Inductive eval_exp (c:typctx) (s:store): exp -> N -> bitwidth -> Prop :=
| EVar v w (TYP: c v = Some w): eval_exp c s (Var v) (s v) w
| EWord n w: eval_exp c s (Word n w) n w
| ELoad e1 e2 en len w m a
        (E1: eval_exp c s e1 m (2^w*8)) (E2: eval_exp c s e2 a w)
        (R: forall n, n < len -> mem_readable s ((a+n) mod 2^w)):
        eval_exp c s (Load e1 e2 en len) (getmem w en len m a) (len*8)
| EStore e1 e2 e3 en len w m a v
         (E1: eval_exp c s e1 m (2^w*8)) (E2: eval_exp c s e2 a w)
         (E3: eval_exp c s e3 v (len*8))
         (W: forall n, n < len -> mem_writable s ((a+n) mod 2^w)):
         eval_exp c s (Store e1 e2 e3 en len) (setmem w en len m a v) (2^w*8)
| EBinOp bop e1 e2 n1 n2 w (E1: eval_exp c s e1 n1 w) (E2: eval_exp c s e2 n2 w):
         eval_exp c s (BinOp bop e1 e2) (eval_binop bop w n1 n2) (widthof_binop bop w)
| EUnOp uop e1 n1 w (E1: eval_exp c s e1 n1 w):
        eval_exp c s (UnOp uop e1) (eval_unop uop n1 w) w
| ECast ct w w' e1 n (E1: eval_exp c s e1 n w):
        eval_exp c s (Cast ct w' e1) (cast ct w w' n) w'
| ELet v e1 e2 n w n' w' (E1: eval_exp c s e1 n w)
       (E2: eval_exp (update c v (Some w)) (update s v n) e2 n' w'):
       eval_exp c s (Let v e1 e2) n' w'
| EUnknown n w (LT: n < 2^w): eval_exp c s (Unknown w) n w
| EIte e1 e2 e3 n1 n2 n3 w w' (E1: eval_exp c s e1 n1 w)
       (E2: eval_exp c s e2 n2 w') (E3: eval_exp c s e3 n3 w'):
       eval_exp c s (Ite e1 e2 e3) (match n1 with N0 => n3 | _ => n2 end) w'
| EExtract w n1 n2 e1 n (E1: eval_exp c s e1 n w):
           eval_exp c s (Extract n1 n2 e1) (xbits n n2 (N.succ n1)) (N.succ n1 - n2)
| EConcat e1 e2 n1 w1 n2 w2 (E1: eval_exp c s e1 n1 w1) (E2: eval_exp c s e2 n2 w2):
          eval_exp c s (Concat e1 e2) (cbits n1 w2 n2) (w1+w2).

(* Execute an IL statement, returning a new store and possibly an exit (if the
   statement exited prematurely).  "None" is returned if the statement finishes
   and falls through. *)
Inductive exec_stmt (c:typctx) (s:store): stmt -> typctx -> store -> option exit -> Prop :=
| XNop: exec_stmt c s Nop c s None
| XMove v e n w (E: eval_exp c s e n w):
    exec_stmt c s (Move v e) (update c v (Some w)) (update s v n) None
| XJmp e a w (E: eval_exp c s e a w):
    exec_stmt c s (Jmp e) c s (Some (Addr a))
| XExn i: exec_stmt c s (Exn i) c s (Some (Raise i))
| XSeq1 q1 q2 c' s' x (XS: exec_stmt c s q1 c' s' (Some x)):
    exec_stmt c s (Seq q1 q2) c' s' (Some x)
| XSeq2 q1 q2 c2 s2 c' s' x' (XS1: exec_stmt c s q1 c2 s2 None) (XS1: exec_stmt c2 s2 q2 c' s' x'):
    exec_stmt c s (Seq q1 q2) c' s' x'
| XIf e q1 q2 b c' s' x
      (E: eval_exp c s e b 1)
      (XS: exec_stmt c s (match b with N0 => q2 | _ => q1 end) c' s' x):
    exec_stmt c s (If e q1 q2) c' s' x
| XRep n w e q c' s' x
       (E: eval_exp c s e n w) (XS: exec_stmt c s (N.iter n (Seq q) Nop) c' s' x):
    exec_stmt c s (Rep e q) c' s' x.

(* A program execution is a trace of consecutive statement executions. *)
Definition trace := list (exit * store).

Definition reset_vars (c:typctx) (s s':store) v :=
  match c v with None => s | Some _ => s' end v.
Definition reset_temps := reset_vars archtyps.

Inductive can_step (p:program): ((exit*store) * (exit*store)) -> Prop :=
| CanStep a s sz q c' s' x (LU: p s a = Some (sz,q)) (XS: exec_stmt archtyps s q c' s' x):
    can_step p ((exitof (a+sz) x, reset_temps s s'),(Addr a, s)).

Definition exec_prog (p:program) (t:trace) := Forall (can_step p) (stepsof t).

End InterpreterEngine.


Section Quantification.

(* Recursive quantification of sub-expressions and sub-statements: *)

Fixpoint exps_in_exp {T:Type} (C:T->T->T) (P:exp->T) (e:exp) : T :=
  match e with
  | Var _ | Word _ _ | Unknown _ => P e
  | UnOp _ e1 | Cast _ _ e1 | Extract _ _ e1 => C (P e) (exps_in_exp C P e1)
  | BinOp _ e1 e2 | Let _ e1 e2 | Concat e1 e2 | Load e1 e2 _ _ =>
      C (P e) (C (exps_in_exp C P e1) (exps_in_exp C P e2))
  | Ite e1 e2 e3 | Store e1 e2 e3 _ _ =>
      C (P e) (C (exps_in_exp C P e1) (C (exps_in_exp C P e2) (exps_in_exp C P e3)))
  end.

Fixpoint exps_in_stmt {T:Type} (C:T->T->T) (b:T) (P:exp->T) (q:stmt) : T :=
  match q with
  | Nop | Exn _ => b
  | Move _ e | Jmp e => exps_in_exp C P e
  | Seq q1 q2 => C (exps_in_stmt C b P q1) (exps_in_stmt C b P q2)
  | Rep e q0 => C (exps_in_exp C P e) (exps_in_stmt C b P q0)
  | If e q1 q2 => C (exps_in_exp C P e) (C (exps_in_stmt C b P q1) (exps_in_stmt C b P q2))
  end.

Fixpoint stmts_in_stmt {T:Type} (C:T->T->T) (P:stmt->T) (q:stmt) : T :=
  match q with
  | Nop | Exn _ | Move _ _ | Jmp _ => P q
  | Rep _ q0 => C (P q) (stmts_in_stmt C P q0)
  | Seq q1 q2 | If _ q1 q2 => C (P q) (C (stmts_in_stmt C P q1) (stmts_in_stmt C P q2))
  end.

Definition forall_exps_in_exp := exps_in_exp and.
Definition forall_exps_in_stmt := exps_in_stmt and True.
Definition exists_exp_in_exp := exps_in_exp or.
Definition exists_exp_in_stmt := exps_in_stmt or False.
Definition forall_stmts_in_stmt := stmts_in_stmt and.
Definition exists_stmt_in_stmt := stmts_in_stmt or.
Definition forall_exps_in_prog P (p:program) :=
  forall s a q sz, p s a = Some (sz,q) -> forall_exps_in_stmt P q.
Definition exists_exp_in_prog P (p:program) :=
  exists s a q sz, p s a = Some (sz,q) /\ exists_exp_in_stmt P q.
Definition forall_stmts_in_prog P (p:program) :=
  forall s a q sz, p s a = Some (sz,q) -> forall_stmts_in_stmt P q.
Definition exists_stmt_in_prog P (p:program) :=
  exists s a q sz, p s a = Some (sz,q) /\ exists_stmt_in_stmt P q.

Definition forall_vars_in_exp (P: var -> Prop) :=
  forall_exps_in_exp (fun e => match e with Var v | Let v _ _ => P v | _ => True end).
Definition forall_vars_in_stmt (P: var -> Prop) (q:stmt) :=
  forall_stmts_in_stmt (fun q => match q with Move v _ => P v | _ => True end) q /\
  forall_exps_in_stmt (forall_vars_in_exp P) q.
Definition forall_vars_in_prog (P: var -> Prop) :=
  forall_stmts_in_prog (forall_vars_in_stmt P).
Definition exists_var_in_exp (P: var -> Prop) :=
  exists_exp_in_exp (fun e => match e with Var v | Let v _ _ => P v | _ => False end).
Definition exists_var_in_stmt (P: var -> Prop) (q: stmt) :=
  exists_stmt_in_stmt (fun q => match q with Move v _ => P v | _ => False end) q \/
  exists_exp_in_stmt (exists_var_in_exp P) q.
Definition exists_var_in_prog (P: var -> Prop) :=
  exists_stmt_in_prog (exists_var_in_stmt P).

Global Arguments exps_in_exp {T} C P !e.
Global Arguments exps_in_stmt {T} C b P !q.
Global Arguments stmts_in_stmt {T} C P !q.
Global Arguments forall_exps_in_exp P e /.
Global Arguments forall_exps_in_stmt P q /.
Global Arguments exists_exp_in_exp P e /.
Global Arguments exists_exp_in_stmt P q /.
Global Arguments forall_stmts_in_stmt P q /.
Global Arguments exists_stmt_in_stmt P q /.
Global Arguments forall_vars_in_exp P e /.
Global Arguments forall_vars_in_stmt P q /.
Global Arguments exists_var_in_exp P e /.
Global Arguments exists_var_in_stmt P q /.

Definition forall_traces_in (p:program) (P: trace -> Prop) : Prop :=
  forall t (XP: exec_prog p t), P t.

Definition forall_endstates (p:program) (P: exit -> store -> exit -> store -> Prop) : Prop :=
  forall t x s x' s' (XP: exec_prog p ((x',s')::t)) (ENTRY: startof t (x',s') = (x,s)),
  P x s x' s'.

(* "Unknown" expressions are the sole source of non-determinism in the IL
   semantics, so it is useful to have a special test for those, which can
   be combined with the quantifiers above to find all "Unknowns". *)
Definition not_unknown e := match e with Unknown _ => False | _ => True end.

(* Many proofs have trivial cases that prove that a variable v is invariant
   because it is never assigned.  To assist these proofs, the following
   inductive predicate defines a universal quantifier over all variables
   appearing on the left of any "Move" statements. *)
Inductive allassigns (P: var -> Prop) : stmt -> Prop :=
| AANop: allassigns P Nop
| AAMove v e (PV: P v): allassigns P (Move v e)
| AAJmp e: allassigns P (Jmp e)
| AAExn i: allassigns P (Exn i)
| AASeq q1 q2 (AA1: allassigns P q1) (AA2: allassigns P q2): allassigns P (Seq q1 q2)
| AARep e q (AA: allassigns P q): allassigns P (Rep e q)
| AAIf e q1 q2 (AA1: allassigns P q1) (AA2: allassigns P q2): allassigns P (If e q1 q2).

Definition noassign v := allassigns (fun v0 => v0 <> v).

Definition prog_noassign v (p:program) :=
  forall s a, match p s a with None => True | Some (_,q) => noassign v q end.

End Quantification.

End PICINAE_CORE.


Module Type PICINAE_IL := Architecture <+ PICINAE_CORE.

Module PicinaeIL (Arch: Architecture) <: PICINAE_IL.
  Include Arch.
  Include PICINAE_CORE Arch.
End PicinaeIL.

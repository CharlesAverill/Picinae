(* Coq syntax for Binary Analysis Platform (BAP)
 *
 * Copyright (c) 2018 Kevin W. Hamlen
 * Computer Science Department
 * The University of Texas at Dallas
 *
 * Any use, commercial or otherwise, requires the express permission of
 * the author.
 *)

Require Import BinNums.
Require Import Structures.Equalities.

Module BAPSyntax (VarID:Typ).

(* IL variables are identifiers as defined by Coq's "Typ" module (see the
   documentation of Coq's Structures.Equalities library. *)
Definition varid := VarID.t.

(* Bitwidths are expressed as natural numbers. *)
Definition bitwidth := N.

(* An IL expression type is a number of bitwidth w, or a memory state with
   addresses of bitwidth w.  (The bitwidth of memory contents is architecture-
   specific ("Mb" in BapInterp), but is usually bitwidth 8.) *)
Inductive typ : Type :=
| NumT (w:bitwidth)
| MemT (w:bitwidth).

(* Endianness: *)
Inductive endianness : Type :=
| BigE
| LittleE.

(* An integer is an unsigned value and its bitwidth.  During signed operations,
   the bits of the value are reinterpreted as a signed integer. *)
Definition word := (N*bitwidth)%type.

(* A variable appearing within an IL expression or statement is written as
   (Va id t) where id is an identifier (from the Typ module---see above)
   and t is its BAP type. *)
Inductive var : Type := Va (id:varid) (t:typ).

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
| Word (n:word)
| Load (e1 e2:exp) (en:endianness) (w:bitwidth)  (* Load(mem,addr,endian,bitwidth) *)
| Store (e1 e2 e3:exp) (en:endianness) (w:bitwidth)  (* Store(mem,addr,val,endian,bitwidth) *)
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

(* Memory addresses are expressed as natural numbers. *)
Definition addr := N.

(* Programs map addresses to an instruction size sz and an IL statement q
   that encodes the instruction.  If q falls through, control flows to
   address a+sz.  We express programs as functions instead of lists in order
   to correctly model architectures and programs with unaligned instructions
   (or those whose alignments are unknown prior to the analysis). *)
Definition program := addr -> option (N * stmt).

End BAPSyntax.

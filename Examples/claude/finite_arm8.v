(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: finite
entry: 0x139f20 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition finite_arm8 : program := fun _ a => match a with

(* 0x00139f20: fmov x0,d0 *)
(*          0: fmov x0,d0 *)
| 0x0 => Some (4,
	Move R_X0 (Extract 63 0 (Var R_Z0))
)

(* 0x00139f24: mov x1,#-0x7ff0000000000000 *)
(*          4: mov x1,#-0x7ff0000000000000 *)
| 0x4 => Some (4,
	Move R_X1 (Word 0x8010000000000000 64)
)

(* 0x00139f28: and x0,x0,#0x7ff0000000000000 *)
(*          8: and x0,x0,#0x7ff0000000000000 *)
| 0x8 => Some (4,
	Move R_X0 (BinOp OP_AND (Var R_X0) (Word 0x7ff0000000000000 64))
)

(* 0x00139f2c: add x0,x0,x1 *)
(*         12: add x0,x0,x1 *)
| 0xc => Some (4,
	Move (V_TEMP 0) (Var R_X1) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 1))
)

(* 0x00139f30: lsr x0,x0,#0x3f *)
(*         16: lsr x0,x0,#0x3f *)
| 0x10 => Some (4,
	Move R_X0 (BinOp OP_RSHIFT (Var R_X0) (Word 63 64))
)

(* 0x00139f34: ret *)
(*         20: ret *)
| 0x14 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx finite_arm8.
Proof. Picinae_typecheck. Qed.


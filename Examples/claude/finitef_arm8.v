(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: finitef
entry: 0x13a230 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition finitef_arm8 : program := fun _ a => match a with

(* 0x0013a230: fmov w0,s0 *)
(*          0: fmov w0,s0 *)
| 0x0 => Some (4,
	Move R_X0 (Concat (Word 0x0 32) (Extract 31 0 (Var R_Z0)))
)

(* 0x0013a234: mov w1,#0x80800000 *)
(*          4: mov w1,#0x80800000 *)
| 0x4 => Some (4,
	Move R_X1 (Word 0x80800000 64)
)

(* 0x0013a238: and w0,w0,#0x7f800000 *)
(*          8: and w0,w0,#0x7f800000 *)
| 0x8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x7f800000 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a23c: add w0,w0,w1 *)
(*         12: add w0,w0,w1 *)
| 0xc => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_X1)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
)

(* 0x0013a240: lsr w0,w0,#0x1f *)
(*         16: lsr w0,w0,#0x1f *)
| 0x10 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x0013a244: ret *)
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

Theorem welltyped: welltyped_prog arm8typctx finitef_arm8.
Proof. Picinae_typecheck. Qed.


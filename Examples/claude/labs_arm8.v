(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: imaxabs
entry: 0x13d820 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition labs_arm8 : program := fun _ a => match a with

(* 0x0013d820: cmp x0,#0x0 *)
(*          0: cmp x0,#0x0 *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0013d824: cneg x0,x0,lt *)
(*          4: cneg x0,x0,lt *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_NG) (Var R_OV))) $;
	Move (V_TEMP 1) (UnOp OP_NEG (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Move R_X0 (Var (V_TEMP 1))
	) (* else *) (
		Move (V_TEMP 1) (Var R_X0) $;
		Move R_X0 (Var (V_TEMP 1))
	)
)

(* 0x0013d828: ret *)
(*          8: ret *)
| 0x8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx labs_arm8.
Proof. Picinae_typecheck. Qed.


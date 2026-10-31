(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: abs
entry: 0x13d810 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition abs_arm8 : program := fun _ a => match a with

(* 0x0013d810: cmp w0,#0x0 *)
(*          0: cmp w0,#0x0 *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0013d814: cneg w0,w0,lt *)
(*          4: cneg w0,w0,lt *)
| 0x4 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_NG) (Var R_OV))) $;
	Move (V_TEMP 1) (UnOp OP_NEG (Extract 31 0 (Var R_X0))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
	) (* else *) (
		Move (V_TEMP 1) (Extract 31 0 (Var R_X0)) $;
		Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1)))
	)
)

(* 0x0013d818: ret *)
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

Theorem welltyped: welltyped_prog arm8typctx abs_arm8.
Proof. Picinae_typecheck. Qed.


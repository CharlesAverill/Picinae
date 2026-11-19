(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_setscope
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_setscope_armv8 : program := fun _ a => match a with

(* 0x001611b4: mov w0,#0x0 *)
(*    1446324: mov w0,#0x0 *)
| 0x1611b4 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001611b8: cbz w1,0x001611cc *)
(*    1446328: cbz w1,0x001611cc *)
| 0x1611b8 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x1611cc 64)
	) (* else *) (
		Nop
	)
)

(* 0x001611bc: cmp w1,#0x1 *)
(*    1446332: cmp w1,#0x1 *)
| 0x1611bc => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x1 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x1 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001611c0: mov w0,#0x5f *)
(*    1446336: mov w0,#0x5f *)
| 0x1611c0 => Some (4,
	Move R_X0 (Word 0x5f 64)
)

(* 0x001611c4: mov w1,#0x16 *)
(*    1446340: mov w1,#0x16 *)
| 0x1611c4 => Some (4,
	Move R_X1 (Word 0x16 64)
)

(* 0x001611c8: csel w0,w0,w1,eq *)
(*    1446344: csel w0,w0,w1,eq *)
| 0x1611c8 => Some (4,
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X1))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1d900)))
)

(* 0x001611cc: ret *)
(*    1446348: ret *)
| 0x1611cc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_setscope_armv8.
Proof. Picinae_typecheck. Qed.

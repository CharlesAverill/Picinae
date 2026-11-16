(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: toupper
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition toupper_armv8 : program := fun _ a => match a with

(* 0x0011f2e8: sub w2,w0,#0x61 *)
(*    1176296: sub w2,w0,#0x61 *)
| 0x11f2e8 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x61 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x0011f2ec: mov w1,#0x5f *)
(*    1176300: mov w1,#0x5f *)
| 0x11f2ec => Some (4,
	Move R_X1 (Word 0x5f 64)
)

(* 0x0011f2f0: cmp w2,#0x19 *)
(*    1176304: cmp w2,#0x19 *)
| 0x11f2f0 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x19 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x19 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x19 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x19 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x19 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011f2f4: and w1,w0,w1 *)
(*    1176308: and w1,w0,w1 *)
| 0x11f2f4 => Some (4,
	Move (V_TEMP 0x12480) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12480)))
)

(* 0x0011f2f8: csel w0,w1,w0,ls *)
(*    1176312: csel w0,w1,w0,ls *)
| 0x11f2f8 => Some (4,
	Move (V_TEMP 0x1b80) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1c80) (BinOp OP_OR (Var (V_TEMP 0x1b80)) (Var R_ZR)) $;
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X1)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1c80))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X0))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1d900)))
)

(* 0x0011f2fc: ret *)
(*    1176316: ret *)
| 0x11f2fc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx toupper_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: ctermid
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ctermid_armv8 : program := fun _ a => match a with

(* 0x00168c94: cbz x0,0x00168ca4 *)
(*    1477780: cbz x0,0x00168ca4 *)
| 0x168c94 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x168ca4 64)
	) (* else *) (
		Nop
	)
)

(* 0x00168c98: adrp x1,0x19f000 *)
(*    1477784: adrp x1,0x19f000 *)
| 0x168c98 => Some (4,
	Move R_X1 (Word 0x19f000 64)
)

(* 0x00168c9c: add x1,x1,#0x980 *)
(*    1477788: add x1,x1,#0x980 *)
| 0x168c9c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x980 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x00168ca0: b 0x0015eccc *)
(*    1477792: b 0x0015eccc *)
| 0x168ca0 => Some (4,
	Jmp (Word 0x15eccc 64)
)

(* 0x00168ca4: adrp x0,0x19f000 *)
(*    1477796: adrp x0,0x19f000 *)
| 0x168ca4 => Some (4,
	Move R_X0 (Word 0x19f000 64)
)

(* 0x00168ca8: add x0,x0,#0x980 *)
(*    1477800: add x0,x0,#0x980 *)
| 0x168ca8 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x980 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x00168cac: ret *)
(*    1477804: ret *)
| 0x168cac => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ctermid_armv8.
Proof. Picinae_typecheck. Qed.

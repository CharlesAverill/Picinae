(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wmemcmp
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wmemcmp_armv8 : program := fun _ a => match a with

(* 0x001601f8: cbz x2,0x00160224 *)
(*    1442296: cbz x2,0x00160224 *)
| 0x1601f8 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x160224 64)
	) (* else *) (
		Nop
	)
)

(* 0x001601fc: ldr w4,[x0] *)
(*    1442300: ldr w4,[x0] *)
| 0x1601fc => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00160200: sub x2,x2,#0x1 *)
(*    1442304: sub x2,x2,#0x1 *)
| 0x160200 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x00160204: ldr w3,[x1] *)
(*    1442308: ldr w3,[x1] *)
| 0x160204 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00160208: add x0,x0,#0x4 *)
(*    1442312: add x0,x0,#0x4 *)
| 0x160208 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0016020c: add x1,x1,#0x4 *)
(*    1442316: add x1,x1,#0x4 *)
| 0x16020c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x00160210: cmp w4,w3 *)
(*    1442320: cmp w4,w3 *)
| 0x160210 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X4)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X4)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X3))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00160214: b.eq 0x001601f8 *)
(*    1442324: b.eq 0x001601f8 *)
| 0x160214 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x1601f8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00160218: cset w0,hi *)
(*    1442328: cset w0,hi *)
| 0x160218 => Some (4,
	Move (V_TEMP 0x2680) (UnOp OP_NOT (Var R_ZR)) $;
	Move (V_TEMP 0x2780) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0x2680))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2780)))
)

(* 0x0016021c: csinv w0,w0,wzr,cs *)
(*    1442332: csinv w0,w0,wzr,cs *)
| 0x16021c => Some (4,
	Move (V_TEMP 0x0) (Word 0x0 32) $;
	Move (V_TEMP 0x1e600) (Extract 31 0 (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1e600) (UnOp OP_NOT (Var (V_TEMP 0x0)))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1e600)))
)

(* 0x00160220: b 0x00160228 *)
(*    1442336: b 0x00160228 *)
| 0x160220 => Some (4,
	Jmp (Word 0x160228 64)
)

(* 0x00160224: mov w0,#0x0 *)
(*    1442340: mov w0,#0x0 *)
| 0x160224 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00160228: ret *)
(*    1442344: ret *)
| 0x160228 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wmemcmp_armv8.
Proof. Picinae_typecheck. Qed.

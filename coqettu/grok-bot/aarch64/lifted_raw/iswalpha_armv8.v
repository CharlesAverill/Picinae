(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: iswalpha
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition iswalpha_armv8 : program := fun _ a => match a with

(* 0x0011ef48: mov w1,#0x1ffff *)
(*    1175368: mov w1,#0x1ffff *)
| 0x11ef48 => Some (4,
	Move R_X1 (Word 0x1ffff 64)
)

(* 0x0011ef4c: cmp w0,w1 *)
(*    1175372: cmp w0,w1 *)
| 0x11ef4c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011ef50: b.ls 0x0011ef68 *)
(*    1175376: b.ls 0x0011ef68 *)
| 0x11ef50 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x11ef68 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011ef54: mov w1,#0xfffd *)
(*    1175380: mov w1,#0xfffd *)
| 0x11ef54 => Some (4,
	Move R_X1 (Word 0xfffd 64)
)

(* 0x0011ef58: movk w1,#0x2, LSL #16 *)
(*    1175384: movk w1,#0x2, LSL #16 *)
| 0x11ef58 => Some (4,
	Move (V_TEMP 0x29b00) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Word 0xffff 32)) $;
	Move (V_TEMP 0x29b00) (BinOp OP_OR (Var (V_TEMP 0x29b00)) (Word 0x20000 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x29b00)))
)

(* 0x0011ef5c: cmp w0,w1 *)
(*    1175388: cmp w0,w1 *)
| 0x11ef5c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011ef60: cset w0,ls *)
(*    1175392: cset w0,ls *)
| 0x11ef60 => Some (4,
	Move (V_TEMP 0x2800) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x2900) (BinOp OP_OR (Var (V_TEMP 0x2800)) (Var R_ZR)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2900)))
)

(* 0x0011ef64: ret *)
(*    1175396: ret *)
| 0x11ef64 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0011ef68: lsr w2,w0,#0x8 *)
(*    1175400: lsr w2,w0,#0x8 *)
| 0x11ef68 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x8 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x0011ef6c: adrp x1,0x172000 *)
(*    1175404: adrp x1,0x172000 *)
| 0x11ef6c => Some (4,
	Move R_X1 (Word 0x172000 64)
)

(* 0x0011ef70: add x1,x1,#0x1b0 *)
(*    1175408: add x1,x1,#0x1b0 *)
| 0x11ef70 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1b0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0011ef74: ubfx x3,x0,#0x3,#0x5 *)
(*    1175412: ubfx x3,x0,#0x3,#0x5 *)
| 0x11ef74 => Some (4,
	Move (V_TEMP 0x41100) (Var R_X0) $;
	Move (V_TEMP 0x41180) (BinOp OP_RSHIFT (Var (V_TEMP 0x41100)) (Word 0x3 64)) $;
	Move (V_TEMP 0x41200) (BinOp OP_MINUS (Word 0x40 64) (Word 0x3 64)) $;
	Move (V_TEMP 0x41280) (BinOp OP_LSHIFT (Var (V_TEMP 0x41100)) (Var (V_TEMP 0x41200))) $;
	Move (V_TEMP 0x41300) (BinOp OP_OR (Var (V_TEMP 0x41180)) (Var (V_TEMP 0x41280))) $;
	Move (V_TEMP 0x41400) (BinOp OP_AND (Var (V_TEMP 0x41300)) (Word 0xe00000000000001f 64)) $;
	Move R_X3 (BinOp OP_AND (Var (V_TEMP 0x41400)) (Word 0x1f 64))
)

(* 0x0011ef78: and w0,w0,#0x7 *)
(*    1175416: and w0,w0,#0x7 *)
| 0x11ef78 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x7 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0011ef7c: ldrb w2,[x1, w2, UXTW ] *)
(*    1175420: ldrb w2,[x1, w2, UXTW ] *)
| 0x11ef7c => Some (4,
	Move (V_TEMP 0x5580) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2))) $;
	Move (V_TEMP 0x6c00) (Var (V_TEMP 0x5580)) $;
	Move (V_TEMP 0x6c00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6c00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6c00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0011ef80: add w2,w3,w2, LSL #0x5 *)
(*    1175424: add w2,w3,w2, LSL #0x5 *)
| 0x11ef80 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X2)) (Word 0x5 32)) $;
	Move (V_TEMP 0x11d80) (Var (V_TEMP 0x3e80)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x11d80))) (Extract 31 0 (Var R_X3)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x11d80))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11d80)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11e80) (BinOp OP_PLUS (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x11d80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80)))
)

(* 0x0011ef84: ldrb w1,[x1, w2, UXTW ] *)
(*    1175428: ldrb w1,[x1, w2, UXTW ] *)
| 0x11ef84 => Some (4,
	Move (V_TEMP 0x5580) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2))) $;
	Move (V_TEMP 0x6c00) (Var (V_TEMP 0x5580)) $;
	Move (V_TEMP 0x6c00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6c00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6c00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0011ef88: asr w0,w1,w0 *)
(*    1175432: asr w0,w1,w0 *)
| 0x11ef88 => Some (4,
	Move (V_TEMP 0x12d80) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move (V_TEMP 0x12e80) (BinOp OP_ARSHIFT (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x12d80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12e80)))
)

(* 0x0011ef8c: and w0,w0,#0x1 *)
(*    1175436: and w0,w0,#0x1 *)
| 0x11ef8c => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x1 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0011ef90: b 0x0011ef64 *)
(*    1175440: b 0x0011ef64 *)
| 0x11ef90 => Some (4,
	Jmp (Word 0x11ef64 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx iswalpha_armv8.
Proof. Picinae_typecheck. Qed.

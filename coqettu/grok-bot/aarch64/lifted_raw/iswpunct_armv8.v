(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: iswpunct
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition iswpunct_armv8 : program := fun _ a => match a with

(* 0x0011f1cc: mov w1,#0x1ffff *)
(*    1176012: mov w1,#0x1ffff *)
| 0x11f1cc => Some (4,
	Move R_X1 (Word 0x1ffff 64)
)

(* 0x0011f1d0: cmp w0,w1 *)
(*    1176016: cmp w0,w1 *)
| 0x11f1d0 => Some (4,
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

(* 0x0011f1d4: b.ls 0x0011f1e0 *)
(*    1176020: b.ls 0x0011f1e0 *)
| 0x11f1d4 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x11f1e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011f1d8: mov w0,#0x0 *)
(*    1176024: mov w0,#0x0 *)
| 0x11f1d8 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0011f1dc: ret *)
(*    1176028: ret *)
| 0x11f1dc => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0011f1e0: lsr w2,w0,#0x8 *)
(*    1176032: lsr w2,w0,#0x8 *)
| 0x11f1e0 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x8 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x0011f1e4: adrp x1,0x173000 *)
(*    1176036: adrp x1,0x173000 *)
| 0x11f1e4 => Some (4,
	Move R_X1 (Word 0x173000 64)
)

(* 0x0011f1e8: add x1,x1,#0x140 *)
(*    1176040: add x1,x1,#0x140 *)
| 0x11f1e8 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x140 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0011f1ec: ubfx x3,x0,#0x3,#0x5 *)
(*    1176044: ubfx x3,x0,#0x3,#0x5 *)
| 0x11f1ec => Some (4,
	Move (V_TEMP 0x41100) (Var R_X0) $;
	Move (V_TEMP 0x41180) (BinOp OP_RSHIFT (Var (V_TEMP 0x41100)) (Word 0x3 64)) $;
	Move (V_TEMP 0x41200) (BinOp OP_MINUS (Word 0x40 64) (Word 0x3 64)) $;
	Move (V_TEMP 0x41280) (BinOp OP_LSHIFT (Var (V_TEMP 0x41100)) (Var (V_TEMP 0x41200))) $;
	Move (V_TEMP 0x41300) (BinOp OP_OR (Var (V_TEMP 0x41180)) (Var (V_TEMP 0x41280))) $;
	Move (V_TEMP 0x41400) (BinOp OP_AND (Var (V_TEMP 0x41300)) (Word 0xe00000000000001f 64)) $;
	Move R_X3 (BinOp OP_AND (Var (V_TEMP 0x41400)) (Word 0x1f 64))
)

(* 0x0011f1f0: and w0,w0,#0x7 *)
(*    1176048: and w0,w0,#0x7 *)
| 0x11f1f0 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x7 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0011f1f4: ldrb w2,[x1, w2, UXTW ] *)
(*    1176052: ldrb w2,[x1, w2, UXTW ] *)
| 0x11f1f4 => Some (4,
	Move (V_TEMP 0x5580) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2))) $;
	Move (V_TEMP 0x6c00) (Var (V_TEMP 0x5580)) $;
	Move (V_TEMP 0x6c00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6c00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6c00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0011f1f8: add w2,w3,w2, LSL #0x5 *)
(*    1176056: add w2,w3,w2, LSL #0x5 *)
| 0x11f1f8 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X2)) (Word 0x5 32)) $;
	Move (V_TEMP 0x11d80) (Var (V_TEMP 0x3e80)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x11d80))) (Extract 31 0 (Var R_X3)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x11d80))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11d80)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11e80) (BinOp OP_PLUS (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x11d80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80)))
)

(* 0x0011f1fc: ldrb w1,[x1, w2, UXTW ] *)
(*    1176060: ldrb w1,[x1, w2, UXTW ] *)
| 0x11f1fc => Some (4,
	Move (V_TEMP 0x5580) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2))) $;
	Move (V_TEMP 0x6c00) (Var (V_TEMP 0x5580)) $;
	Move (V_TEMP 0x6c00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6c00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6c00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0011f200: asr w0,w1,w0 *)
(*    1176064: asr w0,w1,w0 *)
| 0x11f200 => Some (4,
	Move (V_TEMP 0x12d80) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move (V_TEMP 0x12e80) (BinOp OP_ARSHIFT (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x12d80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12e80)))
)

(* 0x0011f204: and w0,w0,#0x1 *)
(*    1176068: and w0,w0,#0x1 *)
| 0x11f204 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x1 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0011f208: b 0x0011f1dc *)
(*    1176072: b 0x0011f1dc *)
| 0x11f208 => Some (4,
	Jmp (Word 0x11f1dc 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx iswpunct_armv8.
Proof. Picinae_typecheck. Qed.

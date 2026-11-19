(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: iswcntrl
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition iswcntrl_armv8 : program := fun _ a => match a with

(* 0x0011efa0: sub w1,w0,#0x7f *)
(*    1175456: sub w1,w0,#0x7f *)
| 0x11efa0 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x7f 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x0011efa4: cmp w1,#0x20 *)
(*    1175460: cmp w1,#0x20 *)
| 0x11efa4 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x20 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x20 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x20 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011efa8: mov w1,#0x1 *)
(*    1175464: mov w1,#0x1 *)
| 0x11efa8 => Some (4,
	Move R_X1 (Word 0x1 64)
)

(* 0x0011efac: ccmp w0,#0x1f,#0x0,hi *)
(*    1175468: ccmp w0,#0x1f,#0x0,hi *)
| 0x11efac => Some (4,
	Move (V_TEMP 0x1a00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x1b00) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0x1a00))) $;
	Move (V_TEMP 0x19800) (Var (V_TEMP 0x1b00)) $;
	Move (V_TEMP 0x19880) (Word 0x0 8) $;
	Move (V_TEMP 0xe380) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe380)) (Word 0x8 8))) $;
	Move (V_TEMP 0xe480) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe480)) (Word 0x4 8))) $;
	Move (V_TEMP 0xe580) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe580)) (Word 0x2 8))) $;
	Move (V_TEMP 0xe680) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe680)) (Word 0x1 8))) $;
	Move (V_TEMP 0x19900) (BinOp OP_XOR (Var (V_TEMP 0x19800)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x19900))) (
		Jmp (Word 0x11efb0 64)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x1f 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1f 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x19a00) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x19a00)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x19a00)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011efb0: b.ls 0x0011efd8 *)
(*    1175472: b.ls 0x0011efd8 *)
| 0x11efb0 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x11efd8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011efb4: mov w2,#0xffffdfd8 *)
(*    1175476: mov w2,#0xffffdfd8 *)
| 0x11efb4 => Some (4,
	Move R_X2 (Word 0xffffdfd8 64)
)

(* 0x0011efb8: add w2,w0,w2 *)
(*    1175480: add w2,w0,w2 *)
| 0x11efb8 => Some (4,
	Move (V_TEMP 0x11d80) (Extract 31 0 (Var R_X2)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11d80))) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11d80))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11d80)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11e80) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11d80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80)))
)

(* 0x0011efbc: mov w1,#0x1 *)
(*    1175484: mov w1,#0x1 *)
| 0x11efbc => Some (4,
	Move R_X1 (Word 0x1 64)
)

(* 0x0011efc0: cmp w2,w1 *)
(*    1175488: cmp w2,w1 *)
| 0x11efc0 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011efc4: b.ls 0x0011efd8 *)
(*    1175492: b.ls 0x0011efd8 *)
| 0x11efc4 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x11efd8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011efc8: mov w1,#0xffff0007 *)
(*    1175496: mov w1,#0xffff0007 *)
| 0x11efc8 => Some (4,
	Move R_X1 (Word 0xffff0007 64)
)

(* 0x0011efcc: add w0,w0,w1 *)
(*    1175500: add w0,w0,w1 *)
| 0x11efcc => Some (4,
	Move (V_TEMP 0x11d80) (Extract 31 0 (Var R_X1)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11d80))) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11d80))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11d80)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11e80) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11d80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80)))
)

(* 0x0011efd0: cmp w0,#0x2 *)
(*    1175504: cmp w0,#0x2 *)
| 0x11efd0 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x2 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x2 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x2 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x2 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011efd4: cset w1,ls *)
(*    1175508: cset w1,ls *)
| 0x11efd4 => Some (4,
	Move (V_TEMP 0x2800) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x2900) (BinOp OP_OR (Var (V_TEMP 0x2800)) (Var R_ZR)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2900)))
)

(* 0x0011efd8: mov w0,w1 *)
(*    1175512: mov w0,w1 *)
| 0x11efd8 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X1)))
)

(* 0x0011efdc: ret *)
(*    1175516: ret *)
| 0x11efdc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx iswcntrl_armv8.
Proof. Picinae_typecheck. Qed.

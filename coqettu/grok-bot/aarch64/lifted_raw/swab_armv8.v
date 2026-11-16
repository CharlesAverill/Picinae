(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: swab
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition swab_armv8 : program := fun _ a => match a with

(* 0x0015f9d8: add x2,x0,x2 *)
(*    1440216: add x2,x0,x2 *)
| 0x15f9d8 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x12080))
)

(* 0x0015f9dc: b 0x0015f9f4 *)
(*    1440220: b 0x0015f9f4 *)
| 0x15f9dc => Some (4,
	Jmp (Word 0x15f9f4 64)
)

(* 0x0015f9e0: ldrb w4,[x0, #0x1] *)
(*    1440224: ldrb w4,[x0, #0x1] *)
| 0x15f9e0 => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X0) (Word 0x1 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f9e4: add x1,x1,#0x2 *)
(*    1440228: add x1,x1,#0x2 *)
| 0x15f9e4 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x2 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015f9e8: ldrb w3,[x0], #0x2 *)
(*    1440232: ldrb w3,[x0], #0x2 *)
| 0x15f9e8 => Some (4,
	Move (V_TEMP 0x7000) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x2 64)) $;
	Move (V_TEMP 0x24f00) (Load (Var V_MEM64) (Var (V_TEMP 0x7000)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24f00)))
)

(* 0x0015f9ec: sturb w4,[x1, #-0x2] *)
(*    1440236: sturb w4,[x1, #-0x2] *)
| 0x15f9ec => Some (4,
	Move (V_TEMP 0x3a680) (Extract 31 0 (Var R_X4)) $;
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X1) (Word 0xfffffffffffffffe 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a680)))) LittleE 1)
)

(* 0x0015f9f0: sturb w3,[x1, #-0x1] *)
(*    1440240: sturb w3,[x1, #-0x1] *)
| 0x15f9f0 => Some (4,
	Move (V_TEMP 0x3a680) (Extract 31 0 (Var R_X3)) $;
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X1) (Word 0xffffffffffffffff 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a680)))) LittleE 1)
)

(* 0x0015f9f4: sub x3,x2,x0 *)
(*    1440244: sub x3,x2,x0 *)
| 0x15f9f4 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X2) (Var R_X0))
)

(* 0x0015f9f8: cmp x3,#0x1 *)
(*    1440248: cmp x3,#0x1 *)
| 0x15f9f8 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X3) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f9fc: b.gt 0x0015f9e0 *)
(*    1440252: b.gt 0x0015f9e0 *)
| 0x15f9fc => Some (4,
	Move (V_TEMP 0x1280) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x1300) (BinOp OP_EQ (Var R_NG) (Var R_OV)) $;
	Move (V_TEMP 0x1400) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Cast CAST_LOW 1 (Var (V_TEMP 0x1280))) (Var (V_TEMP 0x1300)))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1400))) (
		Jmp (Word 0x15f9e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fa00: ret *)
(*    1440256: ret *)
| 0x15fa00 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx swab_armv8.
Proof. Picinae_typecheck. Qed.

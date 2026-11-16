(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strcmp
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcmp_armv8 : program := fun _ a => match a with

(* 0x0015eca4: mov x2,#0x0 *)
(*    1436836: mov x2,#0x0 *)
| 0x15eca4 => Some (4,
	Move R_X2 (Word 0x0 64)
)

(* 0x0015eca8: ldrb w4,[x0, x2, LSL ] *)
(*    1436840: ldrb w4,[x0, x2, LSL ] *)
| 0x15eca8 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015ecac: ldrb w3,[x1, x2, LSL ] *)
(*    1436844: ldrb w3,[x1, x2, LSL ] *)
| 0x15ecac => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015ecb0: add x2,x2,#0x1 *)
(*    1436848: add x2,x2,#0x1 *)
| 0x15ecb0 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015ecb4: cmp w4,w3 *)
(*    1436852: cmp w4,w3 *)
| 0x15ecb4 => Some (4,
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

(* 0x0015ecb8: b.ne 0x0015ecc4 *)
(*    1436856: b.ne 0x0015ecc4 *)
| 0x15ecb8 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15ecc4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ecbc: cbnz w3,0x0015eca8 *)
(*    1436860: cbnz w3,0x0015eca8 *)
| 0x15ecbc => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15eca8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ecc0: mov w4,#0x0 *)
(*    1436864: mov w4,#0x0 *)
| 0x15ecc0 => Some (4,
	Move R_X4 (Word 0x0 64)
)

(* 0x0015ecc4: sub w0,w4,w3 *)
(*    1436868: sub w0,w4,w3 *)
| 0x15ecc4 => Some (4,
	Move (V_TEMP 0x3cc80) (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X3))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3cc80)))
)

(* 0x0015ecc8: ret *)
(*    1436872: ret *)
| 0x15ecc8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strcmp_armv8.
Proof. Picinae_typecheck. Qed.

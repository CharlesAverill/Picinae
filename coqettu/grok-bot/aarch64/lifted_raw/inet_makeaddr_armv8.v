(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: inet_makeaddr
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition inet_makeaddr_armv8 : program := fun _ a => match a with

(* 0x00142348: cmp w0,#0xff *)
(*    1319752: cmp w0,#0xff *)
| 0x142348 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0xff 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0xff 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0xff 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0xff 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xff 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0014234c: b.hi 0x00142358 *)
(*    1319756: b.hi 0x00142358 *)
| 0x14234c => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x142358 64)
	) (* else *) (
		Nop
	)
)

(* 0x00142350: orr w0,w1,w0, LSL #0x18 *)
(*    1319760: orr w0,w1,w0, LSL #0x18 *)
| 0x142350 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x18 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x3e80))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x00142354: ret *)
(*    1319764: ret *)
| 0x142354 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00142358: orr w2,w1,w0, LSL #0x10 *)
(*    1319768: orr w2,w1,w0, LSL #0x10 *)
| 0x142358 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x10 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x3e80))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x0014235c: mov w3,#0xffff *)
(*    1319772: mov w3,#0xffff *)
| 0x14235c => Some (4,
	Move R_X3 (Word 0xffff 64)
)

(* 0x00142360: orr w1,w1,w0, LSL #0x8 *)
(*    1319776: orr w1,w1,w0, LSL #0x8 *)
| 0x142360 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X0)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2d000) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x3e80))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2d000)))
)

(* 0x00142364: cmp w0,w3 *)
(*    1319780: cmp w0,w3 *)
| 0x142364 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X3))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00142368: csel w0,w1,w2,hi *)
(*    1319784: csel w0,w1,w2,hi *)
| 0x142368 => Some (4,
	Move (V_TEMP 0x1a00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x1b00) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0x1a00))) $;
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X1)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1b00))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X2))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1d900)))
)

(* 0x0014236c: b 0x00142354 *)
(*    1319788: b 0x00142354 *)
| 0x14236c => Some (4,
	Jmp (Word 0x142354 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx inet_makeaddr_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: inet_netof
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition inet_netof_armv8 : program := fun _ a => match a with

(* 0x00142394: lsr w2,w0,#0x18 *)
(*    1319828: lsr w2,w0,#0x18 *)
| 0x142394 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x18 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x00142398: tbz w0,#0x1f,0x001423ac *)
(*    1319832: tbz w0,#0x1f,0x001423ac *)
| 0x142398 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x1423ac 64)
	) (* else *) (
		Nop
	)
)

(* 0x0014239c: lsr w3,w0,#0x10 *)
(*    1319836: lsr w3,w0,#0x10 *)
| 0x14239c => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x10 32)) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x001423a0: lsr w1,w0,#0x8 *)
(*    1319840: lsr w1,w0,#0x8 *)
| 0x1423a0 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x8 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x001423a4: cmp w2,#0xbf *)
(*    1319844: cmp w2,#0xbf *)
| 0x1423a4 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0xbf 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0xbf 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0xbf 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0xbf 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xbf 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001423a8: csel w2,w1,w3,hi *)
(*    1319848: csel w2,w1,w3,hi *)
| 0x1423a8 => Some (4,
	Move (V_TEMP 0x1a00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x1b00) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0x1a00))) $;
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X1)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1b00))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X3))
	) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1d900)))
)

(* 0x001423ac: mov w0,w2 *)
(*    1319852: mov w0,w2 *)
| 0x1423ac => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2)))
)

(* 0x001423b0: ret *)
(*    1319856: ret *)
| 0x1423b0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx inet_netof_armv8.
Proof. Picinae_typecheck. Qed.

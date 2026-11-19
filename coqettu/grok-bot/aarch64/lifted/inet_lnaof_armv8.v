(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: inet_lnaof
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition inet_lnaof_armv8 : program := fun _ a => match a with

(* 0x00142370: lsr w1,w0,#0x18 *)
(*    1319792: lsr w1,w0,#0x18 *)
| 0x142370 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x18 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x00142374: tbz w0,#0x1f,0x0014238c *)
(*    1319796: tbz w0,#0x1f,0x0014238c *)
| 0x142374 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x14238c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00142378: and w2,w0,#0xffff *)
(*    1319800: and w2,w0,#0xffff *)
| 0x142378 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xffff 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0014237c: cmp w1,#0xbf *)
(*    1319804: cmp w1,#0xbf *)
| 0x14237c => Some (4,
	Move (V_TEMP 0x1c500) (Word 0xbf 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0xbf 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0xbf 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0xbf 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xbf 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00142380: and w0,w0,#0xff *)
(*    1319808: and w0,w0,#0xff *)
| 0x142380 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xff 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00142384: csel w0,w0,w2,hi *)
(*    1319812: csel w0,w0,w2,hi *)
| 0x142384 => Some (4,
	Move (V_TEMP 0x1a00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x1b00) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0x1a00))) $;
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1b00))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X2))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1d900)))
)

(* 0x00142388: ret *)
(*    1319816: ret *)
| 0x142388 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0014238c: and w0,w0,#0xffffff *)
(*    1319820: and w0,w0,#0xffffff *)
| 0x14238c => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xffffff 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00142390: b 0x00142388 *)
(*    1319824: b 0x00142388 *)
| 0x142390 => Some (4,
	Jmp (Word 0x142388 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx inet_lnaof_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_setconcurrency
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_setconcurrency_armv8 : program := fun _ a => match a with

(* 0x00164410: cmp w0,#0x0 *)
(*    1459216: cmp w0,#0x0 *)
| 0x164410 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00164414: mov w0,#0xb *)
(*    1459220: mov w0,#0xb *)
| 0x164414 => Some (4,
	Move R_X0 (Word 0xb 64)
)

(* 0x00164418: csel w0,wzr,w0,eq *)
(*    1459224: csel w0,wzr,w0,eq *)
| 0x164418 => Some (4,
	Move (V_TEMP 0x180) (Word 0x0 32) $;
	Move (V_TEMP 0x1d900) (Var (V_TEMP 0x180)) $;
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X0))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1d900)))
)

(* 0x0016441c: mov w1,#0x16 *)
(*    1459228: mov w1,#0x16 *)
| 0x16441c => Some (4,
	Move R_X1 (Word 0x16 64)
)

(* 0x00164420: csel w0,w0,w1,ge *)
(*    1459232: csel w0,w0,w1,ge *)
| 0x164420 => Some (4,
	Move (V_TEMP 0x1d80) (BinOp OP_EQ (Var R_NG) (Var R_OV)) $;
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1d80))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1d900) (Extract 31 0 (Var R_X1))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1d900)))
)

(* 0x00164424: ret *)
(*    1459236: ret *)
| 0x164424 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_setconcurrency_armv8.
Proof. Picinae_typecheck. Qed.

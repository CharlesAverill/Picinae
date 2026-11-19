(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_barrierattr_setpshared
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_barrierattr_setpshared_armv8 : program := fun _ a => match a with

(* 0x00161728: cmp w1,#0x1 *)
(*    1447720: cmp w1,#0x1 *)
| 0x161728 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x1 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x1 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0016172c: b.hi 0x00161740 *)
(*    1447724: b.hi 0x00161740 *)
| 0x16172c => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x161740 64)
	) (* else *) (
		Nop
	)
)

(* 0x00161730: lsl w1,w1,#0x1f *)
(*    1447728: lsl w1,w1,#0x1f *)
| 0x161730 => Some (4,
	Move (V_TEMP 0x27e00) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X1)) (Word 0x1f 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27e00)))
)

(* 0x00161734: str w1,[x0] *)
(*    1447732: str w1,[x0] *)
| 0x161734 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x00161738: mov w0,#0x0 *)
(*    1447736: mov w0,#0x0 *)
| 0x161738 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0016173c: ret *)
(*    1447740: ret *)
| 0x16173c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00161740: mov w0,#0x16 *)
(*    1447744: mov w0,#0x16 *)
| 0x161740 => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x00161744: b 0x0016173c *)
(*    1447748: b 0x0016173c *)
| 0x161744 => Some (4,
	Jmp (Word 0x16173c 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_barrierattr_setpshared_armv8.
Proof. Picinae_typecheck. Qed.

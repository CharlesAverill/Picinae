(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_setinheritsched
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_setinheritsched_armv8 : program := fun _ a => match a with

(* 0x0016117c: cmp w1,#0x1 *)
(*    1446268: cmp w1,#0x1 *)
| 0x16117c => Some (4,
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

(* 0x00161180: b.hi 0x00161190 *)
(*    1446272: b.hi 0x00161190 *)
| 0x161180 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x161190 64)
	) (* else *) (
		Nop
	)
)

(* 0x00161184: str w1,[x0, #0x1c] *)
(*    1446276: str w1,[x0, #0x1c] *)
| 0x161184 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x1c 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6000)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x00161188: mov w0,#0x0 *)
(*    1446280: mov w0,#0x0 *)
| 0x161188 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0016118c: ret *)
(*    1446284: ret *)
| 0x16118c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00161190: mov w0,#0x16 *)
(*    1446288: mov w0,#0x16 *)
| 0x161190 => Some (4,
	Move R_X0 (Word 0x16 64)
)

(* 0x00161194: b 0x0016118c *)
(*    1446292: b 0x0016118c *)
| 0x161194 => Some (4,
	Jmp (Word 0x16118c 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_setinheritsched_armv8.
Proof. Picinae_typecheck. Qed.

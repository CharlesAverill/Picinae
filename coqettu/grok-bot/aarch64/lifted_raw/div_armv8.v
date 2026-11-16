(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: div
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition div_armv8 : program := fun _ a => match a with

(* 0x0015d170: sdiv w2,w0,w1 *)
(*    1429872: sdiv w2,w0,w1 *)
| 0x15d170 => Some (4,
	Move (V_TEMP 0x35f00) (Word 0x0 32) $;
	Move (V_TEMP 0x35f80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x35f80))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x35f00) (BinOp OP_SDIVIDE (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1)))
	) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x35f00)))
)

(* 0x0015d174: mov w3,w0 *)
(*    1429876: mov w3,w0 *)
| 0x15d174 => Some (4,
	Move R_X3 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X0)))
)

(* 0x0015d178: mov x0,#0x0 *)
(*    1429880: mov x0,#0x0 *)
| 0x15d178 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0015d17c: bfxil x0,x2,#0x0,#0x20 *)
(*    1429884: bfxil x0,x2,#0x0,#0x20 *)
| 0x15d17c => Some (4,
	Move (V_TEMP 0x15580) (BinOp OP_MINUS (Word 0x40 64) (Word 0x20 64)) $;
	Move (V_TEMP 0x15680) (BinOp OP_RSHIFT (Word 0xffffffffffffffff 64) (Var (V_TEMP 0x15580))) $;
	Move (V_TEMP 0x15700) (BinOp OP_RSHIFT (Var R_X2) (Word 0x0 64)) $;
	Move (V_TEMP 0x15800) (BinOp OP_AND (Var (V_TEMP 0x15700)) (Var (V_TEMP 0x15680))) $;
	Move (V_TEMP 0x15880) (UnOp OP_NOT (Var (V_TEMP 0x15680))) $;
	Move (V_TEMP 0x15900) (BinOp OP_AND (Var R_X0) (Var (V_TEMP 0x15880))) $;
	Move R_X0 (BinOp OP_OR (Var (V_TEMP 0x15900)) (Var (V_TEMP 0x15800)))
)

(* 0x0015d180: msub w2,w2,w1,w3 *)
(*    1429888: msub w2,w2,w1,w3 *)
| 0x15d180 => Some (4,
	Move (V_TEMP 0x2aa00) (BinOp OP_TIMES (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
	Move (V_TEMP 0x2ab00) (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x2aa00))) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2ab00)))
)

(* 0x0015d184: bfm x0,x2,#0x20,#0x1f *)
(*    1429892: bfm x0,x2,#0x20,#0x1f *)
| 0x15d184 => Some (4,
	Move (V_TEMP 0x14500) (Word 0xffffffff00000000 64) $;
	Move (V_TEMP 0x14580) (Word 0xffffffffffffffff 64) $;
	Move (V_TEMP 0x14600) (Var R_X0) $;
	Move (V_TEMP 0x14680) (Var R_X2) $;
	Move (V_TEMP 0x14700) (UnOp OP_NOT (Var (V_TEMP 0x14500))) $;
	Move (V_TEMP 0x14780) (BinOp OP_AND (Var (V_TEMP 0x14600)) (Var (V_TEMP 0x14700))) $;
	Move (V_TEMP 0x14800) (BinOp OP_RSHIFT (Var (V_TEMP 0x14680)) (Word 0x20 64)) $;
	Move (V_TEMP 0x14880) (BinOp OP_MINUS (Word 0x40 64) (Word 0x20 64)) $;
	Move (V_TEMP 0x14900) (BinOp OP_LSHIFT (Var (V_TEMP 0x14680)) (Var (V_TEMP 0x14880))) $;
	Move (V_TEMP 0x14980) (BinOp OP_OR (Var (V_TEMP 0x14800)) (Var (V_TEMP 0x14900))) $;
	Move (V_TEMP 0x14a00) (BinOp OP_AND (Var (V_TEMP 0x14980)) (Var (V_TEMP 0x14500))) $;
	Move (V_TEMP 0x14b00) (BinOp OP_OR (Var (V_TEMP 0x14780)) (Var (V_TEMP 0x14a00))) $;
	Move (V_TEMP 0x14b80) (UnOp OP_NOT (Var (V_TEMP 0x14580))) $;
	Move (V_TEMP 0x14c00) (BinOp OP_AND (Var (V_TEMP 0x14600)) (Var (V_TEMP 0x14b80))) $;
	Move (V_TEMP 0x14c80) (BinOp OP_AND (Var (V_TEMP 0x14b00)) (Var (V_TEMP 0x14580))) $;
	Move R_X0 (BinOp OP_OR (Var (V_TEMP 0x14c00)) (Var (V_TEMP 0x14c80)))
)

(* 0x0015d188: ret *)
(*    1429896: ret *)
| 0x15d188 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx div_armv8.
Proof. Picinae_typecheck. Qed.

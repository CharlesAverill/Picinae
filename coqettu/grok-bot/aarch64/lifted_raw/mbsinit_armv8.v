(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: mbsinit
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition mbsinit_armv8 : program := fun _ a => match a with

(* 0x0013edf4: cbz x0,0x0013ee08 *)
(*    1306100: cbz x0,0x0013ee08 *)
| 0x13edf4 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x13ee08 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013edf8: ldr w0,[x0] *)
(*    1306104: ldr w0,[x0] *)
| 0x13edf8 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0013edfc: cmp w0,#0x0 *)
(*    1306108: cmp w0,#0x0 *)
| 0x13edfc => Some (4,
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

(* 0x0013ee00: cset w0,eq *)
(*    1306112: cset w0,eq *)
| 0x13ee00 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var R_ZR))
)

(* 0x0013ee04: ret *)
(*    1306116: ret *)
| 0x13ee04 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0013ee08: mov w0,#0x1 *)
(*    1306120: mov w0,#0x1 *)
| 0x13ee08 => Some (4,
	Move R_X0 (Word 0x1 64)
)

(* 0x0013ee0c: b 0x0013ee04 *)
(*    1306124: b 0x0013ee04 *)
| 0x13ee0c => Some (4,
	Jmp (Word 0x13ee04 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx mbsinit_armv8.
Proof. Picinae_typecheck. Qed.

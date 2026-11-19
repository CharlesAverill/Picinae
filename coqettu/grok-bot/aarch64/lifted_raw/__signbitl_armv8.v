(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __signbitl
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __signbitl_armv8 : program := fun _ a => match a with

(* 0x0012c0fc: sub sp,sp,#0x10 *)
(*    1229052: sub sp,sp,#0x10 *)
| 0x12c0fc => Some (4,
	Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 0x10 64))
)

(* 0x0012c100: str q0,[sp] *)
(*    1229056: str q0,[sp] *)
| 0x12c100 => Some (4,
	Move (V_TEMP 0x6480) (Var R_SP) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6480)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x0012c104: ldr x0,[sp, #0x8] *)
(*    1229060: ldr x0,[sp, #0x8] *)
| 0x12c104 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0012c108: add sp,sp,#0x10 *)
(*    1229064: add sp,sp,#0x10 *)
| 0x12c108 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x10 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) (Var R_SP))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_SP (Var (V_TEMP 0x11b80))
)

(* 0x0012c10c: lsr x0,x0,#0x30 *)
(*    1229068: lsr x0,x0,#0x30 *)
| 0x12c10c => Some (4,
	Move R_X0 (BinOp OP_RSHIFT (Var R_X0) (Word 0x30 64))
)

(* 0x0012c110: lsr w0,w0,#0xf *)
(*    1229072: lsr w0,w0,#0xf *)
| 0x12c110 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0xf 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x0012c114: ret *)
(*    1229076: ret *)
| 0x12c114 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx __signbitl_armv8.
Proof. Picinae_typecheck. Qed.

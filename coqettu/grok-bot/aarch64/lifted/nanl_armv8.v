(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: nanl
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition nanl_armv8 : program := fun _ a => match a with

(* 0x00137d6c: adrp x0,0x16e000 *)
(*    1277292: adrp x0,0x16e000 *)
| 0x137d6c => Some (4,
	Move R_X0 (Word 0x16e000 64)
)

(* 0x00137d70: add x0,x0,#0x320 *)
(*    1277296: add x0,x0,#0x320 *)
| 0x137d70 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x320 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x00137d74: ldr q0,[x0] *)
(*    1277300: ldr q0,[x0] *)
| 0x137d74 => Some (4,
	Move (V_TEMP 0x6480) (Var R_X0) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (Var (V_TEMP 0x6480)) LittleE 16)) (Word 0 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 128 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 192 256)) (BinOp OP_AND (Var R_Z0) (Word 0x0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256)))
)

(* 0x00137d78: ret *)
(*    1277304: ret *)
| 0x137d78 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx nanl_armv8.
Proof. Picinae_typecheck. Qed.

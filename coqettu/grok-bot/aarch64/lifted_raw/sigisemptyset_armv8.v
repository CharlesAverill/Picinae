(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: sigisemptyset
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition sigisemptyset_armv8 : program := fun _ a => match a with

(* 0x00152320: ldr x0,[x0] *)
(*    1385248: ldr x0,[x0] *)
| 0x152320 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00152324: cmp x0,#0x0 *)
(*    1385252: cmp x0,#0x0 *)
| 0x152324 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X0) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00152328: cset w0,eq *)
(*    1385256: cset w0,eq *)
| 0x152328 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var R_ZR))
)

(* 0x0015232c: ret *)
(*    1385260: ret *)
| 0x15232c => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx sigisemptyset_armv8.
Proof. Picinae_typecheck. Qed.

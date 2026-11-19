(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __fwritable
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __fwritable_armv8 : program := fun _ a => match a with

(* 0x0015395c: ldr x0,[x0] *)
(*    1390940: ldr x0,[x0] *)
| 0x15395c => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x00153960: ubfx x0,x0,#0x3,#0x1 *)
(*    1390944: ubfx x0,x0,#0x3,#0x1 *)
| 0x153960 => Some (4,
	Move (V_TEMP 0x41100) (Var R_X0) $;
	Move (V_TEMP 0x41180) (BinOp OP_RSHIFT (Var (V_TEMP 0x41100)) (Word 0x3 64)) $;
	Move (V_TEMP 0x41200) (BinOp OP_MINUS (Word 0x40 64) (Word 0x3 64)) $;
	Move (V_TEMP 0x41280) (BinOp OP_LSHIFT (Var (V_TEMP 0x41100)) (Var (V_TEMP 0x41200))) $;
	Move (V_TEMP 0x41300) (BinOp OP_OR (Var (V_TEMP 0x41180)) (Var (V_TEMP 0x41280))) $;
	Move (V_TEMP 0x41400) (BinOp OP_AND (Var (V_TEMP 0x41300)) (Word 0xe000000000000001 64)) $;
	Move R_X0 (BinOp OP_AND (Var (V_TEMP 0x41400)) (Word 0x1 64))
)

(* 0x00153964: eor w0,w0,#0x1 *)
(*    1390948: eor w0,w0,#0x1 *)
| 0x153964 => Some (4,
	Move (V_TEMP 0x1fc00) (BinOp OP_XOR (Extract 31 0 (Var R_X0)) (Word 0x1 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1fc00)))
)

(* 0x00153968: ret *)
(*    1390952: ret *)
| 0x153968 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx __fwritable_armv8.
Proof. Picinae_typecheck. Qed.

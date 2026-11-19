(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: explicit_bzero
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition explicit_bzero_armv8 : program := fun _ a => match a with

(* 0x0015e108: stp x29,x30,[sp, #-0x10]! *)
(*    1433864: stp x29,x30,[sp, #-0x10]! *)
| 0x15e108 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015e10c: mov x2,x1 *)
(*    1433868: mov x2,x1 *)
| 0x15e10c => Some (4,
	Move R_X2 (Var R_X1)
)

(* 0x0015e110: mov w1,#0x0 *)
(*    1433872: mov w1,#0x0 *)
| 0x15e110 => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015e114: mov x29,sp *)
(*    1433876: mov x29,sp *)
| 0x15e114 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015e118: bl 0x00118400 *)
(*    1433880: bl 0x00118400 *)
| 0x15e118 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15e118 64) (Word 0x4 64)) $;
	Jmp (Word 0x118400 64)
)

(* 0x0015e11c: ldp x29,x30,[sp], #0x10 *)
(*    1433884: ldp x29,x30,[sp], #0x10 *)
| 0x15e11c => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015e120: ret *)
(*    1433888: ret *)
| 0x15e120 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx explicit_bzero_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strcpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcpy_armv8 : program := fun _ a => match a with

(* 0x0015eccc: stp x29,x30,[sp, #-0x20]! *)
(*    1436876: stp x29,x30,[sp, #-0x20]! *)
| 0x15eccc => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015ecd0: mov x29,sp *)
(*    1436880: mov x29,sp *)
| 0x15ecd0 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015ecd4: str x19,[sp, #0x10] *)
(*    1436884: str x19,[sp, #0x10] *)
| 0x15ecd4 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015ecd8: mov x19,x0 *)
(*    1436888: mov x19,x0 *)
| 0x15ecd8 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015ecdc: bl 0x0015e950 *)
(*    1436892: bl 0x0015e950 *)
| 0x15ecdc => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15ecdc 64) (Word 0x4 64)) $;
	Jmp (Word 0x15e950 64)
)

(* 0x0015ece0: mov x0,x19 *)
(*    1436896: mov x0,x19 *)
| 0x15ece0 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015ece4: ldr x19,[sp, #0x10] *)
(*    1436900: ldr x19,[sp, #0x10] *)
| 0x15ece4 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015ece8: ldp x29,x30,[sp], #0x20 *)
(*    1436904: ldp x29,x30,[sp], #0x20 *)
| 0x15ece8 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015ecec: ret *)
(*    1436908: ret *)
| 0x15ecec => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strcpy_armv8.
Proof. Picinae_typecheck. Qed.

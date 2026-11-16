(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strncpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strncpy_armv8 : program := fun _ a => match a with

(* 0x0015f14c: stp x29,x30,[sp, #-0x20]! *)
(*    1438028: stp x29,x30,[sp, #-0x20]! *)
| 0x15f14c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f150: mov x29,sp *)
(*    1438032: mov x29,sp *)
| 0x15f150 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015f154: str x19,[sp, #0x10] *)
(*    1438036: str x19,[sp, #0x10] *)
| 0x15f154 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015f158: mov x19,x0 *)
(*    1438040: mov x19,x0 *)
| 0x15f158 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015f15c: bl 0x0015e9c0 *)
(*    1438044: bl 0x0015e9c0 *)
| 0x15f15c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f15c 64) (Word 0x4 64)) $;
	Jmp (Word 0x15e9c0 64)
)

(* 0x0015f160: mov x0,x19 *)
(*    1438048: mov x0,x19 *)
| 0x15f160 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015f164: ldr x19,[sp, #0x10] *)
(*    1438052: ldr x19,[sp, #0x10] *)
| 0x15f164 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015f168: ldp x29,x30,[sp], #0x20 *)
(*    1438056: ldp x29,x30,[sp], #0x20 *)
| 0x15f168 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f16c: ret *)
(*    1438060: ret *)
| 0x15f16c => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strncpy_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: conjl
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition conjl_armv8 : program := fun _ a => match a with

(* 0x0011a854: sub sp,sp,#0x20 *)
(*    1157204: sub sp,sp,#0x20 *)
| 0x11a854 => Some (4,
	Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 0x20 64))
)

(* 0x0011a858: str q1,[sp, #0x10] *)
(*    1157208: str q1,[sp, #0x10] *)
| 0x11a858 => Some (4,
	Move (V_TEMP 0x6200) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6200)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z1))) LittleE 16)
)

(* 0x0011a85c: ldr x0,[sp, #0x10] *)
(*    1157212: ldr x0,[sp, #0x10] *)
| 0x11a85c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0011a860: str x0,[sp] *)
(*    1157216: str x0,[sp] *)
| 0x11a860 => Some (4,
	Move (V_TEMP 0x6400) (Var R_SP) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x0011a864: ldr x0,[sp, #0x18] *)
(*    1157220: ldr x0,[sp, #0x18] *)
| 0x11a864 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x18 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0011a868: eor x0,x0,#-0x8000000000000000 *)
(*    1157224: eor x0,x0,#-0x8000000000000000 *)
| 0x11a868 => Some (4,
	Move R_X0 (BinOp OP_XOR (Var R_X0) (Word 0x8000000000000000 64))
)

(* 0x0011a86c: str x0,[sp, #0x8] *)
(*    1157228: str x0,[sp, #0x8] *)
| 0x11a86c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x0011a870: ldr q1,[sp] *)
(*    1157232: ldr q1,[sp] *)
| 0x11a870 => Some (4,
	Move (V_TEMP 0x6480) (Var R_SP) $;
	Move R_Z1 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (Var (V_TEMP 0x6480)) LittleE 16)) (Word 0 256)) (BinOp OP_AND (Var R_Z1) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000 256))) $;
	Move R_Z1 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 128 256)) (BinOp OP_AND (Var R_Z1) (Word 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z1 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 192 256)) (BinOp OP_AND (Var R_Z1) (Word 0x0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256)))
)

(* 0x0011a874: add sp,sp,#0x20 *)
(*    1157236: add sp,sp,#0x20 *)
| 0x11a874 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x20 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) (Var R_SP))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_SP (Var (V_TEMP 0x11b80))
)

(* 0x0011a878: ret *)
(*    1157240: ret *)
| 0x11a878 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx conjl_armv8.
Proof. Picinae_typecheck. Qed.

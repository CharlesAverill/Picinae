(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: rand
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition rand_armv8 : program := fun _ a => match a with

(* 0x00147f0c: adrp x1,0x1c2000 *)
(*    1343244: adrp x1,0x1c2000 *)
| 0x147f0c => Some (4,
	Move R_X1 (Word 0x1c2000 64)
)

(* 0x00147f10: mov x2,#0x7f2d *)
(*    1343248: mov x2,#0x7f2d *)
| 0x147f10 => Some (4,
	Move R_X2 (Word 0x7f2d 64)
)

(* 0x00147f14: movk x2,#0x4c95, LSL #16 *)
(*    1343252: movk x2,#0x4c95, LSL #16 *)
| 0x147f14 => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X2) (Word 0xffffffff0000ffff 64)) $;
	Move R_X2 (BinOp OP_OR (Var R_X2) (Word 0x4c950000 64))
)

(* 0x00147f18: ldr x0,[x1, #0x598] *)
(*    1343256: ldr x0,[x1, #0x598] *)
| 0x147f18 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X1) (Word 0x598 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00147f1c: movk x2,#0xf42d, LSL #32 *)
(*    1343260: movk x2,#0xf42d, LSL #32 *)
| 0x147f1c => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X2) (Word 0xffff0000ffffffff 64)) $;
	Move R_X2 (BinOp OP_OR (Var R_X2) (Word 0xf42d00000000 64))
)

(* 0x00147f20: movk x2,#0x5851, LSL #48 *)
(*    1343264: movk x2,#0x5851, LSL #48 *)
| 0x147f20 => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X2) (Word 0xffffffffffff 64)) $;
	Move R_X2 (BinOp OP_OR (Var R_X2) (Word 0x5851000000000000 64))
)

(* 0x00147f24: mul x0,x0,x2 *)
(*    1343268: mul x0,x0,x2 *)
| 0x147f24 => Some (4,
	Move R_X0 (BinOp OP_TIMES (Var R_X0) (Var R_X2))
)

(* 0x00147f28: add x0,x0,#0x1 *)
(*    1343272: add x0,x0,#0x1 *)
| 0x147f28 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x00147f2c: str x0,[x1, #0x598] *)
(*    1343276: str x0,[x1, #0x598] *)
| 0x147f2c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X1) (Word 0x598 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x00147f30: lsr x0,x0,#0x21 *)
(*    1343280: lsr x0,x0,#0x21 *)
| 0x147f30 => Some (4,
	Move R_X0 (BinOp OP_RSHIFT (Var R_X0) (Word 0x21 64))
)

(* 0x00147f34: ret *)
(*    1343284: ret *)
| 0x147f34 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *               Static Memory Hypotheses                  *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx rand_armv8.
Proof. Picinae_typecheck. Qed.

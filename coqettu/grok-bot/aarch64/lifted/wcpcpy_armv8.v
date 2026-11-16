(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcpcpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcpcpy_armv8 : program := fun _ a => match a with

(* 0x0015fa04: stp x29,x30,[sp, #-0x20]! *)
(*    1440260: stp x29,x30,[sp, #-0x20]! *)
| 0x15fa04 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fa08: mov x29,sp *)
(*    1440264: mov x29,sp *)
| 0x15fa08 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015fa0c: stp x19,x20,[sp, #0x10] *)
(*    1440268: stp x19,x20,[sp, #0x10] *)
| 0x15fa0c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fa10: mov x20,x1 *)
(*    1440272: mov x20,x1 *)
| 0x15fa10 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015fa14: bl 0x0015fb2c *)
(*    1440276: bl 0x0015fb2c *)
| 0x15fa14 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fa14 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fb2c 64)
)

(* 0x0015fa18: mov x19,x0 *)
(*    1440280: mov x19,x0 *)
| 0x15fa18 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015fa1c: mov x0,x20 *)
(*    1440284: mov x0,x20 *)
| 0x15fa1c => Some (4,
	Move R_X0 (Var R_X20)
)

(* 0x0015fa20: bl 0x0015fc18 *)
(*    1440288: bl 0x0015fc18 *)
| 0x15fa20 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fa20 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fc18 64)
)

(* 0x0015fa24: add x0,x19,x0, LSL #0x2 *)
(*    1440292: add x0,x19,x0, LSL #0x2 *)
| 0x15fa24 => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X0) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f80) (Var (V_TEMP 0x4400)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x12080))
)

(* 0x0015fa28: ldp x19,x20,[sp, #0x10] *)
(*    1440296: ldp x19,x20,[sp, #0x10] *)
| 0x15fa28 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015fa2c: ldp x29,x30,[sp], #0x20 *)
(*    1440300: ldp x29,x30,[sp], #0x20 *)
| 0x15fa2c => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015fa30: ret *)
(*    1440304: ret *)
| 0x15fa30 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcpcpy_armv8.
Proof. Picinae_typecheck. Qed.

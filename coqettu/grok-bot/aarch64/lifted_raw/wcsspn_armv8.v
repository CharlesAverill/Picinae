(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcsspn
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsspn_armv8 : program := fun _ a => match a with

(* 0x0015fe6c: stp x29,x30,[sp, #-0x30]! *)
(*    1441388: stp x29,x30,[sp, #-0x30]! *)
| 0x15fe6c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fe70: mov x29,sp *)
(*    1441392: mov x29,sp *)
| 0x15fe70 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015fe74: stp x19,x20,[sp, #0x10] *)
(*    1441396: stp x19,x20,[sp, #0x10] *)
| 0x15fe74 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fe78: mov x20,x1 *)
(*    1441400: mov x20,x1 *)
| 0x15fe78 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015fe7c: mov x19,x0 *)
(*    1441404: mov x19,x0 *)
| 0x15fe7c => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015fe80: str x21,[sp, #0x20] *)
(*    1441408: str x21,[sp, #0x20] *)
| 0x15fe80 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X21)) LittleE 8)
)

(* 0x0015fe84: mov x21,x0 *)
(*    1441412: mov x21,x0 *)
| 0x15fe84 => Some (4,
	Move R_X21 (Var R_X0)
)

(* 0x0015fe88: b 0x0015fe90 *)
(*    1441416: b 0x0015fe90 *)
| 0x15fe88 => Some (4,
	Jmp (Word 0x15fe90 64)
)

(* 0x0015fe8c: add x19,x19,#0x4 *)
(*    1441420: add x19,x19,#0x4 *)
| 0x15fe8c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x11b80))
)

(* 0x0015fe90: ldr w1,[x19] *)
(*    1441424: ldr w1,[x19] *)
| 0x15fe90 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X19) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0015fe94: mov x0,x20 *)
(*    1441428: mov x0,x20 *)
| 0x15fe94 => Some (4,
	Move R_X0 (Var R_X20)
)

(* 0x0015fe98: cbz w1,0x0015fea4 *)
(*    1441432: cbz w1,0x0015fea4 *)
| 0x15fe98 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15fea4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fe9c: bl 0x0015fab4 *)
(*    1441436: bl 0x0015fab4 *)
| 0x15fe9c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fe9c 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fab4 64)
)

(* 0x0015fea0: cbnz x0,0x0015fe8c *)
(*    1441440: cbnz x0,0x0015fe8c *)
| 0x15fea0 => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x15fe8c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fea4: sub x0,x19,x21 *)
(*    1441444: sub x0,x19,x21 *)
| 0x15fea4 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X19) (Var R_X21))
)

(* 0x0015fea8: ldr x21,[sp, #0x20] *)
(*    1441448: ldr x21,[sp, #0x20] *)
| 0x15fea8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move R_X21 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015feac: asr x0,x0,#0x2 *)
(*    1441452: asr x0,x0,#0x2 *)
| 0x15feac => Some (4,
	Move R_X0 (BinOp OP_ARSHIFT (Var R_X0) (Word 0x2 64))
)

(* 0x0015feb0: ldp x19,x20,[sp, #0x10] *)
(*    1441456: ldp x19,x20,[sp, #0x10] *)
| 0x15feb0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015feb4: ldp x29,x30,[sp], #0x30 *)
(*    1441460: ldp x29,x30,[sp], #0x30 *)
| 0x15feb4 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015feb8: ret *)
(*    1441464: ret *)
| 0x15feb8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcsspn_armv8.
Proof. Picinae_typecheck. Qed.

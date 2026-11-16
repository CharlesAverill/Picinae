(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strnlen
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strnlen_armv8 : program := fun _ a => match a with

(* 0x0015f1c0: stp x29,x30,[sp, #-0x20]! *)
(*    1438144: stp x29,x30,[sp, #-0x20]! *)
| 0x15f1c0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f1c4: mov x2,x1 *)
(*    1438148: mov x2,x1 *)
| 0x15f1c4 => Some (4,
	Move R_X2 (Var R_X1)
)

(* 0x0015f1c8: mov x29,sp *)
(*    1438152: mov x29,sp *)
| 0x15f1c8 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015f1cc: stp x19,x20,[sp, #0x10] *)
(*    1438156: stp x19,x20,[sp, #0x10] *)
| 0x15f1cc => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f1d0: mov x19,x0 *)
(*    1438160: mov x19,x0 *)
| 0x15f1d0 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015f1d4: mov x20,x1 *)
(*    1438164: mov x20,x1 *)
| 0x15f1d4 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015f1d8: mov w1,#0x0 *)
(*    1438168: mov w1,#0x0 *)
| 0x15f1d8 => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015f1dc: bl 0x0015e1ec *)
(*    1438172: bl 0x0015e1ec *)
| 0x15f1dc => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f1dc 64) (Word 0x4 64)) $;
	Jmp (Word 0x15e1ec 64)
)

(* 0x0015f1e0: sub x19,x0,x19 *)
(*    1438176: sub x19,x0,x19 *)
| 0x15f1e0 => Some (4,
	Move R_X19 (BinOp OP_MINUS (Var R_X0) (Var R_X19))
)

(* 0x0015f1e4: cmp x0,#0x0 *)
(*    1438180: cmp x0,#0x0 *)
| 0x15f1e4 => Some (4,
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

(* 0x0015f1e8: csel x0,x19,x20,ne *)
(*    1438184: csel x0,x19,x20,ne *)
| 0x15f1e8 => Some (4,
	Move (V_TEMP 0x1680) (UnOp OP_NOT (Var R_ZR)) $;
	Move (V_TEMP 0x1da80) (Var R_X19) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1680))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1da80) (Var R_X20)
	) $;
	Move R_X0 (Var (V_TEMP 0x1da80))
)

(* 0x0015f1ec: ldp x19,x20,[sp, #0x10] *)
(*    1438188: ldp x19,x20,[sp, #0x10] *)
| 0x15f1ec => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015f1f0: ldp x29,x30,[sp], #0x20 *)
(*    1438192: ldp x29,x30,[sp], #0x20 *)
| 0x15f1f0 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f1f4: ret *)
(*    1438196: ret *)
| 0x15f1f4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strnlen_armv8.
Proof. Picinae_typecheck. Qed.

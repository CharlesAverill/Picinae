(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strpbrk
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strpbrk_armv8 : program := fun _ a => match a with

(* 0x0015f1f8: stp x29,x30,[sp, #-0x20]! *)
(*    1438200: stp x29,x30,[sp, #-0x20]! *)
| 0x15f1f8 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f1fc: mov x29,sp *)
(*    1438204: mov x29,sp *)
| 0x15f1fc => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015f200: str x19,[sp, #0x10] *)
(*    1438208: str x19,[sp, #0x10] *)
| 0x15f200 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015f204: mov x19,x0 *)
(*    1438212: mov x19,x0 *)
| 0x15f204 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015f208: bl 0x0015ecf0 *)
(*    1438216: bl 0x0015ecf0 *)
| 0x15f208 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f208 64) (Word 0x4 64)) $;
	Jmp (Word 0x15ecf0 64)
)

(* 0x0015f20c: add x1,x19,x0 *)
(*    1438220: add x1,x19,x0 *)
| 0x15f20c => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X0) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x12080))
)

(* 0x0015f210: ldrb w0,[x19, x0, LSL ] *)
(*    1438224: ldrb w0,[x19, x0, LSL ] *)
| 0x15f210 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015f214: ldr x19,[sp, #0x10] *)
(*    1438228: ldr x19,[sp, #0x10] *)
| 0x15f214 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015f218: cmp w0,#0x0 *)
(*    1438232: cmp w0,#0x0 *)
| 0x15f218 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f21c: csel x0,x1,xzr,ne *)
(*    1438236: csel x0,x1,xzr,ne *)
| 0x15f21c => Some (4,
	Move (V_TEMP 0x1680) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x1da80) (Var R_X1) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1680))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1da80) (Word 0x0 64)
	) $;
	Move R_X0 (Var (V_TEMP 0x1da80))
)

(* 0x0015f220: ldp x29,x30,[sp], #0x20 *)
(*    1438240: ldp x29,x30,[sp], #0x20 *)
| 0x15f220 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f224: ret *)
(*    1438244: ret *)
| 0x15f224 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strpbrk_armv8.
Proof. Picinae_typecheck. Qed.

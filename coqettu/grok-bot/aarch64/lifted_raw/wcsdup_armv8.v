(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: wcsdup
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsdup_armv8 : program := fun _ a => match a with

(* 0x0015fbd0: stp x29,x30,[sp, #-0x30]! *)
(*    1440720: stp x29,x30,[sp, #-0x30]! *)
| 0x15fbd0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015fbd4: mov x29,sp *)
(*    1440724: mov x29,sp *)
| 0x15fbd4 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015fbd8: str x19,[sp, #0x10] *)
(*    1440728: str x19,[sp, #0x10] *)
| 0x15fbd8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015fbdc: mov x19,x0 *)
(*    1440732: mov x19,x0 *)
| 0x15fbdc => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015fbe0: bl 0x0015fc18 *)
(*    1440736: bl 0x0015fc18 *)
| 0x15fbe0 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fbe0 64) (Word 0x4 64)) $;
	Jmp (Word 0x15fc18 64)
)

(* 0x0015fbe4: add x2,x0,#0x1 *)
(*    1440740: add x2,x0,#0x1 *)
| 0x15fbe4 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015fbe8: str x2,[sp, #0x28] *)
(*    1440744: str x2,[sp, #0x28] *)
| 0x15fbe8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x28 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X2)) LittleE 8)
)

(* 0x0015fbec: lsl x0,x2,#0x2 *)
(*    1440748: lsl x0,x2,#0x2 *)
| 0x15fbec => Some (4,
	Move R_X0 (BinOp OP_LSHIFT (Var R_X2) (Word 0x2 64))
)

(* 0x0015fbf0: bl 0x001135d0 *)
(*    1440752: bl 0x001135d0 *)
| 0x15fbf0 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15fbf0 64) (Word 0x4 64)) $;
	Jmp (Word 0x1135d0 64)
)

(* 0x0015fbf4: cbz x0,0x0015fc0c *)
(*    1440756: cbz x0,0x0015fc0c *)
| 0x15fbf4 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15fc0c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015fbf8: ldr x2,[sp, #0x28] *)
(*    1440760: ldr x2,[sp, #0x28] *)
| 0x15fbf8 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x28 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015fbfc: mov x1,x19 *)
(*    1440764: mov x1,x19 *)
| 0x15fbfc => Some (4,
	Move R_X1 (Var R_X19)
)

(* 0x0015fc00: ldr x19,[sp, #0x10] *)
(*    1440768: ldr x19,[sp, #0x10] *)
| 0x15fc00 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015fc04: ldp x29,x30,[sp], #0x30 *)
(*    1440772: ldp x29,x30,[sp], #0x30 *)
| 0x15fc04 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015fc08: b 0x0016022c *)
(*    1440776: b 0x0016022c *)
| 0x15fc08 => Some (4,
	Jmp (Word 0x16022c 64)
)

(* 0x0015fc0c: ldr x19,[sp, #0x10] *)
(*    1440780: ldr x19,[sp, #0x10] *)
| 0x15fc0c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015fc10: ldp x29,x30,[sp], #0x30 *)
(*    1440784: ldp x29,x30,[sp], #0x30 *)
| 0x15fc10 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015fc14: ret *)
(*    1440788: ret *)
| 0x15fc14 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx wcsdup_armv8.
Proof. Picinae_typecheck. Qed.

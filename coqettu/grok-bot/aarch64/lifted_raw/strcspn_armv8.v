(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strcspn
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcspn_armv8 : program := fun _ a => match a with

(* 0x0015ecf0: stp x29,x30,[sp, #-0x50]! *)
(*    1436912: stp x29,x30,[sp, #-0x50]! *)
| 0x15ecf0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffb0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015ecf4: mov x3,x1 *)
(*    1436916: mov x3,x1 *)
| 0x15ecf4 => Some (4,
	Move R_X3 (Var R_X1)
)

(* 0x0015ecf8: mov x29,sp *)
(*    1436920: mov x29,sp *)
| 0x15ecf8 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015ecfc: str x19,[sp, #0x10] *)
(*    1436924: str x19,[sp, #0x10] *)
| 0x15ecfc => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015ed00: mov x19,x0 *)
(*    1436928: mov x19,x0 *)
| 0x15ed00 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015ed04: ldrb w1,[x1] *)
(*    1436932: ldrb w1,[x1] *)
| 0x15ed04 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ed08: cbz w1,0x0015ed14 *)
(*    1436936: cbz w1,0x0015ed14 *)
| 0x15ed08 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15ed14 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ed0c: ldrb w0,[x3, #0x1] *)
(*    1436940: ldrb w0,[x3, #0x1] *)
| 0x15ed0c => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X3) (Word 0x1 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ed10: cbnz w0,0x0015ed2c *)
(*    1436944: cbnz w0,0x0015ed2c *)
| 0x15ed10 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15ed2c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ed14: mov x0,x19 *)
(*    1436948: mov x0,x19 *)
| 0x15ed14 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015ed18: bl 0x0015ebf4 *)
(*    1436952: bl 0x0015ebf4 *)
| 0x15ed18 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15ed18 64) (Word 0x4 64)) $;
	Jmp (Word 0x15ebf4 64)
)

(* 0x0015ed1c: sub x0,x0,x19 *)
(*    1436956: sub x0,x0,x19 *)
| 0x15ed1c => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X0) (Var R_X19))
)

(* 0x0015ed20: ldr x19,[sp, #0x10] *)
(*    1436960: ldr x19,[sp, #0x10] *)
| 0x15ed20 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015ed24: ldp x29,x30,[sp], #0x50 *)
(*    1436964: ldp x29,x30,[sp], #0x50 *)
| 0x15ed24 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x50 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015ed28: ret *)
(*    1436968: ret *)
| 0x15ed28 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015ed2c: add x5,sp,#0x30 *)
(*    1436972: add x5,sp,#0x30 *)
| 0x15ed2c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x30 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) (Var R_SP))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 0x11b80))
)

(* 0x0015ed30: mov x2,#0x20 *)
(*    1436976: mov x2,#0x20 *)
| 0x15ed30 => Some (4,
	Move R_X2 (Word 0x20 64)
)

(* 0x0015ed34: mov x0,x5 *)
(*    1436980: mov x0,x5 *)
| 0x15ed34 => Some (4,
	Move R_X0 (Var R_X5)
)

(* 0x0015ed38: mov w1,#0x0 *)
(*    1436984: mov w1,#0x0 *)
| 0x15ed38 => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015ed3c: stp x5,x3,[sp, #0x20] *)
(*    1436988: stp x5,x3,[sp, #0x20] *)
| 0x15ed3c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X5) $;
	Move (V_TEMP 0x39f80) (Var R_X3) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015ed40: bl 0x00118400 *)
(*    1436992: bl 0x00118400 *)
| 0x15ed40 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15ed40 64) (Word 0x4 64)) $;
	Jmp (Word 0x118400 64)
)

(* 0x0015ed44: ldp x5,x3,[sp, #0x20] *)
(*    1436996: ldp x5,x3,[sp, #0x20] *)
| 0x15ed44 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X5 (Var (V_TEMP 0x24180)) $;
	Move R_X3 (Var (V_TEMP 0x24300))
)

(* 0x0015ed48: mov x0,#0x1 *)
(*    1437000: mov x0,#0x1 *)
| 0x15ed48 => Some (4,
	Move R_X0 (Word 0x1 64)
)

(* 0x0015ed4c: ldrb w1,[x3] *)
(*    1437004: ldrb w1,[x3] *)
| 0x15ed4c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X3) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ed50: add x3,x3,#0x1 *)
(*    1437008: add x3,x3,#0x1 *)
| 0x15ed50 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x0015ed54: ubfx x2,x1,#0x6,#0x2 *)
(*    1437012: ubfx x2,x1,#0x6,#0x2 *)
| 0x15ed54 => Some (4,
	Move (V_TEMP 0x41100) (Var R_X1) $;
	Move (V_TEMP 0x41180) (BinOp OP_RSHIFT (Var (V_TEMP 0x41100)) (Word 0x6 64)) $;
	Move (V_TEMP 0x41200) (BinOp OP_MINUS (Word 0x40 64) (Word 0x6 64)) $;
	Move (V_TEMP 0x41280) (BinOp OP_LSHIFT (Var (V_TEMP 0x41100)) (Var (V_TEMP 0x41200))) $;
	Move (V_TEMP 0x41300) (BinOp OP_OR (Var (V_TEMP 0x41180)) (Var (V_TEMP 0x41280))) $;
	Move (V_TEMP 0x41400) (BinOp OP_AND (Var (V_TEMP 0x41300)) (Word 0xfc00000000000003 64)) $;
	Move R_X2 (BinOp OP_AND (Var (V_TEMP 0x41400)) (Word 0x3 64))
)

(* 0x0015ed58: lsl x4,x0,x1 *)
(*    1437016: lsl x4,x0,x1 *)
| 0x15ed58 => Some (4,
	Move (V_TEMP 0x27a00) (BinOp OP_AND (Var R_X1) (Word 0x3f 64)) $;
	Move R_X4 (BinOp OP_LSHIFT (Var R_X0) (Var (V_TEMP 0x27a00)))
)

(* 0x0015ed5c: cbz w1,0x0015ed98 *)
(*    1437020: cbz w1,0x0015ed98 *)
| 0x15ed5c => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15ed98 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ed60: lsl x2,x2,#0x3 *)
(*    1437024: lsl x2,x2,#0x3 *)
| 0x15ed60 => Some (4,
	Move R_X2 (BinOp OP_LSHIFT (Var R_X2) (Word 0x3 64))
)

(* 0x0015ed64: ldr x1,[x5, x2, LSL #0x0] *)
(*    1437028: ldr x1,[x5, x2, LSL #0x0] *)
| 0x15ed64 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x6d00))) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 8)
)

(* 0x0015ed68: orr x4,x4,x1 *)
(*    1437032: orr x4,x4,x1 *)
| 0x15ed68 => Some (4,
	Move R_X4 (BinOp OP_OR (Var R_X4) (Var R_X1))
)

(* 0x0015ed6c: str x4,[x5, x2, LSL #0x0] *)
(*    1437036: str x4,[x5, x2, LSL #0x0] *)
| 0x15ed6c => Some (4,
	Move (V_TEMP 0x3a280) (Var R_X4) $;
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3a280))) LittleE 8)
)

(* 0x0015ed70: b 0x0015ed4c *)
(*    1437040: b 0x0015ed4c *)
| 0x15ed70 => Some (4,
	Jmp (Word 0x15ed4c 64)
)

(* 0x0015ed74: add x3,x3,#0x1 *)
(*    1437044: add x3,x3,#0x1 *)
| 0x15ed74 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x0015ed78: ldrb w1,[x3] *)
(*    1437048: ldrb w1,[x3] *)
| 0x15ed78 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X3) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ed7c: ubfx x2,x1,#0x6,#0x2 *)
(*    1437052: ubfx x2,x1,#0x6,#0x2 *)
| 0x15ed7c => Some (4,
	Move (V_TEMP 0x41100) (Var R_X1) $;
	Move (V_TEMP 0x41180) (BinOp OP_RSHIFT (Var (V_TEMP 0x41100)) (Word 0x6 64)) $;
	Move (V_TEMP 0x41200) (BinOp OP_MINUS (Word 0x40 64) (Word 0x6 64)) $;
	Move (V_TEMP 0x41280) (BinOp OP_LSHIFT (Var (V_TEMP 0x41100)) (Var (V_TEMP 0x41200))) $;
	Move (V_TEMP 0x41300) (BinOp OP_OR (Var (V_TEMP 0x41180)) (Var (V_TEMP 0x41280))) $;
	Move (V_TEMP 0x41400) (BinOp OP_AND (Var (V_TEMP 0x41300)) (Word 0xfc00000000000003 64)) $;
	Move R_X2 (BinOp OP_AND (Var (V_TEMP 0x41400)) (Word 0x3 64))
)

(* 0x0015ed80: cbz w1,0x0015ed90 *)
(*    1437056: cbz w1,0x0015ed90 *)
| 0x15ed80 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15ed90 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ed84: ldr x2,[x5, x2, LSL #0x3] *)
(*    1437060: ldr x2,[x5, x2, LSL #0x3] *)
| 0x15ed84 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x3 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x6d00))) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 8)
)

(* 0x0015ed88: lsr x1,x2,x1 *)
(*    1437064: lsr x1,x2,x1 *)
| 0x15ed88 => Some (4,
	Move (V_TEMP 0x28300) (BinOp OP_AND (Var R_X1) (Word 0x3f 64)) $;
	Move R_X1 (BinOp OP_RSHIFT (Var R_X2) (Var (V_TEMP 0x28300)))
)

(* 0x0015ed8c: tbz w1,#0x0,0x0015ed74 *)
(*    1437068: tbz w1,#0x0,0x0015ed74 *)
| 0x15ed8c => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x15ed74 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ed90: sub x0,x3,x19 *)
(*    1437072: sub x0,x3,x19 *)
| 0x15ed90 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X3) (Var R_X19))
)

(* 0x0015ed94: b 0x0015ed20 *)
(*    1437076: b 0x0015ed20 *)
| 0x15ed94 => Some (4,
	Jmp (Word 0x15ed20 64)
)

(* 0x0015ed98: mov x3,x19 *)
(*    1437080: mov x3,x19 *)
| 0x15ed98 => Some (4,
	Move R_X3 (Var R_X19)
)

(* 0x0015ed9c: b 0x0015ed78 *)
(*    1437084: b 0x0015ed78 *)
| 0x15ed9c => Some (4,
	Jmp (Word 0x15ed78 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx strcspn_armv8.
Proof. Picinae_typecheck. Qed.

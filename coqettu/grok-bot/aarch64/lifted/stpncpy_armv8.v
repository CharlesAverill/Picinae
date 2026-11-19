(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: stpncpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition stpncpy_armv8 : program := fun _ a => match a with

(* 0x0015e9c0: stp x29,x30,[sp, #-0x20]! *)
(*    1436096: stp x29,x30,[sp, #-0x20]! *)
| 0x15e9c0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015e9c4: eor x3,x1,x0 *)
(*    1436100: eor x3,x1,x0 *)
| 0x15e9c4 => Some (4,
	Move R_X3 (BinOp OP_XOR (Var R_X1) (Var R_X0))
)

(* 0x0015e9c8: mov x29,sp *)
(*    1436104: mov x29,sp *)
| 0x15e9c8 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015e9cc: str x19,[sp, #0x10] *)
(*    1436108: str x19,[sp, #0x10] *)
| 0x15e9cc => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X19)) LittleE 8)
)

(* 0x0015e9d0: tst x3,#0x7 *)
(*    1436112: tst x3,#0x7 *)
| 0x15e9d0 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X3) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e9d4: b.eq 0x0015e9ec *)
(*    1436116: b.eq 0x0015e9ec *)
| 0x15e9d4 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e9ec 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e9d8: mov x19,x0 *)
(*    1436120: mov x19,x0 *)
| 0x15e9d8 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015e9dc: b 0x0015ea64 *)
(*    1436124: b 0x0015ea64 *)
| 0x15e9dc => Some (4,
	Jmp (Word 0x15ea64 64)
)

(* 0x0015e9e0: sub x2,x2,#0x1 *)
(*    1436128: sub x2,x2,#0x1 *)
| 0x15e9e0 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0015e9e4: add x1,x1,#0x1 *)
(*    1436132: add x1,x1,#0x1 *)
| 0x15e9e4 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015e9e8: add x0,x0,#0x1 *)
(*    1436136: add x0,x0,#0x1 *)
| 0x15e9e8 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015e9ec: tst x1,#0x7 *)
(*    1436140: tst x1,#0x7 *)
| 0x15e9ec => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X1) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e9f0: b.eq 0x0015ea08 *)
(*    1436144: b.eq 0x0015ea08 *)
| 0x15e9f0 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ea08 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e9f4: cbz x2,0x0015ea94 *)
(*    1436148: cbz x2,0x0015ea94 *)
| 0x15e9f4 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15ea94 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e9f8: ldrb w3,[x1] *)
(*    1436152: ldrb w3,[x1] *)
| 0x15e9f8 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015e9fc: strb w3,[x0] *)
(*    1436156: strb w3,[x0] *)
| 0x15e9fc => Some (4,
	Move (V_TEMP 0x3a300) (Extract 31 0 (Var R_X3)) $;
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6280)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a300)))) LittleE 1)
)

(* 0x0015ea00: cbnz w3,0x0015e9e0 *)
(*    1436160: cbnz w3,0x0015e9e0 *)
| 0x15ea00 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15e9e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ea04: b 0x0015ea0c *)
(*    1436164: b 0x0015ea0c *)
| 0x15ea04 => Some (4,
	Jmp (Word 0x15ea0c 64)
)

(* 0x0015ea08: cbz x2,0x0015ea94 *)
(*    1436168: cbz x2,0x0015ea94 *)
| 0x15ea08 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15ea94 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ea0c: ldrb w3,[x1] *)
(*    1436172: ldrb w3,[x1] *)
| 0x15ea0c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ea10: mov x19,x0 *)
(*    1436176: mov x19,x0 *)
| 0x15ea10 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015ea14: cbz w3,0x0015ea78 *)
(*    1436180: cbz w3,0x0015ea78 *)
| 0x15ea14 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15ea78 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ea18: and x5,x2,#-0x8 *)
(*    1436184: and x5,x2,#-0x8 *)
| 0x15ea18 => Some (4,
	Move R_X5 (BinOp OP_AND (Var R_X2) (Word 0xfffffffffffffff8 64))
)

(* 0x0015ea1c: orr x7,xzr,#-0x101010101010102 *)
(*    1436188: orr x7,xzr,#-0x101010101010102 *)
| 0x15ea1c => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X7 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0xfefefefefefefefe 64))
)

(* 0x0015ea20: add x6,x1,x2 *)
(*    1436192: add x6,x1,x2 *)
| 0x15ea20 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X6 (Var (V_TEMP 0x12080))
)

(* 0x0015ea24: add x5,x1,x5 *)
(*    1436196: add x5,x1,x5 *)
| 0x15ea24 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X5) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 0x12080))
)

(* 0x0015ea28: movk x7,#0xfeff *)
(*    1436200: movk x7,#0xfeff *)
| 0x15ea28 => Some (4,
	Move R_X7 (BinOp OP_AND (Var R_X7) (Word 0xffffffffffff0000 64)) $;
	Move R_X7 (BinOp OP_OR (Var R_X7) (Word 0xfeff 64))
)

(* 0x0015ea2c: b 0x0015ea38 *)
(*    1436204: b 0x0015ea38 *)
| 0x15ea2c => Some (4,
	Jmp (Word 0x15ea38 64)
)

(* 0x0015ea30: add x1,x1,#0x8 *)
(*    1436208: add x1,x1,#0x8 *)
| 0x15ea30 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015ea34: str x4,[x0], #0x8 *)
(*    1436212: str x4,[x0], #0x8 *)
| 0x15ea34 => Some (4,
	Move (V_TEMP 0x3a180) (Var R_X4) $;
	Move (V_TEMP 0x7000) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3a180))) LittleE 8)
)

(* 0x0015ea38: sub x2,x6,x1 *)
(*    1436216: sub x2,x6,x1 *)
| 0x15ea38 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X6) (Var R_X1))
)

(* 0x0015ea3c: cmp x1,x5 *)
(*    1436220: cmp x1,x5 *)
| 0x15ea3c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X5) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X5)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X5)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X1) (Var R_X5)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ea40: b.eq 0x0015e9d8 *)
(*    1436224: b.eq 0x0015e9d8 *)
| 0x15ea40 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e9d8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ea44: ldr x4,[x1] *)
(*    1436228: ldr x4,[x1] *)
| 0x15ea44 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move R_X4 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0015ea48: add x3,x4,x7 *)
(*    1436232: add x3,x4,x7 *)
| 0x15ea48 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X7) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) (Var R_X4))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x12080))
)

(* 0x0015ea4c: bic x3,x3,x4 *)
(*    1436236: bic x3,x3,x4 *)
| 0x15ea4c => Some (4,
	Move (V_TEMP 0x15e00) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 0x15f00) (BinOp OP_XOR (Var R_X4) (Var (V_TEMP 0x15e00))) $;
	Move R_X3 (BinOp OP_AND (Var R_X3) (Var (V_TEMP 0x15f00)))
)

(* 0x0015ea50: tst x3,#-0x7f7f7f7f7f7f7f80 *)
(*    1436240: tst x3,#-0x7f7f7f7f7f7f7f80 *)
| 0x15ea50 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X3) (Word 0x8080808080808080 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015ea54: b.eq 0x0015ea30 *)
(*    1436244: b.eq 0x0015ea30 *)
| 0x15ea54 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ea30 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ea58: b 0x0015e9d8 *)
(*    1436248: b 0x0015e9d8 *)
| 0x15ea58 => Some (4,
	Jmp (Word 0x15e9d8 64)
)

(* 0x0015ea5c: sub x2,x2,#0x1 *)
(*    1436252: sub x2,x2,#0x1 *)
| 0x15ea5c => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0015ea60: add x19,x19,#0x1 *)
(*    1436256: add x19,x19,#0x1 *)
| 0x15ea60 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x11b80))
)

(* 0x0015ea64: cbz x2,0x0015ea78 *)
(*    1436260: cbz x2,0x0015ea78 *)
| 0x15ea64 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15ea78 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ea68: ldrb w0,[x1] *)
(*    1436264: ldrb w0,[x1] *)
| 0x15ea68 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ea6c: add x1,x1,#0x1 *)
(*    1436268: add x1,x1,#0x1 *)
| 0x15ea6c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015ea70: strb w0,[x19] *)
(*    1436272: strb w0,[x19] *)
| 0x15ea70 => Some (4,
	Move (V_TEMP 0x3a300) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x6280) (Var R_X19) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6280)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a300)))) LittleE 1)
)

(* 0x0015ea74: cbnz w0,0x0015ea5c *)
(*    1436276: cbnz w0,0x0015ea5c *)
| 0x15ea74 => Some (4,
	Move (V_TEMP 0x18980) (BinOp OP_NEQ (Extract 31 0 (Var R_X0)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18980))) (
		Jmp (Word 0x15ea5c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ea78: mov x0,x19 *)
(*    1436280: mov x0,x19 *)
| 0x15ea78 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015ea7c: mov w1,#0x0 *)
(*    1436284: mov w1,#0x0 *)
| 0x15ea7c => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015ea80: bl 0x00118400 *)
(*    1436288: bl 0x00118400 *)
| 0x15ea80 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15ea80 64) (Word 0x4 64)) $;
	Jmp (Word 0x118400 64)
)

(* 0x0015ea84: mov x0,x19 *)
(*    1436292: mov x0,x19 *)
| 0x15ea84 => Some (4,
	Move R_X0 (Var R_X19)
)

(* 0x0015ea88: ldr x19,[sp, #0x10] *)
(*    1436296: ldr x19,[sp, #0x10] *)
| 0x15ea88 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move R_X19 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015ea8c: ldp x29,x30,[sp], #0x20 *)
(*    1436300: ldp x29,x30,[sp], #0x20 *)
| 0x15ea8c => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015ea90: ret *)
(*    1436304: ret *)
| 0x15ea90 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015ea94: mov x19,x0 *)
(*    1436308: mov x19,x0 *)
| 0x15ea94 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015ea98: b 0x0015ea78 *)
(*    1436312: b 0x0015ea78 *)
| 0x15ea98 => Some (4,
	Jmp (Word 0x15ea78 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx stpncpy_armv8.
Proof. Picinae_typecheck. Qed.

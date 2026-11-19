(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: dn_skipname
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition dn_skipname_armv8 : program := fun _ a => match a with

(* 0x0013ff00: mov x3,x0 *)
(*    1310464: mov x3,x0 *)
| 0x13ff00 => Some (4,
	Move R_X3 (Var R_X0)
)

(* 0x0013ff04: cmp x3,x1 *)
(*    1310468: cmp x3,x1 *)
| 0x13ff04 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X1) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var R_X1)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var R_X1)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X3) (Var R_X1)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0013ff08: b.cs 0x0013ff60 *)
(*    1310472: b.cs 0x0013ff60 *)
| 0x13ff08 => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Jmp (Word 0x13ff60 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013ff0c: ldrb w2,[x3] *)
(*    1310476: ldrb w2,[x3] *)
| 0x13ff0c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X3) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0013ff10: cbz w2,0x0013ff3c *)
(*    1310480: cbz w2,0x0013ff3c *)
| 0x13ff10 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x13ff3c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013ff14: cmp w2,#0xbf *)
(*    1310484: cmp w2,#0xbf *)
| 0x13ff14 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0xbf 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0xbf 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0xbf 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0xbf 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xbf 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0013ff18: b.hi 0x0013ff48 *)
(*    1310488: b.hi 0x0013ff48 *)
| 0x13ff18 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x13ff48 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013ff1c: add w4,w2,#0x1 *)
(*    1310492: add w4,w2,#0x1 *)
| 0x13ff1c => Some (4,
	Move (V_TEMP 0x11680) (Word 0x1 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x11680))) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x11680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11680)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11780) (BinOp OP_PLUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x11680))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11780)))
)

(* 0x0013ff20: sub x5,x1,x3 *)
(*    1310496: sub x5,x1,x3 *)
| 0x13ff20 => Some (4,
	Move R_X5 (BinOp OP_MINUS (Var R_X1) (Var R_X3))
)

(* 0x0013ff24: sxtw x4,w4 *)
(*    1310500: sxtw x4,w4 *)
| 0x13ff24 => Some (4,
	Move R_X4 (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_X4)))
)

(* 0x0013ff28: cmp x5,x4 *)
(*    1310504: cmp x5,x4 *)
| 0x13ff28 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X4) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X5) (Var R_X4)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X5) (Var R_X4)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X5) (Var R_X4)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0013ff2c: b.lt 0x0013ff60 *)
(*    1310508: b.lt 0x0013ff60 *)
| 0x13ff2c => Some (4,
	Move (V_TEMP 0x1200) (BinOp OP_NEQ (Var R_NG) (Var R_OV)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1200))) (
		Jmp (Word 0x13ff60 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013ff30: add x2,x2,#0x1 *)
(*    1310512: add x2,x2,#0x1 *)
| 0x13ff30 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0013ff34: add x3,x3,x2 *)
(*    1310516: add x3,x3,x2 *)
| 0x13ff34 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x12080))
)

(* 0x0013ff38: b 0x0013ff04 *)
(*    1310520: b 0x0013ff04 *)
| 0x13ff38 => Some (4,
	Jmp (Word 0x13ff04 64)
)

(* 0x0013ff3c: sub x0,x3,x0 *)
(*    1310524: sub x0,x3,x0 *)
| 0x13ff3c => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X3) (Var R_X0))
)

(* 0x0013ff40: add w0,w0,#0x1 *)
(*    1310528: add w0,w0,#0x1 *)
| 0x13ff40 => Some (4,
	Move (V_TEMP 0x11680) (Word 0x1 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11680)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11780) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11780)))
)

(* 0x0013ff44: b 0x0013ff64 *)
(*    1310532: b 0x0013ff64 *)
| 0x13ff44 => Some (4,
	Jmp (Word 0x13ff64 64)
)

(* 0x0013ff48: add x2,x3,#0x1 *)
(*    1310536: add x2,x3,#0x1 *)
| 0x13ff48 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0013ff4c: sub x0,x3,x0 *)
(*    1310540: sub x0,x3,x0 *)
| 0x13ff4c => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X3) (Var R_X0))
)

(* 0x0013ff50: add w0,w0,#0x2 *)
(*    1310544: add w0,w0,#0x2 *)
| 0x13ff50 => Some (4,
	Move (V_TEMP 0x11680) (Word 0x2 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11680)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11780) (BinOp OP_PLUS (Extract 31 0 (Var R_X0)) (Var (V_TEMP 0x11680))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11780)) (Word 0x0 32))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11780)))
)

(* 0x0013ff54: cmp x1,x2 *)
(*    1310548: cmp x1,x2 *)
| 0x13ff54 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X2)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X2)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X1) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0013ff58: csinv w0,w0,wzr,hi *)
(*    1310552: csinv w0,w0,wzr,hi *)
| 0x13ff58 => Some (4,
	Move (V_TEMP 0x1a00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x1b00) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0x1a00))) $;
	Move (V_TEMP 0x0) (Word 0x0 32) $;
	Move (V_TEMP 0x1e600) (Extract 31 0 (Var R_X0)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1b00))) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1e600) (UnOp OP_NOT (Var (V_TEMP 0x0)))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1e600)))
)

(* 0x0013ff5c: b 0x0013ff64 *)
(*    1310556: b 0x0013ff64 *)
| 0x13ff5c => Some (4,
	Jmp (Word 0x13ff64 64)
)

(* 0x0013ff60: mov w0,#0xffffffff *)
(*    1310560: mov w0,#0xffffffff *)
| 0x13ff60 => Some (4,
	Move R_X0 (Word 0xffffffff 64)
)

(* 0x0013ff64: ret *)
(*    1310564: ret *)
| 0x13ff64 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx dn_skipname_armv8.
Proof. Picinae_typecheck. Qed.

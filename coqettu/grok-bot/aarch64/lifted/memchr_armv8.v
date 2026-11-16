(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: memchr
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition memchr_armv8 : program := fun _ a => match a with

(* 0x0015e1ec: mov x3,x0 *)
(*    1434092: mov x3,x0 *)
| 0x15e1ec => Some (4,
	Move R_X3 (Var R_X0)
)

(* 0x0015e1f0: and w1,w1,#0xff *)
(*    1434096: and w1,w1,#0xff *)
| 0x15e1f0 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Word 0xff 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0015e1f4: b 0x0015e200 *)
(*    1434100: b 0x0015e200 *)
| 0x15e1f4 => Some (4,
	Jmp (Word 0x15e200 64)
)

(* 0x0015e1f8: add x3,x3,#0x1 *)
(*    1434104: add x3,x3,#0x1 *)
| 0x15e1f8 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x0015e1fc: sub x2,x2,#0x1 *)
(*    1434108: sub x2,x2,#0x1 *)
| 0x15e1fc => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0015e200: tst x3,#0x7 *)
(*    1434112: tst x3,#0x7 *)
| 0x15e200 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X3) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e204: b.eq 0x0015e248 *)
(*    1434116: b.eq 0x0015e248 *)
| 0x15e204 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e248 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e208: cbz x2,0x0015e2a0 *)
(*    1434120: cbz x2,0x0015e2a0 *)
| 0x15e208 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15e2a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e20c: ldrb w0,[x3] *)
(*    1434124: ldrb w0,[x3] *)
| 0x15e20c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X3) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015e210: cmp w0,w1 *)
(*    1434128: cmp w0,w1 *)
| 0x15e210 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e214: b.ne 0x0015e1f8 *)
(*    1434132: b.ne 0x0015e1f8 *)
| 0x15e214 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15e1f8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e218: ldrb w0,[x3] *)
(*    1434136: ldrb w0,[x3] *)
| 0x15e218 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X3) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015e21c: cmp w0,w1 *)
(*    1434140: cmp w0,w1 *)
| 0x15e21c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e220: b.eq 0x0015e27c *)
(*    1434144: b.eq 0x0015e27c *)
| 0x15e220 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e27c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e224: sxtw x6,w1 *)
(*    1434148: sxtw x6,w1 *)
| 0x15e224 => Some (4,
	Move R_X6 (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_X1)))
)

(* 0x0015e228: orr x4,xzr,#0x101010101010101 *)
(*    1434152: orr x4,xzr,#0x101010101010101 *)
| 0x15e228 => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X4 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0x101010101010101 64))
)

(* 0x0015e22c: and x0,x2,#-0x8 *)
(*    1434156: and x0,x2,#-0x8 *)
| 0x15e22c => Some (4,
	Move R_X0 (BinOp OP_AND (Var R_X2) (Word 0xfffffffffffffff8 64))
)

(* 0x0015e230: orr x8,xzr,#-0x101010101010102 *)
(*    1434160: orr x8,xzr,#-0x101010101010102 *)
| 0x15e230 => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X8 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0xfefefefefefefefe 64))
)

(* 0x0015e234: add x7,x3,x2 *)
(*    1434164: add x7,x3,x2 *)
| 0x15e234 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X7 (Var (V_TEMP 0x12080))
)

(* 0x0015e238: add x0,x3,x0 *)
(*    1434168: add x0,x3,x0 *)
| 0x15e238 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X0) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x12080))
)

(* 0x0015e23c: mul x6,x6,x4 *)
(*    1434172: mul x6,x6,x4 *)
| 0x15e23c => Some (4,
	Move R_X6 (BinOp OP_TIMES (Var R_X6) (Var R_X4))
)

(* 0x0015e240: movk x8,#0xfeff *)
(*    1434176: movk x8,#0xfeff *)
| 0x15e240 => Some (4,
	Move R_X8 (BinOp OP_AND (Var R_X8) (Word 0xffffffffffff0000 64)) $;
	Move R_X8 (BinOp OP_OR (Var R_X8) (Word 0xfeff 64))
)

(* 0x0015e244: b 0x0015e258 *)
(*    1434180: b 0x0015e258 *)
| 0x15e244 => Some (4,
	Jmp (Word 0x15e258 64)
)

(* 0x0015e248: mov x0,#0x0 *)
(*    1434184: mov x0,#0x0 *)
| 0x15e248 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0015e24c: cbnz x2,0x0015e218 *)
(*    1434188: cbnz x2,0x0015e218 *)
| 0x15e24c => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x15e218 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e250: b 0x0015e2a4 *)
(*    1434192: b 0x0015e2a4 *)
| 0x15e250 => Some (4,
	Jmp (Word 0x15e2a4 64)
)

(* 0x0015e254: add x3,x3,#0x8 *)
(*    1434196: add x3,x3,#0x8 *)
| 0x15e254 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x0015e258: sub x2,x7,x3 *)
(*    1434200: sub x2,x7,x3 *)
| 0x15e258 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X7) (Var R_X3))
)

(* 0x0015e25c: cmp x3,x0 *)
(*    1434204: cmp x3,x0 *)
| 0x15e25c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X0) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var R_X0)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X3) (Var R_X0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X3) (Var R_X0)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e260: b.eq 0x0015e288 *)
(*    1434208: b.eq 0x0015e288 *)
| 0x15e260 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e288 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e264: ldr x4,[x3] *)
(*    1434212: ldr x4,[x3] *)
| 0x15e264 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X3) $;
	Move R_X4 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0015e268: eor x4,x6,x4 *)
(*    1434216: eor x4,x6,x4 *)
| 0x15e268 => Some (4,
	Move R_X4 (BinOp OP_XOR (Var R_X6) (Var R_X4))
)

(* 0x0015e26c: add x5,x4,x8 *)
(*    1434220: add x5,x4,x8 *)
| 0x15e26c => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X8) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) (Var R_X4))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 0x12080))
)

(* 0x0015e270: bic x4,x5,x4 *)
(*    1434224: bic x4,x5,x4 *)
| 0x15e270 => Some (4,
	Move (V_TEMP 0x15e00) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 0x15f00) (BinOp OP_XOR (Var R_X4) (Var (V_TEMP 0x15e00))) $;
	Move R_X4 (BinOp OP_AND (Var R_X5) (Var (V_TEMP 0x15f00)))
)

(* 0x0015e274: tst x4,#-0x7f7f7f7f7f7f7f80 *)
(*    1434228: tst x4,#-0x7f7f7f7f7f7f7f80 *)
| 0x15e274 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X4) (Word 0x8080808080808080 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e278: b.eq 0x0015e254 *)
(*    1434232: b.eq 0x0015e254 *)
| 0x15e278 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e254 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e27c: mov x0,x3 *)
(*    1434236: mov x0,x3 *)
| 0x15e27c => Some (4,
	Move R_X0 (Var R_X3)
)

(* 0x0015e280: b 0x0015e288 *)
(*    1434240: b 0x0015e288 *)
| 0x15e280 => Some (4,
	Jmp (Word 0x15e288 64)
)

(* 0x0015e284: add x0,x0,#0x1 *)
(*    1434244: add x0,x0,#0x1 *)
| 0x15e284 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015e288: cbz x2,0x0015e2a0 *)
(*    1434248: cbz x2,0x0015e2a0 *)
| 0x15e288 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15e2a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e28c: ldrb w3,[x0] *)
(*    1434252: ldrb w3,[x0] *)
| 0x15e28c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015e290: sub x2,x2,#0x1 *)
(*    1434256: sub x2,x2,#0x1 *)
| 0x15e290 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0015e294: cmp w3,w1 *)
(*    1434260: cmp w3,w1 *)
| 0x15e294 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X3)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e298: b.ne 0x0015e284 *)
(*    1434264: b.ne 0x0015e284 *)
| 0x15e298 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15e284 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e29c: b 0x0015e2a4 *)
(*    1434268: b 0x0015e2a4 *)
| 0x15e29c => Some (4,
	Jmp (Word 0x15e2a4 64)
)

(* 0x0015e2a0: mov x0,#0x0 *)
(*    1434272: mov x0,#0x0 *)
| 0x15e2a0 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0015e2a4: ret *)
(*    1434276: ret *)
| 0x15e2a4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx memchr_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: memccpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition memccpy_armv8 : program := fun _ a => match a with

(* 0x0015e128: eor x4,x1,x0 *)
(*    1433896: eor x4,x1,x0 *)
| 0x15e128 => Some (4,
	Move R_X4 (BinOp OP_XOR (Var R_X1) (Var R_X0))
)

(* 0x0015e12c: and w2,w2,#0xff *)
(*    1433900: and w2,w2,#0xff *)
| 0x15e12c => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X2)) (Word 0xff 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x0015e130: tst x4,#0x7 *)
(*    1433904: tst x4,#0x7 *)
| 0x15e130 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X4) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e134: b.eq 0x0015e140 *)
(*    1433908: b.eq 0x0015e140 *)
| 0x15e134 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e140 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e138: b 0x0015e1c0 *)
(*    1433912: b 0x0015e1c0 *)
| 0x15e138 => Some (4,
	Jmp (Word 0x15e1c0 64)
)

(* 0x0015e13c: add x0,x0,#0x1 *)
(*    1433916: add x0,x0,#0x1 *)
| 0x15e13c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015e140: tst x1,#0x7 *)
(*    1433920: tst x1,#0x7 *)
| 0x15e140 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X1) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e144: b.eq 0x0015e168 *)
(*    1433924: b.eq 0x0015e168 *)
| 0x15e144 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e168 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e148: cbz x3,0x0015e1e4 *)
(*    1433928: cbz x3,0x0015e1e4 *)
| 0x15e148 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X3) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15e1e4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e14c: ldrb w4,[x1] *)
(*    1433932: ldrb w4,[x1] *)
| 0x15e14c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015e150: sub x3,x3,#0x1 *)
(*    1433936: sub x3,x3,#0x1 *)
| 0x15e150 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X3) (Word 0x1 64))
)

(* 0x0015e154: strb w4,[x0] *)
(*    1433940: strb w4,[x0] *)
| 0x15e154 => Some (4,
	Move (V_TEMP 0x3a300) (Extract 31 0 (Var R_X4)) $;
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6280)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a300)))) LittleE 1)
)

(* 0x0015e158: add x1,x1,#0x1 *)
(*    1433944: add x1,x1,#0x1 *)
| 0x15e158 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015e15c: cmp w4,w2 *)
(*    1433948: cmp w4,w2 *)
| 0x15e15c => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X4)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X4)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X2))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e160: b.ne 0x0015e13c *)
(*    1433952: b.ne 0x0015e13c *)
| 0x15e160 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15e13c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e164: b 0x0015e1dc *)
(*    1433956: b 0x0015e1dc *)
| 0x15e164 => Some (4,
	Jmp (Word 0x15e1dc 64)
)

(* 0x0015e168: sxtw x8,w2 *)
(*    1433960: sxtw x8,w2 *)
| 0x15e168 => Some (4,
	Move R_X8 (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_X2)))
)

(* 0x0015e16c: orr x4,xzr,#0x101010101010101 *)
(*    1433964: orr x4,xzr,#0x101010101010101 *)
| 0x15e16c => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X4 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0x101010101010101 64))
)

(* 0x0015e170: and x7,x3,#-0x8 *)
(*    1433968: and x7,x3,#-0x8 *)
| 0x15e170 => Some (4,
	Move R_X7 (BinOp OP_AND (Var R_X3) (Word 0xfffffffffffffff8 64))
)

(* 0x0015e174: orr x10,xzr,#-0x101010101010102 *)
(*    1433972: orr x10,xzr,#-0x101010101010102 *)
| 0x15e174 => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X10 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0xfefefefefefefefe 64))
)

(* 0x0015e178: add x9,x1,x3 *)
(*    1433976: add x9,x1,x3 *)
| 0x15e178 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X3) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X9 (Var (V_TEMP 0x12080))
)

(* 0x0015e17c: add x7,x1,x7 *)
(*    1433980: add x7,x1,x7 *)
| 0x15e17c => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X7) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X7 (Var (V_TEMP 0x12080))
)

(* 0x0015e180: mul x8,x8,x4 *)
(*    1433984: mul x8,x8,x4 *)
| 0x15e180 => Some (4,
	Move R_X8 (BinOp OP_TIMES (Var R_X8) (Var R_X4))
)

(* 0x0015e184: movk x10,#0xfeff *)
(*    1433988: movk x10,#0xfeff *)
| 0x15e184 => Some (4,
	Move R_X10 (BinOp OP_AND (Var R_X10) (Word 0xffffffffffff0000 64)) $;
	Move R_X10 (BinOp OP_OR (Var R_X10) (Word 0xfeff 64))
)

(* 0x0015e188: b 0x0015e194 *)
(*    1433992: b 0x0015e194 *)
| 0x15e188 => Some (4,
	Jmp (Word 0x15e194 64)
)

(* 0x0015e18c: add x1,x1,#0x8 *)
(*    1433996: add x1,x1,#0x8 *)
| 0x15e18c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015e190: str x6,[x0], #0x8 *)
(*    1434000: str x6,[x0], #0x8 *)
| 0x15e190 => Some (4,
	Move (V_TEMP 0x3a180) (Var R_X6) $;
	Move (V_TEMP 0x7000) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3a180))) LittleE 8)
)

(* 0x0015e194: sub x3,x9,x1 *)
(*    1434004: sub x3,x9,x1 *)
| 0x15e194 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X9) (Var R_X1))
)

(* 0x0015e198: cmp x1,x7 *)
(*    1434008: cmp x1,x7 *)
| 0x15e198 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X7) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X7)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X1) (Var R_X7)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X7) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X1) (Var R_X7)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e19c: b.eq 0x0015e1c0 *)
(*    1434012: b.eq 0x0015e1c0 *)
| 0x15e19c => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e1c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e1a0: ldr x6,[x1] *)
(*    1434016: ldr x6,[x1] *)
| 0x15e1a0 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move R_X6 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0015e1a4: eor x5,x6,x8 *)
(*    1434020: eor x5,x6,x8 *)
| 0x15e1a4 => Some (4,
	Move R_X5 (BinOp OP_XOR (Var R_X6) (Var R_X8))
)

(* 0x0015e1a8: add x4,x5,x10 *)
(*    1434024: add x4,x5,x10 *)
| 0x15e1a8 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X10) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 0x12080))
)

(* 0x0015e1ac: bic x4,x4,x5 *)
(*    1434028: bic x4,x4,x5 *)
| 0x15e1ac => Some (4,
	Move (V_TEMP 0x15e00) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 0x15f00) (BinOp OP_XOR (Var R_X5) (Var (V_TEMP 0x15e00))) $;
	Move R_X4 (BinOp OP_AND (Var R_X4) (Var (V_TEMP 0x15f00)))
)

(* 0x0015e1b0: tst x4,#-0x7f7f7f7f7f7f7f80 *)
(*    1434032: tst x4,#-0x7f7f7f7f7f7f7f80 *)
| 0x15e1b0 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X4) (Word 0x8080808080808080 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e1b4: b.eq 0x0015e18c *)
(*    1434036: b.eq 0x0015e18c *)
| 0x15e1b4 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e18c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e1b8: b 0x0015e1c0 *)
(*    1434040: b 0x0015e1c0 *)
| 0x15e1b8 => Some (4,
	Jmp (Word 0x15e1c0 64)
)

(* 0x0015e1bc: add x0,x0,#0x1 *)
(*    1434044: add x0,x0,#0x1 *)
| 0x15e1bc => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015e1c0: cbz x3,0x0015e1e4 *)
(*    1434048: cbz x3,0x0015e1e4 *)
| 0x15e1c0 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X3) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15e1e4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e1c4: ldrb w4,[x1] *)
(*    1434052: ldrb w4,[x1] *)
| 0x15e1c4 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015e1c8: sub x3,x3,#0x1 *)
(*    1434056: sub x3,x3,#0x1 *)
| 0x15e1c8 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X3) (Word 0x1 64))
)

(* 0x0015e1cc: strb w4,[x0] *)
(*    1434060: strb w4,[x0] *)
| 0x15e1cc => Some (4,
	Move (V_TEMP 0x3a300) (Extract 31 0 (Var R_X4)) $;
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6280)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a300)))) LittleE 1)
)

(* 0x0015e1d0: add x1,x1,#0x1 *)
(*    1434064: add x1,x1,#0x1 *)
| 0x15e1d0 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015e1d4: cmp w4,w2 *)
(*    1434068: cmp w4,w2 *)
| 0x15e1d4 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X4)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X4)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X4)) (Extract 31 0 (Var R_X2))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e1d8: b.ne 0x0015e1bc *)
(*    1434072: b.ne 0x0015e1bc *)
| 0x15e1d8 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15e1bc 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e1dc: add x0,x0,#0x1 *)
(*    1434076: add x0,x0,#0x1 *)
| 0x15e1dc => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015e1e0: ret *)
(*    1434080: ret *)
| 0x15e1e0 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015e1e4: mov x0,#0x0 *)
(*    1434084: mov x0,#0x0 *)
| 0x15e1e4 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0015e1e8: b 0x0015e1e0 *)
(*    1434088: b 0x0015e1e0 *)
| 0x15e1e8 => Some (4,
	Jmp (Word 0x15e1e0 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx memccpy_armv8.
Proof. Picinae_typecheck. Qed.

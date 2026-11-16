(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strchrnul
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strchrnul_armv8 : program := fun _ a => match a with

(* 0x0015ebf4: ands w1,w1,#0xff *)
(*    1436660: ands w1,w1,#0xff *)
| 0x15ebf4 => Some (4,
	Move (V_TEMP 0x12780) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Word 0xff 32)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12780)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12780)) (Word 0x0 32))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12780))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015ebf8: mov x2,x0 *)
(*    1436664: mov x2,x0 *)
| 0x15ebf8 => Some (4,
	Move R_X2 (Var R_X0)
)

(* 0x0015ebfc: b.eq 0x0015ec20 *)
(*    1436668: b.eq 0x0015ec20 *)
| 0x15ebfc => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ec20 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ec00: tst x2,#0x7 *)
(*    1436672: tst x2,#0x7 *)
| 0x15ec00 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X2) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015ec04: b.eq 0x0015ec44 *)
(*    1436676: b.eq 0x0015ec44 *)
| 0x15ec04 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ec44 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ec08: ldrb w0,[x2] *)
(*    1436680: ldrb w0,[x2] *)
| 0x15ec08 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X2) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ec0c: cmp w0,#0x0 *)
(*    1436684: cmp w0,#0x0 *)
| 0x15ec0c => Some (4,
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

(* 0x0015ec10: ccmp w0,w1,#0x4,ne *)
(*    1436688: ccmp w0,w1,#0x4,ne *)
| 0x15ec10 => Some (4,
	Move (V_TEMP 0x1680) (UnOp OP_NOT (Var R_ZR)) $;
	Move (V_TEMP 0x19d80) (Var (V_TEMP 0x1680)) $;
	Move (V_TEMP 0x19e00) (Word 0x4 8) $;
	Move (V_TEMP 0xe380) (BinOp OP_AND (Var (V_TEMP 0x19e00)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe380)) (Word 0x8 8))) $;
	Move (V_TEMP 0xe480) (BinOp OP_AND (Var (V_TEMP 0x19e00)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe480)) (Word 0x4 8))) $;
	Move (V_TEMP 0xe580) (BinOp OP_AND (Var (V_TEMP 0x19e00)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe580)) (Word 0x2 8))) $;
	Move (V_TEMP 0xe680) (BinOp OP_AND (Var (V_TEMP 0x19e00)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe680)) (Word 0x1 8))) $;
	Move (V_TEMP 0x19e80) (UnOp OP_NOT (Var (V_TEMP 0x19d80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x19e80))) (
		Jmp (Word 0x15ec14 64)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x19f80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x19f80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x19f80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ec14: b.eq 0x0015ec9c *)
(*    1436692: b.eq 0x0015ec9c *)
| 0x15ec14 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15ec9c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ec18: add x2,x2,#0x1 *)
(*    1436696: add x2,x2,#0x1 *)
| 0x15ec18 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015ec1c: b 0x0015ec00 *)
(*    1436700: b 0x0015ec00 *)
| 0x15ec1c => Some (4,
	Jmp (Word 0x15ec00 64)
)

(* 0x0015ec20: stp x29,x30,[sp, #-0x20]! *)
(*    1436704: stp x29,x30,[sp, #-0x20]! *)
| 0x15ec20 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015ec24: mov x29,sp *)
(*    1436708: mov x29,sp *)
| 0x15ec24 => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015ec28: str x0,[sp, #0x18] *)
(*    1436712: str x0,[sp, #0x18] *)
| 0x15ec28 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x18 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x0015ec2c: bl 0x0015efa8 *)
(*    1436716: bl 0x0015efa8 *)
| 0x15ec2c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15ec2c 64) (Word 0x4 64)) $;
	Jmp (Word 0x15efa8 64)
)

(* 0x0015ec30: ldr x2,[sp, #0x18] *)
(*    1436720: ldr x2,[sp, #0x18] *)
| 0x15ec30 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x18 64)) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015ec34: ldp x29,x30,[sp], #0x20 *)
(*    1436724: ldp x29,x30,[sp], #0x20 *)
| 0x15ec34 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015ec38: add x2,x2,x0 *)
(*    1436728: add x2,x2,x0 *)
| 0x15ec38 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X0) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x12080))
)

(* 0x0015ec3c: mov x0,x2 *)
(*    1436732: mov x0,x2 *)
| 0x15ec3c => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015ec40: ret *)
(*    1436736: ret *)
| 0x15ec40 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015ec44: sxtw x6,w1 *)
(*    1436740: sxtw x6,w1 *)
| 0x15ec44 => Some (4,
	Move R_X6 (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_X1)))
)

(* 0x0015ec48: orr x0,xzr,#0x101010101010101 *)
(*    1436744: orr x0,xzr,#0x101010101010101 *)
| 0x15ec48 => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X0 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0x101010101010101 64))
)

(* 0x0015ec4c: orr x7,xzr,#-0x101010101010102 *)
(*    1436748: orr x7,xzr,#-0x101010101010102 *)
| 0x15ec4c => Some (4,
	Move (V_TEMP 0x580) (Word 0x0 64) $;
	Move R_X7 (BinOp OP_OR (Var (V_TEMP 0x580)) (Word 0xfefefefefefefefe 64))
)

(* 0x0015ec50: movk x7,#0xfeff *)
(*    1436752: movk x7,#0xfeff *)
| 0x15ec50 => Some (4,
	Move R_X7 (BinOp OP_AND (Var R_X7) (Word 0xffffffffffff0000 64)) $;
	Move R_X7 (BinOp OP_OR (Var R_X7) (Word 0xfeff 64))
)

(* 0x0015ec54: mul x6,x6,x0 *)
(*    1436756: mul x6,x6,x0 *)
| 0x15ec54 => Some (4,
	Move R_X6 (BinOp OP_TIMES (Var R_X6) (Var R_X0))
)

(* 0x0015ec58: ldr x3,[x2] *)
(*    1436760: ldr x3,[x2] *)
| 0x15ec58 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X2) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x0015ec5c: eor x5,x3,x6 *)
(*    1436764: eor x5,x3,x6 *)
| 0x15ec5c => Some (4,
	Move R_X5 (BinOp OP_XOR (Var R_X3) (Var R_X6))
)

(* 0x0015ec60: eon x4,x3,x6 *)
(*    1436768: eon x4,x3,x6 *)
| 0x15ec60 => Some (4,
	Move (V_TEMP 0x1f900) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 0x1fa00) (BinOp OP_XOR (Var R_X6) (Var (V_TEMP 0x1f900))) $;
	Move R_X4 (BinOp OP_XOR (Var R_X3) (Var (V_TEMP 0x1fa00)))
)

(* 0x0015ec64: add x5,x5,x7 *)
(*    1436772: add x5,x5,x7 *)
| 0x15ec64 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X7) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 0x12080))
)

(* 0x0015ec68: add x0,x3,x7 *)
(*    1436776: add x0,x3,x7 *)
| 0x15ec68 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X7) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x12080))
)

(* 0x0015ec6c: and x4,x4,x5 *)
(*    1436780: and x4,x4,x5 *)
| 0x15ec6c => Some (4,
	Move R_X4 (BinOp OP_AND (Var R_X4) (Var R_X5))
)

(* 0x0015ec70: bic x0,x0,x3 *)
(*    1436784: bic x0,x0,x3 *)
| 0x15ec70 => Some (4,
	Move (V_TEMP 0x15e00) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 0x15f00) (BinOp OP_XOR (Var R_X3) (Var (V_TEMP 0x15e00))) $;
	Move R_X0 (BinOp OP_AND (Var R_X0) (Var (V_TEMP 0x15f00)))
)

(* 0x0015ec74: orr x0,x0,x4 *)
(*    1436788: orr x0,x0,x4 *)
| 0x15ec74 => Some (4,
	Move R_X0 (BinOp OP_OR (Var R_X0) (Var R_X4))
)

(* 0x0015ec78: tst x0,#-0x7f7f7f7f7f7f7f80 *)
(*    1436792: tst x0,#-0x7f7f7f7f7f7f7f80 *)
| 0x15ec78 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X0) (Word 0x8080808080808080 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015ec7c: b.ne 0x0015ec8c *)
(*    1436796: b.ne 0x0015ec8c *)
| 0x15ec7c => Some (4,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15ec8c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ec80: add x2,x2,#0x8 *)
(*    1436800: add x2,x2,#0x8 *)
| 0x15ec80 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015ec84: b 0x0015ec58 *)
(*    1436804: b 0x0015ec58 *)
| 0x15ec84 => Some (4,
	Jmp (Word 0x15ec58 64)
)

(* 0x0015ec88: add x2,x2,#0x1 *)
(*    1436808: add x2,x2,#0x1 *)
| 0x15ec88 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015ec8c: ldrb w0,[x2] *)
(*    1436812: ldrb w0,[x2] *)
| 0x15ec8c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X2) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015ec90: cmp w0,#0x0 *)
(*    1436816: cmp w0,#0x0 *)
| 0x15ec90 => Some (4,
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

(* 0x0015ec94: ccmp w0,w1,#0x4,ne *)
(*    1436820: ccmp w0,w1,#0x4,ne *)
| 0x15ec94 => Some (4,
	Move (V_TEMP 0x1680) (UnOp OP_NOT (Var R_ZR)) $;
	Move (V_TEMP 0x19d80) (Var (V_TEMP 0x1680)) $;
	Move (V_TEMP 0x19e00) (Word 0x4 8) $;
	Move (V_TEMP 0xe380) (BinOp OP_AND (Var (V_TEMP 0x19e00)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe380)) (Word 0x8 8))) $;
	Move (V_TEMP 0xe480) (BinOp OP_AND (Var (V_TEMP 0x19e00)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe480)) (Word 0x4 8))) $;
	Move (V_TEMP 0xe580) (BinOp OP_AND (Var (V_TEMP 0x19e00)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe580)) (Word 0x2 8))) $;
	Move (V_TEMP 0xe680) (BinOp OP_AND (Var (V_TEMP 0x19e00)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe680)) (Word 0x1 8))) $;
	Move (V_TEMP 0x19e80) (UnOp OP_NOT (Var (V_TEMP 0x19d80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x19e80))) (
		Jmp (Word 0x15ec98 64)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X0)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x19f80) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x19f80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x19f80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015ec98: b.ne 0x0015ec88 *)
(*    1436824: b.ne 0x0015ec88 *)
| 0x15ec98 => Some (4,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15ec88 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015ec9c: mov x0,x2 *)
(*    1436828: mov x0,x2 *)
| 0x15ec9c => Some (4,
	Move R_X0 (Var R_X2)
)

(* 0x0015eca0: ret *)
(*    1436832: ret *)
| 0x15eca0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strchrnul_armv8.
Proof. Picinae_typecheck. Qed.

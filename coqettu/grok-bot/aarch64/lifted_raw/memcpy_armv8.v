(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: memcpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition memcpy_armv8 : program := fun _ a => match a with

(* 0x00118270: add x4,x1,x2 *)
(*    1147504: add x4,x1,x2 *)
| 0x118270 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 0x12080))
)

(* 0x00118274: add x5,x0,x2 *)
(*    1147508: add x5,x0,x2 *)
| 0x118274 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X5 (Var (V_TEMP 0x12080))
)

(* 0x00118278: cmp x2,#0x80 *)
(*    1147512: cmp x2,#0x80 *)
| 0x118278 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x80 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011827c: b.hi 0x00118370 *)
(*    1147516: b.hi 0x00118370 *)
| 0x11827c => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x118370 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118280: cmp x2,#0x20 *)
(*    1147520: cmp x2,#0x20 *)
| 0x118280 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x20 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00118284: b.hi 0x00118300 *)
(*    1147524: b.hi 0x00118300 *)
| 0x118284 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x118300 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118288: cmp x2,#0x10 *)
(*    1147528: cmp x2,#0x10 *)
| 0x118288 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x10 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011828c: b.cc 0x001182a4 *)
(*    1147532: b.cc 0x001182a4 *)
| 0x11828c => Some (4,
	Move (V_TEMP 0xb00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xb00))) (
		Jmp (Word 0x1182a4 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118290: ldp x6,x7,[x1] *)
(*    1147536: ldp x6,x7,[x1] *)
| 0x118290 => Some (4,
	Move (V_TEMP 0x7800) (Var R_X1) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7800)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 0x24180)) $;
	Move R_X7 (Var (V_TEMP 0x24300))
)

(* 0x00118294: ldp x12,x13,[x4, #-0x10] *)
(*    1147540: ldp x12,x13,[x4, #-0x10] *)
| 0x118294 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0x24180)) $;
	Move R_X13 (Var (V_TEMP 0x24300))
)

(* 0x00118298: stp x6,x7,[x0] *)
(*    1147544: stp x6,x7,[x0] *)
| 0x118298 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X6) $;
	Move (V_TEMP 0x39f80) (Var R_X7) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011829c: stp x12,x13,[x5, #-0x10] *)
(*    1147548: stp x12,x13,[x5, #-0x10] *)
| 0x11829c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X12) $;
	Move (V_TEMP 0x39f80) (Var R_X13) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001182a0: ret *)
(*    1147552: ret *)
| 0x1182a0 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001182a4: tbz w2,#0x3,0x001182c0 *)
(*    1147556: tbz w2,#0x3,0x001182c0 *)
| 0x1182a4 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x3 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x1182c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001182a8: ldr x6,[x1] *)
(*    1147560: ldr x6,[x1] *)
| 0x1182a8 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X1) $;
	Move R_X6 (Load (Var V_MEM64) (Var (V_TEMP 0x6400)) LittleE 8)
)

(* 0x001182ac: ldur x7,[x4, #-0x8] *)
(*    1147564: ldur x7,[x4, #-0x8] *)
| 0x1182ac => Some (4,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff8 64)) $;
	Move R_X7 (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 8)
)

(* 0x001182b0: str x6,[x0] *)
(*    1147568: str x6,[x0] *)
| 0x1182b0 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X6)) LittleE 8)
)

(* 0x001182b4: stur x7,[x5, #-0x8] *)
(*    1147572: stur x7,[x5, #-0x8] *)
| 0x1182b4 => Some (4,
	Move (V_TEMP 0x3a780) (Var R_X7) $;
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3a780))) LittleE 8)
)

(* 0x001182b8: ret *)
(*    1147576: ret *)
| 0x1182b8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001182c0: tbz w2,#0x2,0x001182d8 *)
(*    1147584: tbz w2,#0x2,0x001182d8 *)
| 0x1182c0 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x2 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x1182d8 64)
	) (* else *) (
		Nop
	)
)

(* 0x001182c4: ldr w6,[x1] *)
(*    1147588: ldr w6,[x1] *)
| 0x1182c4 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x001182c8: ldur w8,[x4, #-0x4] *)
(*    1147592: ldur w8,[x4, #-0x4] *)
| 0x1182c8 => Some (4,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffffc 64)) $;
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_X8 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24800)))
)

(* 0x001182cc: str w6,[x0] *)
(*    1147596: str w6,[x0] *)
| 0x1182cc => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X6))) LittleE 4)
)

(* 0x001182d0: stur w8,[x5, #-0x4] *)
(*    1147600: stur w8,[x5, #-0x4] *)
| 0x1182d0 => Some (4,
	Move (V_TEMP 0x3a080) (Extract 31 0 (Var R_X8)) $;
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffffc 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x3a080))) LittleE 4)
)

(* 0x001182d4: ret *)
(*    1147604: ret *)
| 0x1182d4 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001182d8: cbz x2,0x001182f8 *)
(*    1147608: cbz x2,0x001182f8 *)
| 0x1182d8 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x1182f8 64)
	) (* else *) (
		Nop
	)
)

(* 0x001182dc: lsr x14,x2,#0x1 *)
(*    1147612: lsr x14,x2,#0x1 *)
| 0x1182dc => Some (4,
	Move R_X14 (BinOp OP_RSHIFT (Var R_X2) (Word 0x1 64))
)

(* 0x001182e0: ldrb w6,[x1] *)
(*    1147616: ldrb w6,[x1] *)
| 0x1182e0 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x001182e4: ldurb w10,[x4, #-0x1] *)
(*    1147620: ldurb w10,[x4, #-0x1] *)
| 0x1182e4 => Some (4,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffff 64)) $;
	Move (V_TEMP 0x26980) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 1) $;
	Move R_X10 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x26980)))
)

(* 0x001182e8: ldrb w8,[x1, x14, LSL ] *)
(*    1147624: ldrb w8,[x1, x14, LSL ] *)
| 0x1182e8 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X14) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X8 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x001182ec: strb w6,[x0] *)
(*    1147628: strb w6,[x0] *)
| 0x1182ec => Some (4,
	Move (V_TEMP 0x3a300) (Extract 31 0 (Var R_X6)) $;
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6280)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a300)))) LittleE 1)
)

(* 0x001182f0: strb w8,[x0, x14, LSL ] *)
(*    1147632: strb w8,[x0, x14, LSL ] *)
| 0x1182f0 => Some (4,
	Move (V_TEMP 0x3a400) (Extract 31 0 (Var R_X8)) $;
	Move (V_TEMP 0x5700) (Var R_X14) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a400)))) LittleE 1)
)

(* 0x001182f4: sturb w10,[x5, #-0x1] *)
(*    1147636: sturb w10,[x5, #-0x1] *)
| 0x1182f4 => Some (4,
	Move (V_TEMP 0x3a680) (Extract 31 0 (Var R_X10)) $;
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffff 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 8 (Extract 7 0 (Var (V_TEMP 0x3a680)))) LittleE 1)
)

(* 0x001182f8: ret *)
(*    1147640: ret *)
| 0x1182f8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00118300: ldp x6,x7,[x1] *)
(*    1147648: ldp x6,x7,[x1] *)
| 0x118300 => Some (4,
	Move (V_TEMP 0x7800) (Var R_X1) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7800)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 0x24180)) $;
	Move R_X7 (Var (V_TEMP 0x24300))
)

(* 0x00118304: ldp x8,x9,[x1, #0x10] *)
(*    1147652: ldp x8,x9,[x1, #0x10] *)
| 0x118304 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 0x24180)) $;
	Move R_X9 (Var (V_TEMP 0x24300))
)

(* 0x00118308: ldp x10,x11,[x4, #-0x20] *)
(*    1147656: ldp x10,x11,[x4, #-0x20] *)
| 0x118308 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 0x24180)) $;
	Move R_X11 (Var (V_TEMP 0x24300))
)

(* 0x0011830c: ldp x12,x13,[x4, #-0x10] *)
(*    1147660: ldp x12,x13,[x4, #-0x10] *)
| 0x11830c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0x24180)) $;
	Move R_X13 (Var (V_TEMP 0x24300))
)

(* 0x00118310: cmp x2,#0x40 *)
(*    1147664: cmp x2,#0x40 *)
| 0x118310 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x40 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x00118314: b.hi 0x00118330 *)
(*    1147668: b.hi 0x00118330 *)
| 0x118314 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x118330 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118318: stp x6,x7,[x0] *)
(*    1147672: stp x6,x7,[x0] *)
| 0x118318 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X6) $;
	Move (V_TEMP 0x39f80) (Var R_X7) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011831c: stp x8,x9,[x0, #0x10] *)
(*    1147676: stp x8,x9,[x0, #0x10] *)
| 0x11831c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X8) $;
	Move (V_TEMP 0x39f80) (Var R_X9) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118320: stp x10,x11,[x5, #-0x20] *)
(*    1147680: stp x10,x11,[x5, #-0x20] *)
| 0x118320 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X10) $;
	Move (V_TEMP 0x39f80) (Var R_X11) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118324: stp x12,x13,[x5, #-0x10] *)
(*    1147684: stp x12,x13,[x5, #-0x10] *)
| 0x118324 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X12) $;
	Move (V_TEMP 0x39f80) (Var R_X13) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118328: ret *)
(*    1147688: ret *)
| 0x118328 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00118330: ldp x14,x15,[x1, #0x20] *)
(*    1147696: ldp x14,x15,[x1, #0x20] *)
| 0x118330 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X14 (Var (V_TEMP 0x24180)) $;
	Move R_X15 (Var (V_TEMP 0x24300))
)

(* 0x00118334: ldp x16,x17,[x1, #0x30] *)
(*    1147700: ldp x16,x17,[x1, #0x30] *)
| 0x118334 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X16 (Var (V_TEMP 0x24180)) $;
	Move R_X17 (Var (V_TEMP 0x24300))
)

(* 0x00118338: cmp x2,#0x60 *)
(*    1147704: cmp x2,#0x60 *)
| 0x118338 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x60 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011833c: b.ls 0x00118350 *)
(*    1147708: b.ls 0x00118350 *)
| 0x11833c => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x118350 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118340: ldp x2,x3,[x4, #-0x40] *)
(*    1147712: ldp x2,x3,[x4, #-0x40] *)
| 0x118340 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X2 (Var (V_TEMP 0x24180)) $;
	Move R_X3 (Var (V_TEMP 0x24300))
)

(* 0x00118344: ldp x1,x4,[x4, #-0x30] *)
(*    1147716: ldp x1,x4,[x4, #-0x30] *)
| 0x118344 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffd0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X1 (Var (V_TEMP 0x24180)) $;
	Move R_X4 (Var (V_TEMP 0x24300))
)

(* 0x00118348: stp x2,x3,[x5, #-0x40] *)
(*    1147720: stp x2,x3,[x5, #-0x40] *)
| 0x118348 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X2) $;
	Move (V_TEMP 0x39f80) (Var R_X3) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011834c: stp x1,x4,[x5, #-0x30] *)
(*    1147724: stp x1,x4,[x5, #-0x30] *)
| 0x11834c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X1) $;
	Move (V_TEMP 0x39f80) (Var R_X4) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118350: stp x6,x7,[x0] *)
(*    1147728: stp x6,x7,[x0] *)
| 0x118350 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X6) $;
	Move (V_TEMP 0x39f80) (Var R_X7) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118354: stp x8,x9,[x0, #0x10] *)
(*    1147732: stp x8,x9,[x0, #0x10] *)
| 0x118354 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X8) $;
	Move (V_TEMP 0x39f80) (Var R_X9) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118358: stp x14,x15,[x0, #0x20] *)
(*    1147736: stp x14,x15,[x0, #0x20] *)
| 0x118358 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X14) $;
	Move (V_TEMP 0x39f80) (Var R_X15) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011835c: stp x16,x17,[x0, #0x30] *)
(*    1147740: stp x16,x17,[x0, #0x30] *)
| 0x11835c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X16) $;
	Move (V_TEMP 0x39f80) (Var R_X17) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118360: stp x10,x11,[x5, #-0x20] *)
(*    1147744: stp x10,x11,[x5, #-0x20] *)
| 0x118360 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X10) $;
	Move (V_TEMP 0x39f80) (Var R_X11) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118364: stp x12,x13,[x5, #-0x10] *)
(*    1147748: stp x12,x13,[x5, #-0x10] *)
| 0x118364 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X12) $;
	Move (V_TEMP 0x39f80) (Var R_X13) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x00118368: ret *)
(*    1147752: ret *)
| 0x118368 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00118370: ldp x12,x13,[x1] *)
(*    1147760: ldp x12,x13,[x1] *)
| 0x118370 => Some (4,
	Move (V_TEMP 0x7800) (Var R_X1) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7800)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0x24180)) $;
	Move R_X13 (Var (V_TEMP 0x24300))
)

(* 0x00118374: and x14,x0,#0xf *)
(*    1147764: and x14,x0,#0xf *)
| 0x118374 => Some (4,
	Move R_X14 (BinOp OP_AND (Var R_X0) (Word 0xf 64))
)

(* 0x00118378: and x3,x0,#-0x10 *)
(*    1147768: and x3,x0,#-0x10 *)
| 0x118378 => Some (4,
	Move R_X3 (BinOp OP_AND (Var R_X0) (Word 0xfffffffffffffff0 64))
)

(* 0x0011837c: sub x1,x1,x14 *)
(*    1147772: sub x1,x1,x14 *)
| 0x11837c => Some (4,
	Move R_X1 (BinOp OP_MINUS (Var R_X1) (Var R_X14))
)

(* 0x00118380: add x2,x2,x14 *)
(*    1147776: add x2,x2,x14 *)
| 0x118380 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X14) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x12080))
)

(* 0x00118384: ldp x6,x7,[x1, #0x10] *)
(*    1147780: ldp x6,x7,[x1, #0x10] *)
| 0x118384 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 0x24180)) $;
	Move R_X7 (Var (V_TEMP 0x24300))
)

(* 0x00118388: stp x12,x13,[x0] *)
(*    1147784: stp x12,x13,[x0] *)
| 0x118388 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X12) $;
	Move (V_TEMP 0x39f80) (Var R_X13) $;
	Move (V_TEMP 0x7800) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0011838c: ldp x8,x9,[x1, #0x20] *)
(*    1147788: ldp x8,x9,[x1, #0x20] *)
| 0x11838c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 0x24180)) $;
	Move R_X9 (Var (V_TEMP 0x24300))
)

(* 0x00118390: ldp x10,x11,[x1, #0x30] *)
(*    1147792: ldp x10,x11,[x1, #0x30] *)
| 0x118390 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 0x24180)) $;
	Move R_X11 (Var (V_TEMP 0x24300))
)

(* 0x00118394: ldp x12,x13,[x1, #0x40]! *)
(*    1147796: ldp x12,x13,[x1, #0x40]! *)
| 0x118394 => Some (4,
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var R_X1) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0x24180)) $;
	Move R_X13 (Var (V_TEMP 0x24300))
)

(* 0x00118398: subs x2,x2,#0x90 *)
(*    1147800: subs x2,x2,#0x90 *)
| 0x118398 => Some (4,
	Move (V_TEMP 0x3d680) (Word 0x90 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x3d680)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3d680))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3d680))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3d680)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x3d780) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3d680))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3d780)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3d780)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x3d780)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0011839c: b.ls 0x001183c8 *)
(*    1147804: b.ls 0x001183c8 *)
| 0x11839c => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x1183c8 64)
	) (* else *) (
		Nop
	)
)

(* 0x001183a0: stp x6,x7,[x3, #0x10] *)
(*    1147808: stp x6,x7,[x3, #0x10] *)
| 0x1183a0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X6) $;
	Move (V_TEMP 0x39f80) (Var R_X7) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183a4: ldp x6,x7,[x1, #0x10] *)
(*    1147812: ldp x6,x7,[x1, #0x10] *)
| 0x1183a4 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 0x24180)) $;
	Move R_X7 (Var (V_TEMP 0x24300))
)

(* 0x001183a8: stp x8,x9,[x3, #0x20] *)
(*    1147816: stp x8,x9,[x3, #0x20] *)
| 0x1183a8 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X8) $;
	Move (V_TEMP 0x39f80) (Var R_X9) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183ac: ldp x8,x9,[x1, #0x20] *)
(*    1147820: ldp x8,x9,[x1, #0x20] *)
| 0x1183ac => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 0x24180)) $;
	Move R_X9 (Var (V_TEMP 0x24300))
)

(* 0x001183b0: stp x10,x11,[x3, #0x30] *)
(*    1147824: stp x10,x11,[x3, #0x30] *)
| 0x1183b0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X10) $;
	Move (V_TEMP 0x39f80) (Var R_X11) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183b4: ldp x10,x11,[x1, #0x30] *)
(*    1147828: ldp x10,x11,[x1, #0x30] *)
| 0x1183b4 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 0x24180)) $;
	Move R_X11 (Var (V_TEMP 0x24300))
)

(* 0x001183b8: stp x12,x13,[x3, #0x40]! *)
(*    1147832: stp x12,x13,[x3, #0x40]! *)
| 0x1183b8 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X12) $;
	Move (V_TEMP 0x39f80) (Var R_X13) $;
	Move R_X3 (BinOp OP_PLUS (Var R_X3) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_X3) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_X3) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183bc: ldp x12,x13,[x1, #0x40]! *)
(*    1147836: ldp x12,x13,[x1, #0x40]! *)
| 0x1183bc => Some (4,
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var R_X1) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X12 (Var (V_TEMP 0x24180)) $;
	Move R_X13 (Var (V_TEMP 0x24300))
)

(* 0x001183c0: subs x2,x2,#0x40 *)
(*    1147840: subs x2,x2,#0x40 *)
| 0x1183c0 => Some (4,
	Move (V_TEMP 0x3d680) (Word 0x40 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x3d680)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3d680))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3d680))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3d680)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x3d780) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3d680))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3d780)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3d780)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x3d780)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001183c4: b.hi 0x001183a0 *)
(*    1147844: b.hi 0x001183a0 *)
| 0x1183c4 => Some (4,
	Move (V_TEMP 0xd80) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x1183a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001183c8: ldp x14,x15,[x4, #-0x40] *)
(*    1147848: ldp x14,x15,[x4, #-0x40] *)
| 0x1183c8 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X14 (Var (V_TEMP 0x24180)) $;
	Move R_X15 (Var (V_TEMP 0x24300))
)

(* 0x001183cc: stp x6,x7,[x3, #0x10] *)
(*    1147852: stp x6,x7,[x3, #0x10] *)
| 0x1183cc => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X6) $;
	Move (V_TEMP 0x39f80) (Var R_X7) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183d0: ldp x6,x7,[x4, #-0x30] *)
(*    1147856: ldp x6,x7,[x4, #-0x30] *)
| 0x1183d0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffd0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X6 (Var (V_TEMP 0x24180)) $;
	Move R_X7 (Var (V_TEMP 0x24300))
)

(* 0x001183d4: stp x8,x9,[x3, #0x20] *)
(*    1147860: stp x8,x9,[x3, #0x20] *)
| 0x1183d4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X8) $;
	Move (V_TEMP 0x39f80) (Var R_X9) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183d8: ldp x8,x9,[x4, #-0x20] *)
(*    1147864: ldp x8,x9,[x4, #-0x20] *)
| 0x1183d8 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X8 (Var (V_TEMP 0x24180)) $;
	Move R_X9 (Var (V_TEMP 0x24300))
)

(* 0x001183dc: stp x10,x11,[x3, #0x30] *)
(*    1147868: stp x10,x11,[x3, #0x30] *)
| 0x1183dc => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X10) $;
	Move (V_TEMP 0x39f80) (Var R_X11) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183e0: ldp x10,x11,[x4, #-0x10] *)
(*    1147872: ldp x10,x11,[x4, #-0x10] *)
| 0x1183e0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X10 (Var (V_TEMP 0x24180)) $;
	Move R_X11 (Var (V_TEMP 0x24300))
)

(* 0x001183e4: stp x12,x13,[x3, #0x40] *)
(*    1147876: stp x12,x13,[x3, #0x40] *)
| 0x1183e4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X12) $;
	Move (V_TEMP 0x39f80) (Var R_X13) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183e8: stp x14,x15,[x5, #-0x40] *)
(*    1147880: stp x14,x15,[x5, #-0x40] *)
| 0x1183e8 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X14) $;
	Move (V_TEMP 0x39f80) (Var R_X15) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183ec: stp x6,x7,[x5, #-0x30] *)
(*    1147884: stp x6,x7,[x5, #-0x30] *)
| 0x1183ec => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X6) $;
	Move (V_TEMP 0x39f80) (Var R_X7) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffd0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183f0: stp x8,x9,[x5, #-0x20] *)
(*    1147888: stp x8,x9,[x5, #-0x20] *)
| 0x1183f0 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X8) $;
	Move (V_TEMP 0x39f80) (Var R_X9) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183f4: stp x10,x11,[x5, #-0x10] *)
(*    1147892: stp x10,x11,[x5, #-0x10] *)
| 0x1183f4 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X10) $;
	Move (V_TEMP 0x39f80) (Var R_X11) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x001183f8: ret *)
(*    1147896: ret *)
| 0x1183f8 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx memcpy_armv8.
Proof. Picinae_typecheck. Qed.

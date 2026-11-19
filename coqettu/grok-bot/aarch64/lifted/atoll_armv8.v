(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: atoll (lifted as Ghidra function FUN_0015d088, which also contains atoll's first two instructions; the symbol atoll alone lifts truncated)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition atoll_armv8 : program := fun _ a => match a with

(* 0x0015d088: ldrb w1,[x0] *)
(*    1429640: ldrb w1,[x0] *)
| 0x15d088 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015d08c: sub w2,w1,#0x9 *)
(*    1429644: sub w2,w1,#0x9 *)
| 0x15d08c => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x9 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x0015d090: cmp w1,#0x20 *)
(*    1429648: cmp w1,#0x20 *)
| 0x15d090 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x20 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x20 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x20 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015d094: ccmp w2,#0x4,#0x0,ne *)
(*    1429652: ccmp w2,#0x4,#0x0,ne *)
| 0x15d094 => Some (4,
	Move (V_TEMP 0x1680) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x19800) (Var (V_TEMP 0x1680)) $;
	Move (V_TEMP 0x19880) (Word 0x0 8) $;
	Move (V_TEMP 0xe380) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe380)) (Word 0x8 8))) $;
	Move (V_TEMP 0xe480) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe480)) (Word 0x4 8))) $;
	Move (V_TEMP 0xe580) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe580)) (Word 0x2 8))) $;
	Move (V_TEMP 0xe680) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe680)) (Word 0x1 8))) $;
	Move (V_TEMP 0x19900) (BinOp OP_XOR (Var (V_TEMP 0x19800)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x19900))) (
		Jmp (Word 0x15d098 64)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x4 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x4 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x19a00) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x4 32)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x19a00)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x19a00)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015d098: b.ls 0x0015d084 *)
(*    1429656: b.ls 0x0015d084 *)
| 0x15d098 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x15d084 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015d09c: mov w3,#0x0 *)
(*    1429660: mov w3,#0x0 *)
| 0x15d09c => Some (4,
	Move R_X3 (Word 0x0 64)
)

(* 0x0015d0a0: cmp w1,#0x2b *)
(*    1429664: cmp w1,#0x2b *)
| 0x15d0a0 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x2b 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x2b 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x2b 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x2b 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2b 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015d0a4: b.eq 0x0015d0b4 *)
(*    1429668: b.eq 0x0015d0b4 *)
| 0x15d0a4 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15d0b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015d0a8: cmp w1,#0x2d *)
(*    1429672: cmp w1,#0x2d *)
| 0x15d0a8 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x2d 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x2d 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x2d 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x2d 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2d 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015d0ac: b.ne 0x0015d0b8 *)
(*    1429676: b.ne 0x0015d0b8 *)
| 0x15d0ac => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15d0b8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015d0b0: mov w3,#0x1 *)
(*    1429680: mov w3,#0x1 *)
| 0x15d0b0 => Some (4,
	Move R_X3 (Word 0x1 64)
)

(* 0x0015d0b4: add x0,x0,#0x1 *)
(*    1429684: add x0,x0,#0x1 *)
| 0x15d0b4 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015d0b8: mov x1,#0x0 *)
(*    1429688: mov x1,#0x0 *)
| 0x15d0b8 => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015d0bc: b 0x0015d0d0 *)
(*    1429692: b 0x0015d0d0 *)
| 0x15d0bc => Some (4,
	Jmp (Word 0x15d0d0 64)
)

(* 0x0015d0c0: add x1,x1,x1, LSL #0x2 *)
(*    1429696: add x1,x1,x1, LSL #0x2 *)
| 0x15d0c0 => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X1) (Word 0x2 64)) $;
	Move (V_TEMP 0x11f80) (Var (V_TEMP 0x4400)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x12080))
)

(* 0x0015d0c4: add x0,x0,#0x1 *)
(*    1429700: add x0,x0,#0x1 *)
| 0x15d0c4 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015d0c8: lsl x1,x1,#0x1 *)
(*    1429704: lsl x1,x1,#0x1 *)
| 0x15d0c8 => Some (4,
	Move R_X1 (BinOp OP_LSHIFT (Var R_X1) (Word 0x1 64))
)

(* 0x0015d0cc: sub x1,x1,w2, SXTW  *)
(*    1429708: sub x1,x1,w2, SXTW  *)
| 0x15d0cc => Some (4,
	Move (V_TEMP 0x5b80) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_X2))) $;
	Move (V_TEMP 0x5c80) (Var (V_TEMP 0x5b80)) $;
	Move (V_TEMP 0x5c80) (BinOp OP_LSHIFT (Var (V_TEMP 0x5c80)) (Word 0x0 64)) $;
	Move R_X1 (BinOp OP_MINUS (Var R_X1) (Var (V_TEMP 0x5c80)))
)

(* 0x0015d0d0: ldrb w2,[x0] *)
(*    1429712: ldrb w2,[x0] *)
| 0x15d0d0 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015d0d4: sub w2,w2,#0x30 *)
(*    1429716: sub w2,w2,#0x30 *)
| 0x15d0d4 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x30 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x0015d0d8: cmp w2,#0x9 *)
(*    1429720: cmp w2,#0x9 *)
| 0x15d0d8 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x9 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x9 32) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x9 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x9 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x9 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015d0dc: b.ls 0x0015d0c0 *)
(*    1429724: b.ls 0x0015d0c0 *)
| 0x15d0dc => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x15d0c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015d0e0: cmp w3,#0x0 *)
(*    1429728: cmp w3,#0x0 *)
| 0x15d0e0 => Some (4,
	Move (V_TEMP 0x1c500) (Word 0x0 32) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X3)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1c600) (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Var (V_TEMP 0x1c500))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c600)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015d0e4: cneg x0,x1,eq *)
(*    1429732: cneg x0,x1,eq *)
| 0x15d0e4 => Some (4,
	Move (V_TEMP 0x1d000) (UnOp OP_NEG (Var R_X1)) $;
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1d000) (Var R_X1)
	) $;
	Move R_X0 (Var (V_TEMP 0x1d000))
)

(* 0x0015d0e8: ret *)
(*    1429736: ret *)
| 0x15d0e8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015d080: b 0x0015d088 *)
(*    1429632: b 0x0015d088 *)
| 0x15d080 => Some (4,
	Jmp (Word 0x15d088 64)
)

(* 0x0015d084: add x0,x0,#0x1 *)
(*    1429636: add x0,x0,#0x1 *)
| 0x15d084 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx atoll_armv8.
Proof. Picinae_typecheck. Qed.

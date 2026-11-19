(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: atoi (lifted as Ghidra function FUN_0015cfb0, which also contains atoi's first two instructions; the symbol atoi alone lifts truncated)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition atoi_armv8 : program := fun _ a => match a with

(* 0x0015cfb0: ldrb w1,[x0] *)
(*    1429424: ldrb w1,[x0] *)
| 0x15cfb0 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015cfb4: sub w2,w1,#0x9 *)
(*    1429428: sub w2,w1,#0x9 *)
| 0x15cfb4 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x9 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x0015cfb8: cmp w1,#0x20 *)
(*    1429432: cmp w1,#0x20 *)
| 0x15cfb8 => Some (4,
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

(* 0x0015cfbc: ccmp w2,#0x4,#0x0,ne *)
(*    1429436: ccmp w2,#0x4,#0x0,ne *)
| 0x15cfbc => Some (4,
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
		Jmp (Word 0x15cfc0 64)
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

(* 0x0015cfc0: b.ls 0x0015cfac *)
(*    1429440: b.ls 0x0015cfac *)
| 0x15cfc0 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x15cfac 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015cfc4: mov w3,#0x0 *)
(*    1429444: mov w3,#0x0 *)
| 0x15cfc4 => Some (4,
	Move R_X3 (Word 0x0 64)
)

(* 0x0015cfc8: cmp w1,#0x2b *)
(*    1429448: cmp w1,#0x2b *)
| 0x15cfc8 => Some (4,
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

(* 0x0015cfcc: b.eq 0x0015cfdc *)
(*    1429452: b.eq 0x0015cfdc *)
| 0x15cfcc => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15cfdc 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015cfd0: cmp w1,#0x2d *)
(*    1429456: cmp w1,#0x2d *)
| 0x15cfd0 => Some (4,
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

(* 0x0015cfd4: b.ne 0x0015cfe0 *)
(*    1429460: b.ne 0x0015cfe0 *)
| 0x15cfd4 => Some (4,
	Move (V_TEMP 0xa00) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15cfe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015cfd8: mov w3,#0x1 *)
(*    1429464: mov w3,#0x1 *)
| 0x15cfd8 => Some (4,
	Move R_X3 (Word 0x1 64)
)

(* 0x0015cfdc: add x0,x0,#0x1 *)
(*    1429468: add x0,x0,#0x1 *)
| 0x15cfdc => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015cfe0: mov w1,#0x0 *)
(*    1429472: mov w1,#0x0 *)
| 0x15cfe0 => Some (4,
	Move R_X1 (Word 0x0 64)
)

(* 0x0015cfe4: b 0x0015cff8 *)
(*    1429476: b 0x0015cff8 *)
| 0x15cfe4 => Some (4,
	Jmp (Word 0x15cff8 64)
)

(* 0x0015cfe8: add w1,w1,w1, LSL #0x2 *)
(*    1429480: add w1,w1,w1, LSL #0x2 *)
| 0x15cfe8 => Some (4,
	Move (V_TEMP 0x3e80) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X1)) (Word 0x2 32)) $;
	Move (V_TEMP 0x11d80) (Var (V_TEMP 0x3e80)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x11d80))) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x11d80))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11d80)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x11e80) (BinOp OP_PLUS (Extract 31 0 (Var R_X1)) (Var (V_TEMP 0x11d80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11e80)) (Word 0x0 32))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11e80)))
)

(* 0x0015cfec: add x0,x0,#0x1 *)
(*    1429484: add x0,x0,#0x1 *)
| 0x15cfec => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015cff0: lsl w1,w1,#0x1 *)
(*    1429488: lsl w1,w1,#0x1 *)
| 0x15cff0 => Some (4,
	Move (V_TEMP 0x27e00) (BinOp OP_LSHIFT (Extract 31 0 (Var R_X1)) (Word 0x1 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27e00)))
)

(* 0x0015cff4: sub w1,w1,w2 *)
(*    1429492: sub w1,w1,w2 *)
| 0x15cff4 => Some (4,
	Move (V_TEMP 0x3cc80) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2))) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3cc80)))
)

(* 0x0015cff8: ldrb w2,[x0] *)
(*    1429496: ldrb w2,[x0] *)
| 0x15cff8 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015cffc: sub w2,w2,#0x30 *)
(*    1429500: sub w2,w2,#0x30 *)
| 0x15cffc => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Word 0x30 32)) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x0015d000: cmp w2,#0x9 *)
(*    1429504: cmp w2,#0x9 *)
| 0x15d000 => Some (4,
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

(* 0x0015d004: b.ls 0x0015cfe8 *)
(*    1429508: b.ls 0x0015cfe8 *)
| 0x15d004 => Some (4,
	Move (V_TEMP 0xf00) (BinOp OP_XOR (Var R_CY) (Word 1 8)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x15cfe8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015d008: cmp w3,#0x0 *)
(*    1429512: cmp w3,#0x0 *)
| 0x15d008 => Some (4,
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

(* 0x0015d00c: cneg w0,w1,eq *)
(*    1429516: cneg w0,w1,eq *)
| 0x15d00c => Some (4,
	Move (V_TEMP 0x1ce00) (UnOp OP_NEG (Extract 31 0 (Var R_X1))) $;
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Nop
	) (* else *) (
	Move (V_TEMP 0x1ce00) (Extract 31 0 (Var R_X1))
	) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x1ce00)))
)

(* 0x0015d010: ret *)
(*    1429520: ret *)
| 0x15d010 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015cfa8: b 0x0015cfb0 *)
(*    1429416: b 0x0015cfb0 *)
| 0x15cfa8 => Some (4,
	Jmp (Word 0x15cfb0 64)
)

(* 0x0015cfac: add x0,x0,#0x1 *)
(*    1429420: add x0,x0,#0x1 *)
| 0x15cfac => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx atoi_armv8.
Proof. Picinae_typecheck. Qed.

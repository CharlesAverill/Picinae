(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: memmove
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition memmove_armv8 : program := fun _ a => match a with

(* 0x0015e708: mov x5,x0 *)
(*    1435400: mov x5,x0 *)
| 0x15e708 => Some (4,
	Move R_X5 (Var R_X0)
)

(* 0x0015e70c: mov x4,x1 *)
(*    1435404: mov x4,x1 *)
| 0x15e70c => Some (4,
	Move R_X4 (Var R_X1)
)

(* 0x0015e710: mov x3,x2 *)
(*    1435408: mov x3,x2 *)
| 0x15e710 => Some (4,
	Move R_X3 (Var R_X2)
)

(* 0x0015e714: cmp x0,x1 *)
(*    1435412: cmp x0,x1 *)
| 0x15e714 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X1) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X1)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X1)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X0) (Var R_X1)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e718: b.eq 0x0015e7b4 *)
(*    1435416: b.eq 0x0015e7b4 *)
| 0x15e718 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e71c: sub x6,x1,x2 *)
(*    1435420: sub x6,x1,x2 *)
| 0x15e71c => Some (4,
	Move R_X6 (BinOp OP_MINUS (Var R_X1) (Var R_X2))
)

(* 0x0015e720: neg x7,x2, LSL #0x1 *)
(*    1435424: neg x7,x2, LSL #0x1 *)
| 0x15e720 => Some (4,
	Move (V_TEMP 0x4400) (BinOp OP_LSHIFT (Var R_X2) (Word 0x1 64)) $;
	Move R_X7 (UnOp OP_NEG (Var (V_TEMP 0x4400)))
)

(* 0x0015e724: sub x6,x6,x0 *)
(*    1435428: sub x6,x6,x0 *)
| 0x15e724 => Some (4,
	Move R_X6 (BinOp OP_MINUS (Var R_X6) (Var R_X0))
)

(* 0x0015e728: cmp x6,x7 *)
(*    1435432: cmp x6,x7 *)
| 0x15e728 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X7) (Var R_X6))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X6) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X6) (Var R_X7)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X6) (Var R_X7)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X7) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X6) (Var R_X7)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e72c: b.ls 0x0015e750 *)
(*    1435436: b.ls 0x0015e750 *)
| 0x15e72c => Some (4,
	Move (V_TEMP 0xf00) (UnOp OP_NOT (Var R_CY)) $;
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x15e750 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e730: eor x0,x1,x0 *)
(*    1435440: eor x0,x1,x0 *)
| 0x15e730 => Some (4,
	Move R_X0 (BinOp OP_XOR (Var R_X1) (Var R_X0))
)

(* 0x0015e734: and x0,x0,#0x7 *)
(*    1435444: and x0,x0,#0x7 *)
| 0x15e734 => Some (4,
	Move R_X0 (BinOp OP_AND (Var R_X0) (Word 0x7 64))
)

(* 0x0015e738: cmp x5,x1 *)
(*    1435448: cmp x5,x1 *)
| 0x15e738 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X1) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X5) (Var R_X1)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X5) (Var R_X1)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X5) (Var R_X1)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e73c: b.cs 0x0015e7bc *)
(*    1435452: b.cs 0x0015e7bc *)
| 0x15e73c => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Jmp (Word 0x15e7bc 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e740: cbz x0,0x0015e754 *)
(*    1435456: cbz x0,0x0015e754 *)
| 0x15e740 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15e754 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e744: mov x1,x5 *)
(*    1435460: mov x1,x5 *)
| 0x15e744 => Some (4,
	Move R_X1 (Var R_X5)
)

(* 0x0015e748: mov x0,#0x0 *)
(*    1435464: mov x0,#0x0 *)
| 0x15e748 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0015e74c: b 0x0015e7ac *)
(*    1435468: b 0x0015e7ac *)
| 0x15e74c => Some (4,
	Jmp (Word 0x15e7ac 64)
)

(* 0x0015e750: b 0x00118270 *)
(*    1435472: b 0x00118270 *)
| 0x15e750 => Some (4,
	Jmp (Word 0x118270 64)
)

(* 0x0015e754: mov x0,x5 *)
(*    1435476: mov x0,x5 *)
| 0x15e754 => Some (4,
	Move R_X0 (Var R_X5)
)

(* 0x0015e758: ands x2,x0,#0x7 *)
(*    1435480: ands x2,x0,#0x7 *)
| 0x15e758 => Some (4,
	Move (V_TEMP 0x12900) (BinOp OP_AND (Var R_X0) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12900)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x12900)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e75c: b.eq 0x0015e774 *)
(*    1435484: b.eq 0x0015e774 *)
| 0x15e75c => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e774 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e760: cbz x3,0x0015e7b4 *)
(*    1435488: cbz x3,0x0015e7b4 *)
| 0x15e760 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X3) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15e7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e764: ldrb w1,[x4], #0x1 *)
(*    1435492: ldrb w1,[x4], #0x1 *)
| 0x15e764 => Some (4,
	Move (V_TEMP 0x7000) (Var R_X4) $;
	Move R_X4 (BinOp OP_PLUS (Var R_X4) (Word 0x1 64)) $;
	Move (V_TEMP 0x24f00) (Load (Var V_MEM64) (Var (V_TEMP 0x7000)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24f00)))
)

(* 0x0015e768: sub x3,x3,#0x1 *)
(*    1435496: sub x3,x3,#0x1 *)
| 0x15e768 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X3) (Word 0x1 64))
)

(* 0x0015e76c: strb w1,[x0], #0x1 *)
(*    1435500: strb w1,[x0], #0x1 *)
| 0x15e76c => Some (4,
	Move (V_TEMP 0x3a380) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 0x7000) (Var R_X0) $;
	Move R_X0 (BinOp OP_PLUS (Var R_X0) (Word 0x1 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7000)) (Cast CAST_LOW 8 (Var (V_TEMP 0x3a380))) LittleE 1)
)

(* 0x0015e770: b 0x0015e758 *)
(*    1435504: b 0x0015e758 *)
| 0x15e770 => Some (4,
	Jmp (Word 0x15e758 64)
)

(* 0x0015e774: and x6,x3,#-0x8 *)
(*    1435508: and x6,x3,#-0x8 *)
| 0x15e774 => Some (4,
	Move R_X6 (BinOp OP_AND (Var R_X3) (Word 0xfffffffffffffff8 64))
)

(* 0x0015e778: b 0x0015e788 *)
(*    1435512: b 0x0015e788 *)
| 0x15e778 => Some (4,
	Jmp (Word 0x15e788 64)
)

(* 0x0015e77c: ldr x1,[x4, x2, LSL #0x0] *)
(*    1435516: ldr x1,[x4, x2, LSL #0x0] *)
| 0x15e77c => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x6d00))) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 8)
)

(* 0x0015e780: str x1,[x0, x2, LSL #0x0] *)
(*    1435520: str x1,[x0, x2, LSL #0x0] *)
| 0x15e780 => Some (4,
	Move (V_TEMP 0x3a280) (Var R_X1) $;
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3a280))) LittleE 8)
)

(* 0x0015e784: add x2,x2,#0x8 *)
(*    1435524: add x2,x2,#0x8 *)
| 0x15e784 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x8 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015e788: cmp x2,x6 *)
(*    1435528: cmp x2,x6 *)
| 0x15e788 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X6) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var R_X6)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var R_X6)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X6) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X2) (Var R_X6)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e78c: b.ne 0x0015e77c *)
(*    1435532: b.ne 0x0015e77c *)
| 0x15e78c => Some (4,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15e77c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e790: add x4,x4,x2 *)
(*    1435536: add x4,x4,x2 *)
| 0x15e790 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) (Var R_X4))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X4) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 0x12080))
)

(* 0x0015e794: add x1,x0,x2 *)
(*    1435540: add x1,x0,x2 *)
| 0x15e794 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x12080))
)

(* 0x0015e798: sub x3,x3,x2 *)
(*    1435544: sub x3,x3,x2 *)
| 0x15e798 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X3) (Var R_X2))
)

(* 0x0015e79c: b 0x0015e748 *)
(*    1435548: b 0x0015e748 *)
| 0x15e79c => Some (4,
	Jmp (Word 0x15e748 64)
)

(* 0x0015e7a0: ldrb w2,[x4, x0, LSL ] *)
(*    1435552: ldrb w2,[x4, x0, LSL ] *)
| 0x15e7a0 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015e7a4: strb w2,[x1, x0, LSL ] *)
(*    1435556: strb w2,[x1, x0, LSL ] *)
| 0x15e7a4 => Some (4,
	Move (V_TEMP 0x3a400) (Extract 31 0 (Var R_X2)) $;
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_LOW 8 (Var (V_TEMP 0x3a400))) LittleE 1)
)

(* 0x0015e7a8: add x0,x0,#0x1 *)
(*    1435560: add x0,x0,#0x1 *)
| 0x15e7a8 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x11b80))
)

(* 0x0015e7ac: cmp x3,x0 *)
(*    1435564: cmp x3,x0 *)
| 0x15e7ac => Some (4,
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

(* 0x0015e7b0: b.ne 0x0015e7a0 *)
(*    1435568: b.ne 0x0015e7a0 *)
| 0x15e7b0 => Some (4,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15e7a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e7b4: mov x0,x5 *)
(*    1435572: mov x0,x5 *)
| 0x15e7b4 => Some (4,
	Move R_X0 (Var R_X5)
)

(* 0x0015e7b8: ret *)
(*    1435576: ret *)
| 0x15e7b8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015e7bc: cbnz x0,0x0015e814 *)
(*    1435580: cbnz x0,0x0015e814 *)
| 0x15e7bc => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X0) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x15e814 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e7c0: add x0,x5,x3 *)
(*    1435584: add x0,x5,x3 *)
| 0x15e7c0 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X3) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 0x12080))
)

(* 0x0015e7c4: tst x0,#0x7 *)
(*    1435588: tst x0,#0x7 *)
| 0x15e7c4 => Some (4,
	Move (V_TEMP 0x3f200) (BinOp OP_AND (Var R_X0) (Word 0x7 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)

(* 0x0015e7c8: b.eq 0x0015e7e0 *)
(*    1435592: b.eq 0x0015e7e0 *)
| 0x15e7c8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15e7e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e7cc: cbz x3,0x0015e7b4 *)
(*    1435596: cbz x3,0x0015e7b4 *)
| 0x15e7cc => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X3) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15e7b4 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e7d0: sub x3,x3,#0x1 *)
(*    1435600: sub x3,x3,#0x1 *)
| 0x15e7d0 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X3) (Word 0x1 64))
)

(* 0x0015e7d4: ldrb w0,[x4, x3, LSL ] *)
(*    1435604: ldrb w0,[x4, x3, LSL ] *)
| 0x15e7d4 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015e7d8: strb w0,[x5, x3, LSL ] *)
(*    1435608: strb w0,[x5, x3, LSL ] *)
| 0x15e7d8 => Some (4,
	Move (V_TEMP 0x3a400) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_LOW 8 (Var (V_TEMP 0x3a400))) LittleE 1)
)

(* 0x0015e7dc: b 0x0015e7c0 *)
(*    1435612: b 0x0015e7c0 *)
| 0x15e7dc => Some (4,
	Jmp (Word 0x15e7c0 64)
)

(* 0x0015e7e0: and x2,x3,#0x7 *)
(*    1435616: and x2,x3,#0x7 *)
| 0x15e7e0 => Some (4,
	Move R_X2 (BinOp OP_AND (Var R_X3) (Word 0x7 64))
)

(* 0x0015e7e4: mov x0,x3 *)
(*    1435620: mov x0,x3 *)
| 0x15e7e4 => Some (4,
	Move R_X0 (Var R_X3)
)

(* 0x0015e7e8: b 0x0015e7f8 *)
(*    1435624: b 0x0015e7f8 *)
| 0x15e7e8 => Some (4,
	Jmp (Word 0x15e7f8 64)
)

(* 0x0015e7ec: sub x0,x0,#0x8 *)
(*    1435628: sub x0,x0,#0x8 *)
| 0x15e7ec => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X0) (Word 0x8 64))
)

(* 0x0015e7f0: ldr x1,[x4, x0, LSL #0x0] *)
(*    1435632: ldr x1,[x4, x0, LSL #0x0] *)
| 0x15e7f0 => Some (4,
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x6d00))) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 8)
)

(* 0x0015e7f4: str x1,[x5, x0, LSL #0x0] *)
(*    1435636: str x1,[x5, x0, LSL #0x0] *)
| 0x15e7f4 => Some (4,
	Move (V_TEMP 0x3a280) (Var R_X1) $;
	Move (V_TEMP 0x5700) (Var R_X0) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3a280))) LittleE 8)
)

(* 0x0015e7f8: cmp x0,x2 *)
(*    1435640: cmp x0,x2 *)
| 0x15e7f8 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X2) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X2)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X0) (Var R_X2)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1cc80) (BinOp OP_MINUS (Var R_X0) (Var R_X2)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cc80)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015e7fc: b.ne 0x0015e7ec *)
(*    1435644: b.ne 0x0015e7ec *)
| 0x15e7fc => Some (4,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x15e7ec 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e800: and x3,x3,#0x7 *)
(*    1435648: and x3,x3,#0x7 *)
| 0x15e800 => Some (4,
	Move R_X3 (BinOp OP_AND (Var R_X3) (Word 0x7 64))
)

(* 0x0015e804: b 0x0015e814 *)
(*    1435652: b 0x0015e814 *)
| 0x15e804 => Some (4,
	Jmp (Word 0x15e814 64)
)

(* 0x0015e808: sub x3,x3,#0x1 *)
(*    1435656: sub x3,x3,#0x1 *)
| 0x15e808 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X3) (Word 0x1 64))
)

(* 0x0015e80c: ldrb w0,[x4, x3, LSL ] *)
(*    1435660: ldrb w0,[x4, x3, LSL ] *)
| 0x15e80c => Some (4,
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X4) (Var (V_TEMP 0x6d00))) $;
	Move (V_TEMP 0x25100) (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25100)))
)

(* 0x0015e810: strb w0,[x5, x3, LSL ] *)
(*    1435664: strb w0,[x5, x3, LSL ] *)
| 0x15e810 => Some (4,
	Move (V_TEMP 0x3a400) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x5700) (Var R_X3) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_LOW 8 (Var (V_TEMP 0x3a400))) LittleE 1)
)

(* 0x0015e814: cbnz x3,0x0015e808 *)
(*    1435668: cbnz x3,0x0015e808 *)
| 0x15e814 => Some (4,
	Move (V_TEMP 0x18a00) (BinOp OP_NEQ (Var R_X3) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a00))) (
		Jmp (Word 0x15e808 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015e818: b 0x0015e7b4 *)
(*    1435672: b 0x0015e7b4 *)
| 0x15e818 => Some (4,
	Jmp (Word 0x15e7b4 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx memmove_armv8.
Proof. Picinae_typecheck. Qed.

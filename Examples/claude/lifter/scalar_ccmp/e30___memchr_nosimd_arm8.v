(* Explicit scalar replacement, Ghidra 11.4.2 raw SLEIGH pcode.
libc SHA256: 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06
function: __memchr_nosimd; entry: 0x19c7c0; addressing: global
Instruction-local canonical temps; strict failure; staticMemory=False.
No functional correctness or lifter soundness claim. *)
Require Import Picinae_armv8 NArith.
Open Scope N.
Definition e30___memchr_nosimd_arm8 : program := fun _ a => match a with
(* 0x19c7c0: nop *)
| 0x19c7c0 => Some (4,
	Nop
)
(* 0x19c7c4: cbz x2,0x0019c898 *)
| 0x19c7c4 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X2) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19c898 64)) (Nop)
)
(* 0x19c7c8: tst x0,#0xf *)
| 0x19c7c8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X0) (Word 0xf 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)
(* 0x19c7cc: and x6,x0,#-0x10 *)
| 0x19c7cc => Some (4,
	Move R_X6 (BinOp OP_AND (Var R_X0) (Word 0xfffffffffffffff0 64))
)
(* 0x19c7d0: orr x10,xzr,#0x101010101010101 *)
| 0x19c7d0 => Some (4,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move R_X10 (BinOp OP_OR (Var (V_TEMP 0)) (Word 0x101010101010101 64))
)
(* 0x19c7d4: and x1,x1,#0xff *)
| 0x19c7d4 => Some (4,
	Move R_X1 (BinOp OP_AND (Var R_X1) (Word 0xff 64))
)
(* 0x19c7d8: mul x1,x1,x10 *)
| 0x19c7d8 => Some (4,
	Move R_X1 (BinOp OP_TIMES (Var R_X1) (Var R_X10))
)
(* 0x19c7dc: add x7,x0,x2 *)
| 0x19c7dc => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X7 (Var (V_TEMP 1))
)
(* 0x19c7e0: add x8,x7,#0xf *)
| 0x19c7e0 => Some (4,
	Move (V_TEMP 0) (Word 0xf 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X7) (Var (V_TEMP 0))) (Var R_X7))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X7)) (Extract 63 63 (Var (V_TEMP 0)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X7)) (Extract 63 63 (BinOp OP_PLUS (Var R_X7) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_X7) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X8 (Var (V_TEMP 1))
)
(* 0x19c7e4: and x8,x8,#-0x10 *)
| 0x19c7e4 => Some (4,
	Move R_X8 (BinOp OP_AND (Var R_X8) (Word 0xfffffffffffffff0 64))
)
(* 0x19c7e8: b.eq 0x0019c830 *)
| 0x19c7e8 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (Jmp (Word 0x19c830 64)) (Nop)
)
(* 0x19c7ec: ldp x11,x12,[x6], #0x10 *)
| 0x19c7ec => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move R_X6 (BinOp OP_PLUS (Var R_X6) (Word 0x10 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X11 (Var (V_TEMP 1)) $;
	Move R_X12 (Var (V_TEMP 3))
)
(* 0x19c7f0: lsl x2,x0,#0x3 *)
| 0x19c7f0 => Some (4,
	Move R_X2 (BinOp OP_LSHIFT (Var R_X0) (Word 0x3 64))
)
(* 0x19c7f4: mov x3,#-0x1 *)
| 0x19c7f4 => Some (4,
	Move R_X3 (Word 0xffffffffffffffff 64)
)
(* 0x19c7f8: lsl x4,x3,x2 *)
| 0x19c7f8 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X2) (Word 0x3f 64)) $;
	Move R_X4 (BinOp OP_LSHIFT (Var R_X3) (Var (V_TEMP 0)))
)
(* 0x19c7fc: tst x0,#0x8 *)
| 0x19c7fc => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Var R_X0) (Word 0x8 64)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Word 0x0 8) $;
	Move R_OV (Word 0x0 8)
)
(* 0x19c800: eor x11,x11,x1 *)
| 0x19c800 => Some (4,
	Move R_X11 (BinOp OP_XOR (Var R_X11) (Var R_X1))
)
(* 0x19c804: eor x12,x12,x1 *)
| 0x19c804 => Some (4,
	Move R_X12 (BinOp OP_XOR (Var R_X12) (Var R_X1))
)
(* 0x19c808: orn x2,x11,x4 *)
| 0x19c808 => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var R_X4) (Var (V_TEMP 0))) $;
	Move R_X2 (BinOp OP_OR (Var R_X11) (Var (V_TEMP 1)))
)
(* 0x19c80c: orn x3,x12,x4 *)
| 0x19c80c => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var R_X4) (Var (V_TEMP 0))) $;
	Move R_X3 (BinOp OP_OR (Var R_X12) (Var (V_TEMP 1)))
)
(* 0x19c810: csinv x11,x2,xzr,eq *)
| 0x19c810 => Some (4,
	Move (V_TEMP 0) (Var R_X2) $;
	If (Cast CAST_LOW 1 (Var R_ZR)) (Nop) (Move (V_TEMP 0) (UnOp OP_NOT (Word 0x0 64))) $;
	Move R_X11 (Var (V_TEMP 0))
)
(* 0x19c814: csel x12,x12,x3,eq *)
| 0x19c814 => Some (4,
	Move (V_TEMP 0) (Var R_X12) $;
	If (Cast CAST_LOW 1 (Var R_ZR)) (Nop) (Move (V_TEMP 0) (Var R_X3)) $;
	Move R_X12 (Var (V_TEMP 0))
)
(* 0x19c818: cmp x0,x7 *)
| 0x19c818 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X7) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (Var R_X7))) (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (BinOp OP_MINUS (Var R_X0) (Var R_X7)))))) $;
	Move (V_TEMP 0) (BinOp OP_MINUS (Var R_X0) (Var R_X7)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19c81c: ccmp x6,x8,#0x0,mi *)
| 0x19c81c => Some (4,
	Move (V_TEMP 0) (Var R_NG) $;
	Move (V_TEMP 1) (Word 0x0 8) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x8 8))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x4 8))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x2 8))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 5)) (Word 0x1 8))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 6))) (Nop) (Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X8) (Var R_X6))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X6)) (Extract 63 63 (Var R_X8))) (BinOp OP_XOR (Extract 63 63 (Var R_X6)) (Extract 63 63 (BinOp OP_MINUS (Var R_X6) (Var R_X8)))))) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Var R_X6) (Var R_X8)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 7)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV))
)
(* 0x19c820: csetm x9,ne *)
| 0x19c820 => Some (4,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (UnOp OP_NEG (Word 0x1 64)) $;
	Move R_X9 (BinOp OP_TIMES (Var (V_TEMP 2)) (Var (V_TEMP 3)))
)
(* 0x19c824: b 0x0019c840 *)
| 0x19c824 => Some (4,
	Jmp (Word 0x19c840 64)
)
(* 0x19c828: nop *)
| 0x19c828 => Some (4,
	Nop
)
(* 0x19c82c: nop *)
| 0x19c82c => Some (4,
	Nop
)
(* 0x19c830: ldp x11,x12,[x6], #0x10 *)
| 0x19c830 => Some (4,
	Move (V_TEMP 0) (Var R_X6) $;
	Move R_X6 (BinOp OP_PLUS (Var R_X6) (Word 0x10 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 8) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Word 0x8 64)) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_X11 (Var (V_TEMP 1)) $;
	Move R_X12 (Var (V_TEMP 3))
)
(* 0x19c834: subs x9,x6,x8 *)
| 0x19c834 => Some (4,
	Move (V_TEMP 0) (Var R_X8) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X6))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X6)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X6)) (Extract 63 63 (BinOp OP_MINUS (Var R_X6) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X6) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_X9 (Var (V_TEMP 1)) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19c838: eor x11,x11,x1 *)
| 0x19c838 => Some (4,
	Move R_X11 (BinOp OP_XOR (Var R_X11) (Var R_X1))
)
(* 0x19c83c: eor x12,x12,x1 *)
| 0x19c83c => Some (4,
	Move R_X12 (BinOp OP_XOR (Var R_X12) (Var R_X1))
)
(* 0x19c840: sub x2,x11,x10 *)
| 0x19c840 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X11) (Var R_X10))
)
(* 0x19c844: sub x3,x12,x10 *)
| 0x19c844 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X12) (Var R_X10))
)
(* 0x19c848: orr x4,x11,#0x7f7f7f7f7f7f7f7f *)
| 0x19c848 => Some (4,
	Move R_X4 (BinOp OP_OR (Var R_X11) (Word 0x7f7f7f7f7f7f7f7f 64))
)
(* 0x19c84c: orr x5,x12,#0x7f7f7f7f7f7f7f7f *)
| 0x19c84c => Some (4,
	Move R_X5 (BinOp OP_OR (Var R_X12) (Word 0x7f7f7f7f7f7f7f7f 64))
)
(* 0x19c850: bic x13,x2,x4 *)
| 0x19c850 => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var R_X4) (Var (V_TEMP 0))) $;
	Move R_X13 (BinOp OP_AND (Var R_X2) (Var (V_TEMP 1)))
)
(* 0x19c854: bic x14,x3,x5 *)
| 0x19c854 => Some (4,
	Move (V_TEMP 0) (UnOp OP_NEG (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var R_X5) (Var (V_TEMP 0))) $;
	Move R_X14 (BinOp OP_AND (Var R_X3) (Var (V_TEMP 1)))
)
(* 0x19c858: orr x2,x13,x14 *)
| 0x19c858 => Some (4,
	Move R_X2 (BinOp OP_OR (Var R_X13) (Var R_X14))
)
(* 0x19c85c: ccmp x2,#0x0,#0x0,ne *)
| 0x19c85c => Some (4,
	Move (V_TEMP 0) (BinOp OP_XOR (Var R_ZR) (Word 0x1 8)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 8) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x8 8))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x4 8))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 5)) (Word 0x2 8))) $;
	Move (V_TEMP 6) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 6)) (Word 0x1 8))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 1)) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 7))) (Nop) (Move (V_TEMP 8) (Cast CAST_UNSIGNED 64 (Word 0x0 32)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 8)) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (Var (V_TEMP 8)))) (BinOp OP_XOR (Extract 63 63 (Var R_X2)) (Extract 63 63 (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 8))))))) $;
	Move (V_TEMP 8) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 8))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 8)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 8)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV))
)
(* 0x19c860: b.eq 0x0019c830 *)
| 0x19c860 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (Jmp (Word 0x19c830 64)) (Nop)
)
(* 0x19c864: cbz x13,0x0019c874 *)
| 0x19c864 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X13) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19c874 64)) (Nop)
)
(* 0x19c868: sub x0,x6,#0x10 *)
| 0x19c868 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X6) (Word 0x10 64))
)
(* 0x19c86c: rev x13,x13 *)
| 0x19c86c => Some (4,
	Move (V_TEMP 0) (Var R_X13) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff00 64)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff 64)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff0000 64)) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 5)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff 64)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move (V_TEMP 10) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move R_X13 (BinOp OP_OR (Var (V_TEMP 9)) (Var (V_TEMP 10)))
)
(* 0x19c870: b 0x0019c880 *)
| 0x19c870 => Some (4,
	Jmp (Word 0x19c880 64)
)
(* 0x19c874: cbz x14,0x0019c898 *)
| 0x19c874 => Some (4,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X14) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (Jmp (Word 0x19c898 64)) (Nop)
)
(* 0x19c878: sub x0,x6,#0x8 *)
| 0x19c878 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X6) (Word 0x8 64))
)
(* 0x19c87c: rev x13,x14 *)
| 0x19c87c => Some (4,
	Move (V_TEMP 0) (Var R_X14) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff00 64)) $;
	Move (V_TEMP 2) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff00ff00ff00ff 64)) $;
	Move (V_TEMP 4) (BinOp OP_LSHIFT (Var (V_TEMP 3)) (Cast CAST_UNSIGNED 64 (Word 0x8 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff0000 64)) $;
	Move (V_TEMP 6) (BinOp OP_RSHIFT (Var (V_TEMP 5)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 7) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xffff0000ffff 64)) $;
	Move (V_TEMP 8) (BinOp OP_LSHIFT (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 64 (Word 0x10 32))) $;
	Move (V_TEMP 0) (BinOp OP_OR (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move (V_TEMP 10) (BinOp OP_LSHIFT (Var (V_TEMP 0)) (Cast CAST_UNSIGNED 64 (Word 0x20 32))) $;
	Move R_X13 (BinOp OP_OR (Var (V_TEMP 9)) (Var (V_TEMP 10)))
)
(* 0x19c880: cmp x9,#0x0 *)
| 0x19c880 => Some (4,
	Move (V_TEMP 0) (Word 0x0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0)) (Var R_X9))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X9)) (Extract 63 63 (Var (V_TEMP 0)))) (BinOp OP_XOR (Extract 63 63 (Var R_X9)) (Extract 63 63 (BinOp OP_MINUS (Var R_X9) (Var (V_TEMP 0))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_X9) (Var (V_TEMP 0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)
(* 0x19c884: clz x2,x13 *)
| 0x19c884 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Word 0x40 64) (UnOp OP_BITWIDTH (Var R_X13)))
)
(* 0x19c888: add x0,x0,x2, LSR #0x3 *)
| 0x19c888 => Some (4,
	Move (V_TEMP 0) (BinOp OP_RSHIFT (Var R_X2) (Cast CAST_UNSIGNED 64 (Word 0x3 32))) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 1))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (Var (V_TEMP 1)))) (Word 0x1 1)) (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 1))))))) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 2)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 64))) $;
	Move R_X0 (Var (V_TEMP 2))
)
(* 0x19c88c: ccmp x0,x7,#0x8,eq *)
| 0x19c88c => Some (4,
	Move (V_TEMP 0) (Var R_ZR) $;
	Move (V_TEMP 1) (Word 0x8 8) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x8 8))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x4 8))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x2 8))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 5)) (Word 0x1 8))) $;
	Move (V_TEMP 6) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 0x1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 6))) (Nop) (Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var R_X7) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (Var R_X7))) (BinOp OP_XOR (Extract 63 63 (Var R_X0)) (Extract 63 63 (BinOp OP_MINUS (Var R_X0) (Var R_X7)))))) $;
	Move (V_TEMP 7) (BinOp OP_MINUS (Var R_X0) (Var R_X7)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 7)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 7)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV))
)
(* 0x19c890: csel x0,x0,xzr,mi *)
| 0x19c890 => Some (4,
	Move (V_TEMP 0) (Var R_X0) $;
	If (Cast CAST_LOW 1 (Var R_NG)) (Nop) (Move (V_TEMP 0) (Word 0x0 64)) $;
	Move R_X0 (Var (V_TEMP 0))
)
(* 0x19c894: ret *)
| 0x19c894 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
(* 0x19c898: mov x0,#0x0 *)
| 0x19c898 => Some (4,
	Move R_X0 (Word 0x0 64)
)
(* 0x19c89c: ret *)
| 0x19c89c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)
| _ => None
end.
Theorem welltyped : welltyped_prog arm8typctx e30___memchr_nosimd_arm8.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

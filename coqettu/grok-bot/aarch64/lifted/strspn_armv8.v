(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strspn
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strspn_armv8 : program := fun _ a => match a with

(* 0x0015f2e8: adrp x2,0x19e000 *)
(*    1438440: adrp x2,0x19e000 *)
| 0x15f2e8 => Some (4,
	Move R_X2 (Word 0x19e000 64)
)

(* 0x0015f2ec: add x2,x2,#0x6b0 *)
(*    1438444: add x2,x2,#0x6b0 *)
| 0x15f2ec => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x6b0 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X2 (Var (V_TEMP 0x11b80))
)

(* 0x0015f2f0: sub sp,sp,#0x20 *)
(*    1438448: sub sp,sp,#0x20 *)
| 0x15f2f0 => Some (4,
	Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 0x20 64))
)

(* 0x0015f2f4: ldrb w3,[x1] *)
(*    1438452: ldrb w3,[x1] *)
| 0x15f2f4 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f2f8: ldp q30,q31,[x2] *)
(*    1438456: ldp q30,q31,[x2] *)
| 0x15f2f8 => Some (4,
	Move (V_TEMP 0x7800) (Var R_X2) $;
	Move R_Z30 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (Var (V_TEMP 0x7800)) LittleE 16)) (Word 0 256)) (BinOp OP_AND (Var R_Z30) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000 256))) $;
	Move R_Z30 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 128 256)) (BinOp OP_AND (Var R_Z30) (Word 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z30 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 192 256)) (BinOp OP_AND (Var R_Z30) (Word 0x0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move (V_TEMP 0xc9580) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x10 64)) $;
	Move R_Z31 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Load (Var V_MEM64) (Var (V_TEMP 0xc9580)) LittleE 16)) (Word 0 256)) (BinOp OP_AND (Var R_Z31) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000 256))) $;
	Move R_Z31 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 128 256)) (BinOp OP_AND (Var R_Z31) (Word 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z31 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 192 256)) (BinOp OP_AND (Var R_Z31) (Word 0x0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256)))
)

(* 0x0015f2fc: stp q30,q31,[sp] *)
(*    1438460: stp q30,q31,[sp] *)
| 0x15f2fc => Some (4,
	Move (V_TEMP 0x7800) (Var R_SP) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7800)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z30))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7800)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z31))) LittleE 16)
)

(* 0x0015f300: cbz w3,0x0015f38c *)
(*    1438464: cbz w3,0x0015f38c *)
| 0x15f300 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f38c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f304: ldrb w2,[x1, #0x1] *)
(*    1438468: ldrb w2,[x1, #0x1] *)
| 0x15f304 => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X1) (Word 0x1 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f308: cbz w2,0x0015f354 *)
(*    1438472: cbz w2,0x0015f354 *)
| 0x15f308 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f354 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f30c: mov x5,sp *)
(*    1438476: mov x5,sp *)
| 0x15f30c => Some (4,
	Move R_X5 (Var R_SP)
)

(* 0x0015f310: mov x6,#0x1 *)
(*    1438480: mov x6,#0x1 *)
| 0x15f310 => Some (4,
	Move R_X6 (Word 0x1 64)
)

(* 0x0015f314: ldrb w3,[x1] *)
(*    1438484: ldrb w3,[x1] *)
| 0x15f314 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f318: add x1,x1,#0x1 *)
(*    1438488: add x1,x1,#0x1 *)
| 0x15f318 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015f31c: ubfx x2,x3,#0x6,#0x2 *)
(*    1438492: ubfx x2,x3,#0x6,#0x2 *)
| 0x15f31c => Some (4,
	Move (V_TEMP 0x41100) (Var R_X3) $;
	Move (V_TEMP 0x41180) (BinOp OP_RSHIFT (Var (V_TEMP 0x41100)) (Word 0x6 64)) $;
	Move (V_TEMP 0x41200) (BinOp OP_MINUS (Word 0x40 64) (Word 0x6 64)) $;
	Move (V_TEMP 0x41280) (BinOp OP_LSHIFT (Var (V_TEMP 0x41100)) (Var (V_TEMP 0x41200))) $;
	Move (V_TEMP 0x41300) (BinOp OP_OR (Var (V_TEMP 0x41180)) (Var (V_TEMP 0x41280))) $;
	Move (V_TEMP 0x41400) (BinOp OP_AND (Var (V_TEMP 0x41300)) (Word 0xfc00000000000003 64)) $;
	Move R_X2 (BinOp OP_AND (Var (V_TEMP 0x41400)) (Word 0x3 64))
)

(* 0x0015f320: lsl x4,x6,x3 *)
(*    1438496: lsl x4,x6,x3 *)
| 0x15f320 => Some (4,
	Move (V_TEMP 0x27a00) (BinOp OP_AND (Var R_X3) (Word 0x3f 64)) $;
	Move R_X4 (BinOp OP_LSHIFT (Var R_X6) (Var (V_TEMP 0x27a00)))
)

(* 0x0015f324: cbz w3,0x0015f384 *)
(*    1438500: cbz w3,0x0015f384 *)
| 0x15f324 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X3)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f384 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f328: lsl x2,x2,#0x3 *)
(*    1438504: lsl x2,x2,#0x3 *)
| 0x15f328 => Some (4,
	Move R_X2 (BinOp OP_LSHIFT (Var R_X2) (Word 0x3 64))
)

(* 0x0015f32c: ldr x3,[x5, x2, LSL #0x0] *)
(*    1438508: ldr x3,[x5, x2, LSL #0x0] *)
| 0x15f32c => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x6d00))) $;
	Move R_X3 (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 8)
)

(* 0x0015f330: orr x4,x4,x3 *)
(*    1438512: orr x4,x4,x3 *)
| 0x15f330 => Some (4,
	Move R_X4 (BinOp OP_OR (Var R_X4) (Var R_X3))
)

(* 0x0015f334: str x4,[x5, x2, LSL #0x0] *)
(*    1438516: str x4,[x5, x2, LSL #0x0] *)
| 0x15f334 => Some (4,
	Move (V_TEMP 0x3a280) (Var R_X4) $;
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x0 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_X5) (Var (V_TEMP 0x6d00))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7180)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3a280))) LittleE 8)
)

(* 0x0015f338: b 0x0015f314 *)
(*    1438520: b 0x0015f314 *)
| 0x15f338 => Some (4,
	Jmp (Word 0x15f314 64)
)

(* 0x0015f33c: add x1,x1,#0x1 *)
(*    1438524: add x1,x1,#0x1 *)
| 0x15f33c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X1 (Var (V_TEMP 0x11b80))
)

(* 0x0015f340: ldrb w2,[x1] *)
(*    1438528: ldrb w2,[x1] *)
| 0x15f340 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X1) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f344: cmp w2,w3 *)
(*    1438532: cmp w2,w3 *)
| 0x15f344 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f348: b.eq 0x0015f33c *)
(*    1438536: b.eq 0x0015f33c *)
| 0x15f348 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15f33c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f34c: sub x0,x1,x0 *)
(*    1438540: sub x0,x1,x0 *)
| 0x15f34c => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X1) (Var R_X0))
)

(* 0x0015f350: b 0x0015f37c *)
(*    1438544: b 0x0015f37c *)
| 0x15f350 => Some (4,
	Jmp (Word 0x15f37c 64)
)

(* 0x0015f354: mov x1,x0 *)
(*    1438548: mov x1,x0 *)
| 0x15f354 => Some (4,
	Move R_X1 (Var R_X0)
)

(* 0x0015f358: b 0x0015f340 *)
(*    1438552: b 0x0015f340 *)
| 0x15f358 => Some (4,
	Jmp (Word 0x15f340 64)
)

(* 0x0015f35c: add x3,x3,#0x1 *)
(*    1438556: add x3,x3,#0x1 *)
| 0x15f35c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x0015f360: ldrb w1,[x3] *)
(*    1438560: ldrb w1,[x3] *)
| 0x15f360 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X3) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f364: ubfx x2,x1,#0x6,#0x2 *)
(*    1438564: ubfx x2,x1,#0x6,#0x2 *)
| 0x15f364 => Some (4,
	Move (V_TEMP 0x41100) (Var R_X1) $;
	Move (V_TEMP 0x41180) (BinOp OP_RSHIFT (Var (V_TEMP 0x41100)) (Word 0x6 64)) $;
	Move (V_TEMP 0x41200) (BinOp OP_MINUS (Word 0x40 64) (Word 0x6 64)) $;
	Move (V_TEMP 0x41280) (BinOp OP_LSHIFT (Var (V_TEMP 0x41100)) (Var (V_TEMP 0x41200))) $;
	Move (V_TEMP 0x41300) (BinOp OP_OR (Var (V_TEMP 0x41180)) (Var (V_TEMP 0x41280))) $;
	Move (V_TEMP 0x41400) (BinOp OP_AND (Var (V_TEMP 0x41300)) (Word 0xfc00000000000003 64)) $;
	Move R_X2 (BinOp OP_AND (Var (V_TEMP 0x41400)) (Word 0x3 64))
)

(* 0x0015f368: cbz w1,0x0015f378 *)
(*    1438568: cbz w1,0x0015f378 *)
| 0x15f368 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f378 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f36c: ldr x2,[sp, x2, LSL #0x3] *)
(*    1438572: ldr x2,[sp, x2, LSL #0x3] *)
| 0x15f36c => Some (4,
	Move (V_TEMP 0x5700) (Var R_X2) $;
	Move (V_TEMP 0x6d00) (Var (V_TEMP 0x5700)) $;
	Move (V_TEMP 0x6d00) (BinOp OP_LSHIFT (Var (V_TEMP 0x6d00)) (Word 0x3 64)) $;
	Move (V_TEMP 0x7180) (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x6d00))) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 0x7180)) LittleE 8)
)

(* 0x0015f370: lsr x1,x2,x1 *)
(*    1438576: lsr x1,x2,x1 *)
| 0x15f370 => Some (4,
	Move (V_TEMP 0x28300) (BinOp OP_AND (Var R_X1) (Word 0x3f 64)) $;
	Move R_X1 (BinOp OP_RSHIFT (Var R_X2) (Var (V_TEMP 0x28300)))
)

(* 0x0015f374: tbnz w1,#0x0,0x0015f35c *)
(*    1438580: tbnz w1,#0x0,0x0015f35c *)
| 0x15f374 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x15f35c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f378: sub x0,x3,x0 *)
(*    1438584: sub x0,x3,x0 *)
| 0x15f378 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X3) (Var R_X0))
)

(* 0x0015f37c: add sp,sp,#0x20 *)
(*    1438588: add sp,sp,#0x20 *)
| 0x15f37c => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x20 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) (Var R_SP))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_SP (Var (V_TEMP 0x11b80))
)

(* 0x0015f380: ret *)
(*    1438592: ret *)
| 0x15f380 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015f384: mov x3,x0 *)
(*    1438596: mov x3,x0 *)
| 0x15f384 => Some (4,
	Move R_X3 (Var R_X0)
)

(* 0x0015f388: b 0x0015f360 *)
(*    1438600: b 0x0015f360 *)
| 0x15f388 => Some (4,
	Jmp (Word 0x15f360 64)
)

(* 0x0015f38c: mov x0,#0x0 *)
(*    1438604: mov x0,#0x0 *)
| 0x15f38c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0015f390: b 0x0015f37c *)
(*    1438608: b 0x0015f37c *)
| 0x15f390 => Some (4,
	Jmp (Word 0x15f37c 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx strspn_armv8.
Proof. Picinae_typecheck. Qed.

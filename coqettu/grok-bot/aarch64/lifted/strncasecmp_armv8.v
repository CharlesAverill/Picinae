(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: strncasecmp
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strncasecmp_armv8 : program := fun _ a => match a with

(* 0x0015f004: cbz x2,0x0015f0a8 *)
(*    1437700: cbz x2,0x0015f0a8 *)
| 0x15f004 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15f0a8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f008: stp x29,x30,[sp, #-0x40]! *)
(*    1437704: stp x29,x30,[sp, #-0x40]! *)
| 0x15f008 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X29) $;
	Move (V_TEMP 0x39f80) (Var R_X30) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_SP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var R_SP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f00c: mov x29,sp *)
(*    1437708: mov x29,sp *)
| 0x15f00c => Some (4,
	Move R_X29 (Var R_SP)
)

(* 0x0015f010: stp x19,x20,[sp, #0x10] *)
(*    1437712: stp x19,x20,[sp, #0x10] *)
| 0x15f010 => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X19) $;
	Move (V_TEMP 0x39f80) (Var R_X20) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f014: mov x20,x1 *)
(*    1437716: mov x20,x1 *)
| 0x15f014 => Some (4,
	Move R_X20 (Var R_X1)
)

(* 0x0015f018: mov x19,x0 *)
(*    1437720: mov x19,x0 *)
| 0x15f018 => Some (4,
	Move R_X19 (Var R_X0)
)

(* 0x0015f01c: stp x21,x22,[sp, #0x20] *)
(*    1437724: stp x21,x22,[sp, #0x20] *)
| 0x15f01c => Some (4,
	Move (V_TEMP 0x39f00) (Var R_X21) $;
	Move (V_TEMP 0x39f80) (Var R_X22) $;
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f00))) LittleE 8) $;
	Move (V_TEMP 0x3a000) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a000)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x39f80))) LittleE 8)
)

(* 0x0015f020: mov x22,x0 *)
(*    1437728: mov x22,x0 *)
| 0x15f020 => Some (4,
	Move R_X22 (Var R_X0)
)

(* 0x0015f024: sub x21,x2,#0x1 *)
(*    1437732: sub x21,x2,#0x1 *)
| 0x15f024 => Some (4,
	Move R_X21 (BinOp OP_MINUS (Var R_X2) (Word 0x1 64))
)

(* 0x0015f028: str x23,[sp, #0x30] *)
(*    1437736: str x23,[sp, #0x30] *)
| 0x15f028 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X23)) LittleE 8)
)

(* 0x0015f02c: b 0x0015f038 *)
(*    1437740: b 0x0015f038 *)
| 0x15f02c => Some (4,
	Jmp (Word 0x15f038 64)
)

(* 0x0015f030: add x19,x19,#0x1 *)
(*    1437744: add x19,x19,#0x1 *)
| 0x15f030 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Var R_X19))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X19) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X19) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X19 (Var (V_TEMP 0x11b80))
)

(* 0x0015f034: add x20,x20,#0x1 *)
(*    1437748: add x20,x20,#0x1 *)
| 0x15f034 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Var R_X20))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X20) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X20) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X20 (Var (V_TEMP 0x11b80))
)

(* 0x0015f038: ldrb w2,[x19] *)
(*    1437752: ldrb w2,[x19] *)
| 0x15f038 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X19) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f03c: sub x1,x22,x19 *)
(*    1437756: sub x1,x22,x19 *)
| 0x15f03c => Some (4,
	Move R_X1 (BinOp OP_MINUS (Var R_X22) (Var R_X19))
)

(* 0x0015f040: cmn x1,x21 *)
(*    1437760: cmn x1,x21 *)
| 0x15f040 => Some (4,
	Move (V_TEMP 0x1bf80) (Var R_X21) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x1bf80))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x1bf80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1bf80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c080) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x1bf80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c080)) (Word 0x0 64))) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f044: mov w0,w2 *)
(*    1437764: mov w0,w2 *)
| 0x15f044 => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2)))
)

(* 0x0015f048: cbz w2,0x0015f07c *)
(*    1437768: cbz w2,0x0015f07c *)
| 0x15f048 => Some (4,
	Move (V_TEMP 0x18a80) (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18a80))) (
		Jmp (Word 0x15f07c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f04c: ldrb w1,[x20] *)
(*    1437772: ldrb w1,[x20] *)
| 0x15f04c => Some (4,
	Move (V_TEMP 0x6280) (Var R_X20) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f050: ccmp w1,#0x0,#0x4,ne *)
(*    1437776: ccmp w1,#0x0,#0x4,ne *)
| 0x15f050 => Some (4,
	Move (V_TEMP 0x1680) (BinOp OP_XOR (Var R_ZR) (Word 1 8)) $;
	Move (V_TEMP 0x19800) (Var (V_TEMP 0x1680)) $;
	Move (V_TEMP 0x19880) (Word 0x4 8) $;
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
		Jmp (Word 0x15f054 64)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Word 0x0 32) (Extract 31 0 (Var R_X1)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x19a00) (BinOp OP_MINUS (Extract 31 0 (Var R_X1)) (Word 0x0 32)) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x19a00)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x19a00)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f054: b.eq 0x0015f07c *)
(*    1437780: b.eq 0x0015f07c *)
| 0x15f054 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15f07c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f058: cmp w2,w1 *)
(*    1437784: cmp w2,w1 *)
| 0x15f058 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X1)) (Extract 31 0 (Var R_X2)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X1)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X1))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f05c: b.eq 0x0015f030 *)
(*    1437788: b.eq 0x0015f030 *)
| 0x15f05c => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15f030 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f060: bl 0x0011f2d0 *)
(*    1437792: bl 0x0011f2d0 *)
| 0x15f060 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f060 64) (Word 0x4 64)) $;
	Jmp (Word 0x11f2d0 64)
)

(* 0x0015f064: mov w23,w0 *)
(*    1437796: mov w23,w0 *)
| 0x15f064 => Some (4,
	Move R_X23 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X0)))
)

(* 0x0015f068: ldrb w0,[x20] *)
(*    1437800: ldrb w0,[x20] *)
| 0x15f068 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X20) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f06c: bl 0x0011f2d0 *)
(*    1437804: bl 0x0011f2d0 *)
| 0x15f06c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f06c 64) (Word 0x4 64)) $;
	Jmp (Word 0x11f2d0 64)
)

(* 0x0015f070: cmp w23,w0 *)
(*    1437808: cmp w23,w0 *)
| 0x15f070 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X0)) (Extract 31 0 (Var R_X23)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X23)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X23)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X23)) (Extract 31 0 (Var R_X0))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x1cb80) (BinOp OP_MINUS (Extract 31 0 (Var R_X23)) (Extract 31 0 (Var R_X0))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cb80)) (Word 0x0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x0015f074: b.eq 0x0015f030 *)
(*    1437812: b.eq 0x0015f030 *)
| 0x15f074 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 0x15f030 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015f078: ldrb w2,[x19] *)
(*    1437816: ldrb w2,[x19] *)
| 0x15f078 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X19) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f07c: mov w0,w2 *)
(*    1437820: mov w0,w2 *)
| 0x15f07c => Some (4,
	Move R_X0 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X2)))
)

(* 0x0015f080: bl 0x0011f2d0 *)
(*    1437824: bl 0x0011f2d0 *)
| 0x15f080 => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f080 64) (Word 0x4 64)) $;
	Jmp (Word 0x11f2d0 64)
)

(* 0x0015f084: mov w19,w0 *)
(*    1437828: mov w19,w0 *)
| 0x15f084 => Some (4,
	Move R_X19 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_X0)))
)

(* 0x0015f088: ldrb w0,[x20] *)
(*    1437832: ldrb w0,[x20] *)
| 0x15f088 => Some (4,
	Move (V_TEMP 0x6280) (Var R_X20) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x6280)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0015f08c: bl 0x0011f2d0 *)
(*    1437836: bl 0x0011f2d0 *)
| 0x15f08c => Some (4,
	Move R_X30 (BinOp OP_PLUS (Word 0x15f08c 64) (Word 0x4 64)) $;
	Jmp (Word 0x11f2d0 64)
)

(* 0x0015f090: sub w0,w19,w0 *)
(*    1437840: sub w0,w19,w0 *)
| 0x15f090 => Some (4,
	Move (V_TEMP 0x3cc80) (BinOp OP_MINUS (Extract 31 0 (Var R_X19)) (Extract 31 0 (Var R_X0))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3cc80)))
)

(* 0x0015f094: ldr x23,[sp, #0x30] *)
(*    1437844: ldr x23,[sp, #0x30] *)
| 0x15f094 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_SP) (Word 0x30 64)) $;
	Move R_X23 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x0015f098: ldp x19,x20,[sp, #0x10] *)
(*    1437848: ldp x19,x20,[sp, #0x10] *)
| 0x15f098 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x10 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X19 (Var (V_TEMP 0x24180)) $;
	Move R_X20 (Var (V_TEMP 0x24300))
)

(* 0x0015f09c: ldp x21,x22,[sp, #0x20] *)
(*    1437852: ldp x21,x22,[sp, #0x20] *)
| 0x15f09c => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_SP) (Word 0x20 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7780)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X21 (Var (V_TEMP 0x24180)) $;
	Move R_X22 (Var (V_TEMP 0x24300))
)

(* 0x0015f0a0: ldp x29,x30,[sp], #0x40 *)
(*    1437856: ldp x29,x30,[sp], #0x40 *)
| 0x15f0a0 => Some (4,
	Move (V_TEMP 0x7880) (Var R_SP) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 0x40 64)) $;
	Move (V_TEMP 0x24180) (Load (Var V_MEM64) (Var (V_TEMP 0x7880)) LittleE 8) $;
	Move (V_TEMP 0x24200) (BinOp OP_PLUS (Var (V_TEMP 0x7880)) (Word 0x8 64)) $;
	Move (V_TEMP 0x24300) (Load (Var V_MEM64) (Var (V_TEMP 0x24200)) LittleE 8) $;
	Move R_X29 (Var (V_TEMP 0x24180)) $;
	Move R_X30 (Var (V_TEMP 0x24300))
)

(* 0x0015f0a4: ret *)
(*    1437860: ret *)
| 0x15f0a4 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015f0a8: mov w0,#0x0 *)
(*    1437864: mov w0,#0x0 *)
| 0x15f0a8 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0015f0ac: ret *)
(*    1437868: ret *)
| 0x15f0ac => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx strncasecmp_armv8.
Proof. Picinae_typecheck. Qed.

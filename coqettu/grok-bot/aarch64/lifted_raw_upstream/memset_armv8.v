(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: memset
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition memset_armv8 : program := fun _ a => match a with

(* 0x00118400: dup v0.16B,w1 *)
(*    1147904: dup v0.16B,w1 *)
| 0x118400 => Some (4,
	Move (V_TEMP 0x85c80) (Extract 7 0 (Var R_X1)) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 0 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 8 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 16 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 24 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 32 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 40 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 48 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 56 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 64 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 72 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 80 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 88 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 96 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 104 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 112 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Var (V_TEMP 0x85c80))) (Word 120 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 128 256)) (BinOp OP_AND (Var R_Z0) (Word 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256))) $;
	Move R_Z0 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 256 (Word 0x0 64)) (Word 192 256)) (BinOp OP_AND (Var R_Z0) (Word 0x0000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF 256)))
)

(* 0x00118404: add x4,x0,x2 *)
(*    1147908: add x4,x0,x2 *)
| 0x118404 => Some (4,
	Move (V_TEMP 0x11f80) (Var R_X2) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Var R_X0))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11f80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x12080) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x11f80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12080)) (Word 0x0 64))) $;
	Move R_X4 (Var (V_TEMP 0x12080))
)

(* 0x00118408: cmp x2,#0x60 *)
(*    1147912: cmp x2,#0x60 *)
| 0x118408 => Some (4,
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

(* 0x0011840c: b.hi 0x00118480 *)
(*    1147916: b.hi 0x00118480 *)
| 0x11840c => Some (4,
	Move (V_TEMP 0xd80) (UnOp OP_NOT (Var R_ZR)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x118480 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118410: cmp x2,#0x10 *)
(*    1147920: cmp x2,#0x10 *)
| 0x118410 => Some (4,
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

(* 0x00118414: b.cs 0x00118454 *)
(*    1147924: b.cs 0x00118454 *)
| 0x118414 => Some (4,
	If (Cast CAST_LOW 1 (Var R_CY)) (
		Jmp (Word 0x118454 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118418: mov x1,v0.D[0x0] *)
(*    1147928: mov x1,v0.D[0x0] *)
| 0x118418 => Some (4,
	Move R_X1 (Extract 63 0 (Var R_Z0))
)

(* 0x0011841c: tbz w2,#0x3,0x00118430 *)
(*    1147932: tbz w2,#0x3,0x00118430 *)
| 0x11841c => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x3 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x118430 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118420: str x1,[x0] *)
(*    1147936: str x1,[x0] *)
| 0x118420 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var R_X1)) LittleE 8)
)

(* 0x00118424: stur x1,[x4, #-0x8] *)
(*    1147940: stur x1,[x4, #-0x8] *)
| 0x118424 => Some (4,
	Move (V_TEMP 0x3a780) (Var R_X1) $;
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3a780))) LittleE 8)
)

(* 0x00118428: ret *)
(*    1147944: ret *)
| 0x118428 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00118430: tbz w2,#0x2,0x00118440 *)
(*    1147952: tbz w2,#0x2,0x00118440 *)
| 0x118430 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x2 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x118440 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118434: str w1,[x0] *)
(*    1147956: str w1,[x0] *)
| 0x118434 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x00118438: stur w1,[x4, #-0x4] *)
(*    1147960: stur w1,[x4, #-0x4] *)
| 0x118438 => Some (4,
	Move (V_TEMP 0x3a080) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffffc 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x3a080))) LittleE 4)
)

(* 0x0011843c: ret *)
(*    1147964: ret *)
| 0x11843c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00118440: cbz x2,0x00118450 *)
(*    1147968: cbz x2,0x00118450 *)
| 0x118440 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X2) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x118450 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118444: strb w1,[x0] *)
(*    1147972: strb w1,[x0] *)
| 0x118444 => Some (4,
	Move (V_TEMP 0x3a300) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 0x6280) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6280)) (Cast CAST_LOW 8 (Var (V_TEMP 0x3a300))) LittleE 1)
)

(* 0x00118448: tbz w2,#0x1,0x00118450 *)
(*    1147976: tbz w2,#0x1,0x00118450 *)
| 0x118448 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x118450 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011844c: sturh w1,[x4, #-0x2] *)
(*    1147980: sturh w1,[x4, #-0x2] *)
| 0x11844c => Some (4,
	Move (V_TEMP 0x3a700) (Extract 31 0 (Var R_X1)) $;
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffffe 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_LOW 16 (Var (V_TEMP 0x3a700))) LittleE 2)
)

(* 0x00118450: ret *)
(*    1147984: ret *)
| 0x118450 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00118454: str q0,[x0] *)
(*    1147988: str q0,[x0] *)
| 0x118454 => Some (4,
	Move (V_TEMP 0x6480) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6480)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x00118458: tbnz w2,#0x6,0x00118470 *)
(*    1147992: tbnz w2,#0x6,0x00118470 *)
| 0x118458 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x6 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x118470 64)
	) (* else *) (
		Nop
	)
)

(* 0x0011845c: stur q0,[x4, #-0x10] *)
(*    1147996: stur q0,[x4, #-0x10] *)
| 0x11845c => Some (4,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x00118460: tbz w2,#0x5,0x0011846c *)
(*    1148000: tbz w2,#0x5,0x0011846c *)
| 0x118460 => Some (4,
	Move (V_TEMP 0x18480) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x5 32)) $;
	Move (V_TEMP 0x18500) (BinOp OP_AND (Var (V_TEMP 0x18480)) (Word 0x1 32)) $;
	Move (V_TEMP 0x18600) (BinOp OP_EQ (Var (V_TEMP 0x18500)) (Word 0x0 32)) $;
	Move (V_TEMP 0x3ef00) (BinOp OP_EQ (Var (V_TEMP 0x18600)) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3ef00))) (
		Jmp (Word 0x11846c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118464: str q0,[x0, #0x10] *)
(*    1148004: str q0,[x0, #0x10] *)
| 0x118464 => Some (4,
	Move (V_TEMP 0x6200) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6200)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x00118468: stur q0,[x4, #-0x20] *)
(*    1148008: stur q0,[x4, #-0x20] *)
| 0x118468 => Some (4,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x0011846c: ret *)
(*    1148012: ret *)
| 0x11846c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00118470: str q0,[x0, #0x10] *)
(*    1148016: str q0,[x0, #0x10] *)
| 0x118470 => Some (4,
	Move (V_TEMP 0x6200) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6200)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x00118474: stp q0,q0,[x0, #0x20] *)
(*    1148020: stp q0,q0,[x0, #0x20] *)
| 0x118474 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x00118478: stp q0,q0,[x4, #-0x20] *)
(*    1148024: stp q0,q0,[x4, #-0x20] *)
| 0x118478 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x0011847c: ret *)
(*    1148028: ret *)
| 0x11847c => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x00118480: and w1,w1,#0xff *)
(*    1148032: and w1,w1,#0xff *)
| 0x118480 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X1)) (Word 0xff 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00118484: and x3,x0,#-0x10 *)
(*    1148036: and x3,x0,#-0x10 *)
| 0x118484 => Some (4,
	Move R_X3 (BinOp OP_AND (Var R_X0) (Word 0xfffffffffffffff0 64))
)

(* 0x00118488: str q0,[x0] *)
(*    1148040: str q0,[x0] *)
| 0x118488 => Some (4,
	Move (V_TEMP 0x6480) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6480)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x0011848c: cmp x2,#0xa0 *)
(*    1148044: cmp x2,#0xa0 *)
| 0x11848c => Some (4,
	Move (V_TEMP 0x1c800) (Word 0xa0 64) $;
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

(* 0x00118490: ccmp w1,#0x0,#0x0,cs *)
(*    1148048: ccmp w1,#0x0,#0x0,cs *)
| 0x118490 => Some (4,
	Move (V_TEMP 0x19800) (Var R_CY) $;
	Move (V_TEMP 0x19880) (Word 0x0 8) $;
	Move (V_TEMP 0xe380) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x8 8)) $;
	Move R_NG (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe380)) (Word 0x8 8))) $;
	Move (V_TEMP 0xe480) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x4 8)) $;
	Move R_ZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe480)) (Word 0x4 8))) $;
	Move (V_TEMP 0xe580) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x2 8)) $;
	Move R_CY (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe580)) (Word 0x2 8))) $;
	Move (V_TEMP 0xe680) (BinOp OP_AND (Var (V_TEMP 0x19880)) (Word 0x1 8)) $;
	Move R_OV (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0xe680)) (Word 0x1 8))) $;
	Move (V_TEMP 0x19900) (UnOp OP_NOT (Var (V_TEMP 0x19800))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x19900))) (
		Jmp (Word 0x118494 64)
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

(* 0x00118494: b.ne 0x001184dc *)
(*    1148052: b.ne 0x001184dc *)
| 0x118494 => Some (4,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x1184dc 64)
	) (* else *) (
		Nop
	)
)

(* 0x00118498: mrs x5,dczid_el0 *)
(*    1148056: mrs x5,dczid_el0 *)
| 0x118498 => Some (4,
	Nop (* Unmodeled Regs: R_DCZID_EL0 *)
)

(* 0x0011849c: and x5,x5,#0x1f *)
(*    1148060: and x5,x5,#0x1f *)
| 0x11849c => Some (4,
	Move R_X5 (BinOp OP_AND (Var R_X5) (Word 0x1f 64))
)

(* 0x001184a0: cmp x5,#0x4 *)
(*    1148064: cmp x5,#0x4 *)
| 0x1184a0 => Some (4,
	Move (V_TEMP 0x1c800) (Word 0x4 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1c800)) (Var R_X5))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X5) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X5) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X5) (Var (V_TEMP 0x1c800))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1c800)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x1c900) (BinOp OP_MINUS (Var R_X5) (Var (V_TEMP 0x1c800))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1c900)) (Word 0x0 64))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x001184a4: b.ne 0x001184dc *)
(*    1148068: b.ne 0x001184dc *)
| 0x1184a4 => Some (4,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZR)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa00))) (
		Jmp (Word 0x1184dc 64)
	) (* else *) (
		Nop
	)
)

(* 0x001184a8: str q0,[x3, #0x10] *)
(*    1148072: str q0,[x3, #0x10] *)
| 0x1184a8 => Some (4,
	Move (V_TEMP 0x6200) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6200)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x001184ac: stp q0,q0,[x3, #0x20] *)
(*    1148076: stp q0,q0,[x3, #0x20] *)
| 0x1184ac => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x001184b0: and x3,x3,#-0x40 *)
(*    1148080: and x3,x3,#-0x40 *)
| 0x1184b0 => Some (4,
	Move R_X3 (BinOp OP_AND (Var R_X3) (Word 0xffffffffffffffc0 64))
)

(* 0x001184b4: sub x2,x4,x3 *)
(*    1148084: sub x2,x4,x3 *)
| 0x1184b4 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X4) (Var R_X3))
)

(* 0x001184b8: sub x2,x2,#0x80 *)
(*    1148088: sub x2,x2,#0x80 *)
| 0x1184b8 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x80 64))
)

(* 0x001184bc: nop *)
(*    1148092: nop *)
| 0x1184bc => Some (4,
	Nop
)

(* 0x001184c0: add x3,x3,#0x40 *)
(*    1148096: add x3,x3,#0x40 *)
| 0x1184c0 => Some (4,
	Move (V_TEMP 0x11a80) (Word 0x40 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Var R_X3))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X3) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x11a80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 0x11b80) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 0x11a80))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x11b80)) (Word 0x0 64))) $;
	Move R_X3 (Var (V_TEMP 0x11b80))
)

(* 0x001184c4: dc ZVA,x3 *)
(*    1148100: dc ZVA,x3 *)
| 0x1184c4 => Some (4,
	Nop (* Unmodeled Op: CALLOTHER *)
)

(* 0x001184c8: subs x2,x2,#0x40 *)
(*    1148104: subs x2,x2,#0x40 *)
| 0x1184c8 => Some (4,
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

(* 0x001184cc: b.hi 0x001184c0 *)
(*    1148108: b.hi 0x001184c0 *)
| 0x1184cc => Some (4,
	Move (V_TEMP 0xd80) (UnOp OP_NOT (Var R_ZR)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x1184c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001184d0: stp q0,q0,[x4, #-0x40] *)
(*    1148112: stp q0,q0,[x4, #-0x40] *)
| 0x1184d0 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x001184d4: stp q0,q0,[x4, #-0x20] *)
(*    1148116: stp q0,q0,[x4, #-0x20] *)
| 0x1184d4 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x001184d8: ret *)
(*    1148120: ret *)
| 0x1184d8 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001184dc: sub x2,x4,x3 *)
(*    1148124: sub x2,x4,x3 *)
| 0x1184dc => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X4) (Var R_X3))
)

(* 0x001184e0: sub x3,x3,#0x10 *)
(*    1148128: sub x3,x3,#0x10 *)
| 0x1184e0 => Some (4,
	Move R_X3 (BinOp OP_MINUS (Var R_X3) (Word 0x10 64))
)

(* 0x001184e4: sub x2,x2,#0x50 *)
(*    1148132: sub x2,x2,#0x50 *)
| 0x1184e4 => Some (4,
	Move R_X2 (BinOp OP_MINUS (Var R_X2) (Word 0x50 64))
)

(* 0x001184e8: stp q0,q0,[x3, #0x20] *)
(*    1148136: stp q0,q0,[x3, #0x20] *)
| 0x1184e8 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x001184ec: stp q0,q0,[x3, #0x40]! *)
(*    1148140: stp q0,q0,[x3, #0x40]! *)
| 0x1184ec => Some (4,
	Move R_X3 (BinOp OP_PLUS (Var R_X3) (Word 0x40 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_X3) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x001184f0: subs x2,x2,#0x40 *)
(*    1148144: subs x2,x2,#0x40 *)
| 0x1184f0 => Some (4,
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

(* 0x001184f4: b.hi 0x001184e8 *)
(*    1148148: b.hi 0x001184e8 *)
| 0x1184f4 => Some (4,
	Move (V_TEMP 0xd80) (UnOp OP_NOT (Var R_ZR)) $;
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x1184e8 64)
	) (* else *) (
		Nop
	)
)

(* 0x001184f8: stp q0,q0,[x4, #-0x40] *)
(*    1148152: stp q0,q0,[x4, #-0x40] *)
| 0x1184f8 => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x001184fc: stp q0,q0,[x4, #-0x20] *)
(*    1148156: stp q0,q0,[x4, #-0x20] *)
| 0x1184fc => Some (4,
	Move (V_TEMP 0x7780) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7780)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16) $;
	Move (V_TEMP 0x139680) (BinOp OP_PLUS (Var (V_TEMP 0x7780)) (Word 0x10 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x139680)) (Cast CAST_UNSIGNED 128 (Extract 127 0 (Var R_Z0))) LittleE 16)
)

(* 0x00118500: ret *)
(*    1148160: ret *)
| 0x118500 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx memset_armv8.
Proof. Picinae_typecheck. Qed.

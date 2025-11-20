(* Automatically generated with pcode2coq
arch: armv8
file: memcpy.lo
function: memcpy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition memcpy_lo_memcpy_armv8 : program := fun _ a => match a with

(* 0x00100000: add x4,x1,x2 *)
(*    1048576: add x4,x1,x2 *)
| 0x100000 => Some (4,
	(* (unique, 0x12380, 8) COPY (register, 0x4010, 8) *)
	Move (V_TEMP 0x12380) (Var R_X2) $;
	(* (register, 0x105, 1) INT_CARRY (register, 0x4008, 8) , (unique, 0x12380, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x12380))) (Var R_X1))) $;
	(* (register, 0x106, 1) INT_SCARRY (register, 0x4008, 8) , (unique, 0x12380, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x12380))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x12380)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x12480, 8) INT_ADD (register, 0x4008, 8) , (unique, 0x12380, 8) *)
	Move (V_TEMP 0x12480) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x12380))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x12480, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12480)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x12480, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12480)) (Word 0x0 64))) $;
	(* (register, 0x4020, 8) COPY (unique, 0x12480, 8) *)
	Move R_X4 (Var (V_TEMP 0x12480))
)

(* 0x00100004: add x5,x0,x2 *)
(*    1048580: add x5,x0,x2 *)
| 0x100004 => Some (4,
	(* (unique, 0x12380, 8) COPY (register, 0x4010, 8) *)
	Move (V_TEMP 0x12380) (Var R_X2) $;
	(* (register, 0x105, 1) INT_CARRY (register, 0x4000, 8) , (unique, 0x12380, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x12380))) (Var R_X0))) $;
	(* (register, 0x106, 1) INT_SCARRY (register, 0x4000, 8) , (unique, 0x12380, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x12380))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X0) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x12380)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x12480, 8) INT_ADD (register, 0x4000, 8) , (unique, 0x12380, 8) *)
	Move (V_TEMP 0x12480) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x12380))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x12480, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12480)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x12480, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12480)) (Word 0x0 64))) $;
	(* (register, 0x4028, 8) COPY (unique, 0x12480, 8) *)
	Move R_X5 (Var (V_TEMP 0x12480))
)

(* 0x00100008: cmp x2,#0x80 *)
(*    1048584: cmp x2,#0x80 *)
| 0x100008 => Some (4,
	(* (unique, 0x1cc80, 8) COPY (const, 0x80, 8) *)
	Move (V_TEMP 0x1cc80) (Word 0x80 64) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (unique, 0x1cc80, 8) , (register, 0x4010, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1cc80)) (Var R_X2))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1cc80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x1cd80, 8) INT_SUB (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move (V_TEMP 0x1cd80) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x0010000c: b.hi 0x00100100 *)
(*    1048588: b.hi 0x00100100 *)
| 0x10000c => Some (4,
	(* (unique, 0xd80, 1) BOOL_NEGATE (register, 0x101, 1) *)
	Move (V_TEMP 0xd80) (UnOp OP_NOT (Var R_ZR)) $;
	(* (unique, 0xe80, 1) BOOL_AND (register, 0x102, 1) , (unique, 0xd80, 1) *)
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	(*  ---  CBRANCH (ram, 0x100100, 8) , (unique, 0xe80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x100100 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100010: cmp x2,#0x20 *)
(*    1048592: cmp x2,#0x20 *)
| 0x100010 => Some (4,
	(* (unique, 0x1cc80, 8) COPY (const, 0x20, 8) *)
	Move (V_TEMP 0x1cc80) (Word 0x20 64) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (unique, 0x1cc80, 8) , (register, 0x4010, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1cc80)) (Var R_X2))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1cc80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x1cd80, 8) INT_SUB (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move (V_TEMP 0x1cd80) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x00100014: b.hi 0x00100090 *)
(*    1048596: b.hi 0x00100090 *)
| 0x100014 => Some (4,
	(* (unique, 0xd80, 1) BOOL_NEGATE (register, 0x101, 1) *)
	Move (V_TEMP 0xd80) (UnOp OP_NOT (Var R_ZR)) $;
	(* (unique, 0xe80, 1) BOOL_AND (register, 0x102, 1) , (unique, 0xd80, 1) *)
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	(*  ---  CBRANCH (ram, 0x100090, 8) , (unique, 0xe80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x100090 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100018: cmp x2,#0x10 *)
(*    1048600: cmp x2,#0x10 *)
| 0x100018 => Some (4,
	(* (unique, 0x1cc80, 8) COPY (const, 0x10, 8) *)
	Move (V_TEMP 0x1cc80) (Word 0x10 64) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (unique, 0x1cc80, 8) , (register, 0x4010, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1cc80)) (Var R_X2))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1cc80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x1cd80, 8) INT_SUB (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move (V_TEMP 0x1cd80) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x0010001c: b.cc 0x00100034 *)
(*    1048604: b.cc 0x00100034 *)
| 0x10001c => Some (4,
	(* (unique, 0xb00, 1) BOOL_NEGATE (register, 0x102, 1) *)
	Move (V_TEMP 0xb00) (UnOp OP_NOT (Var R_CY)) $;
	(*  ---  CBRANCH (ram, 0x100034, 8) , (unique, 0xb00, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xb00))) (
		Jmp (Word 0x100034 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100020: ldp x6,x7,[x1] *)
(*    1048608: ldp x6,x7,[x1] *)
| 0x100020 => Some (4,
	(* (unique, 0x7c00, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x7c00) (Var R_X1) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7c00, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7c00)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7c00, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7c00)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4030, 8) COPY (unique, 0x24680, 8) *)
	Move R_X6 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4038, 8) COPY (unique, 0x24800, 8) *)
	Move R_X7 (Var (V_TEMP 0x24800))
)

(* 0x00100024: ldp x12,x13,[x4, #-0x10] *)
(*    1048612: ldp x12,x13,[x4, #-0x10] *)
| 0x100024 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4060, 8) COPY (unique, 0x24680, 8) *)
	Move R_X12 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4068, 8) COPY (unique, 0x24800, 8) *)
	Move R_X13 (Var (V_TEMP 0x24800))
)

(* 0x00100028: stp x6,x7,[x0] *)
(*    1048616: stp x6,x7,[x0] *)
| 0x100028 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4030, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X6) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4038, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X7) $;
	(* (unique, 0x7c00, 8) COPY (register, 0x4000, 8) *)
	Move (V_TEMP 0x7c00) (Var R_X0) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7c00, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7c00)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7c00, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7c00)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x0010002c: stp x12,x13,[x5, #-0x10] *)
(*    1048620: stp x12,x13,[x5, #-0x10] *)
| 0x10002c => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4060, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X12) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4068, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X13) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100030: ret *)
(*    1048624: ret *)
| 0x100030 => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

(* 0x00100034: tbz w2,#0x3,0x00100050 *)
(*    1048628: tbz w2,#0x3,0x00100050 *)
| 0x100034 => Some (4,
	(* (unique, 0x18900, 4) INT_RIGHT (register, 0x4010, 4) , (const, 0x3, 4) *)
	Move (V_TEMP 0x18900) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x3 32)) $;
	(* (unique, 0x18980, 4) INT_AND (unique, 0x18900, 4) , (const, 0x1, 4) *)
	Move (V_TEMP 0x18980) (BinOp OP_AND (Var (V_TEMP 0x18900)) (Word 0x1 32)) $;
	(* (unique, 0x18a80, 1) INT_EQUAL (unique, 0x18980, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x18a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x18980)) (Word 0x0 32))) $;
	(* (unique, 0x3fc00, 1) INT_EQUAL (unique, 0x18a80, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x3fc00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x18a80)) (Word 0x1 8))) $;
	(*  ---  CBRANCH (ram, 0x100050, 8) , (unique, 0x3fc00, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3fc00))) (
		Jmp (Word 0x100050 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100038: ldr x6,[x1] *)
(*    1048632: ldr x6,[x1] *)
| 0x100038 => Some (4,
	(* (unique, 0x6800, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x6800) (Var R_X1) $;
	(* (register, 0x4030, 8) LOAD (const, 0x1b1, 8) , (unique, 0x6800, 8) *)
	Move R_X6 (Load (Var V_MEM64) (Var (V_TEMP 0x6800)) LittleE 8)
)

(* 0x0010003c: ldur x7,[x4, #-0x8] *)
(*    1048636: ldur x7,[x4, #-0x8] *)
| 0x10003c => Some (4,
	(* (unique, 0x6980, 8) INT_ADD (register, 0x4020, 8) , (const, 0xfffffffffffffff8, 8) *)
	Move (V_TEMP 0x6980) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff8 64)) $;
	(* (register, 0x4038, 8) LOAD (const, 0x1b1, 8) , (unique, 0x6980, 8) *)
	Move R_X7 (Load (Var V_MEM64) (Var (V_TEMP 0x6980)) LittleE 8)
)

(* 0x00100040: str x6,[x0] *)
(*    1048640: str x6,[x0] *)
| 0x100040 => Some (4,
	(* (unique, 0x6800, 8) COPY (register, 0x4000, 8) *)
	Move (V_TEMP 0x6800) (Var R_X0) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x6800, 8) , (register, 0x4030, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6800)) (Cast CAST_LOW 64 (Var R_X6)) LittleE 8)
)

(* 0x00100044: stur x7,[x5, #-0x8] *)
(*    1048644: stur x7,[x5, #-0x8] *)
| 0x100044 => Some (4,
	(* (unique, 0x3b180, 8) COPY (register, 0x4038, 8) *)
	Move (V_TEMP 0x3b180) (Var R_X7) $;
	(* (unique, 0x6980, 8) INT_ADD (register, 0x4028, 8) , (const, 0xfffffffffffffff8, 8) *)
	Move (V_TEMP 0x6980) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x6980, 8) , (unique, 0x3b180, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6980)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3b180))) LittleE 8)
)

(* 0x00100048: ret *)
(*    1048648: ret *)
| 0x100048 => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

(* 0x00100050: tbz w2,#0x2,0x00100068 *)
(*    1048656: tbz w2,#0x2,0x00100068 *)
| 0x100050 => Some (4,
	(* (unique, 0x18900, 4) INT_RIGHT (register, 0x4010, 4) , (const, 0x2, 4) *)
	Move (V_TEMP 0x18900) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0x2 32)) $;
	(* (unique, 0x18980, 4) INT_AND (unique, 0x18900, 4) , (const, 0x1, 4) *)
	Move (V_TEMP 0x18980) (BinOp OP_AND (Var (V_TEMP 0x18900)) (Word 0x1 32)) $;
	(* (unique, 0x18a80, 1) INT_EQUAL (unique, 0x18980, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x18a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x18980)) (Word 0x0 32))) $;
	(* (unique, 0x3fc00, 1) INT_EQUAL (unique, 0x18a80, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x3fc00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x18a80)) (Word 0x1 8))) $;
	(*  ---  CBRANCH (ram, 0x100068, 8) , (unique, 0x3fc00, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3fc00))) (
		Jmp (Word 0x100068 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100054: ldr w6,[x1] *)
(*    1048660: ldr w6,[x1] *)
| 0x100054 => Some (4,
	(* (unique, 0x6780, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x6780) (Var R_X1) $;
	(* (unique, 0x24c00, 4) LOAD (const, 0x1b1, 8) , (unique, 0x6780, 8) *)
	Move (V_TEMP 0x24c00) (Load (Var V_MEM64) (Var (V_TEMP 0x6780)) LittleE 4) $;
	(* (register, 0x4030, 8) INT_ZEXT (unique, 0x24c00, 4) *)
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24c00)))
)

(* 0x00100058: ldur w8,[x4, #-0x4] *)
(*    1048664: ldur w8,[x4, #-0x4] *)
| 0x100058 => Some (4,
	(* (unique, 0x6980, 8) INT_ADD (register, 0x4020, 8) , (const, 0xfffffffffffffffc, 8) *)
	Move (V_TEMP 0x6980) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffffc 64)) $;
	(* (unique, 0x24d00, 4) LOAD (const, 0x1b1, 8) , (unique, 0x6980, 8) *)
	Move (V_TEMP 0x24d00) (Load (Var V_MEM64) (Var (V_TEMP 0x6980)) LittleE 4) $;
	(* (register, 0x4040, 8) INT_ZEXT (unique, 0x24d00, 4) *)
	Move R_X8 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24d00)))
)

(* 0x0010005c: str w6,[x0] *)
(*    1048668: str w6,[x0] *)
| 0x10005c => Some (4,
	(* (unique, 0x6780, 8) COPY (register, 0x4000, 8) *)
	Move (V_TEMP 0x6780) (Var R_X0) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x6780, 8) , (register, 0x4030, 4) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6780)) (Cast CAST_LOW 32 (Extract 31 0 (Var R_X6))) LittleE 4)
)

(* 0x00100060: stur w8,[x5, #-0x4] *)
(*    1048672: stur w8,[x5, #-0x4] *)
| 0x100060 => Some (4,
	(* (unique, 0x3a680, 4) COPY (register, 0x4040, 4) *)
	Move (V_TEMP 0x3a680) (Extract 31 0 (Var R_X8)) $;
	(* (unique, 0x6980, 8) INT_ADD (register, 0x4028, 8) , (const, 0xfffffffffffffffc, 8) *)
	Move (V_TEMP 0x6980) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffffc 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x6980, 8) , (unique, 0x3a680, 4) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6980)) (Cast CAST_LOW 32 (Var (V_TEMP 0x3a680))) LittleE 4)
)

(* 0x00100064: ret *)
(*    1048676: ret *)
| 0x100064 => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

(* 0x00100068: cbz x2,0x00100088 *)
(*    1048680: cbz x2,0x00100088 *)
| 0x100068 => Some (4,
	(* (unique, 0x18f80, 1) INT_EQUAL (register, 0x4010, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x18f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_X2) (Word 0x0 64))) $;
	(*  ---  CBRANCH (ram, 0x100088, 8) , (unique, 0x18f80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18f80))) (
		Jmp (Word 0x100088 64)
	) (* else *) (
		Nop
	)
)

(* 0x0010006c: lsr x14,x2,#0x1 *)
(*    1048684: lsr x14,x2,#0x1 *)
| 0x10006c => Some (4,
	(* (register, 0x4070, 8) INT_RIGHT (register, 0x4010, 8) , (const, 0x1, 8) *)
	Move R_X14 (BinOp OP_RSHIFT (Var R_X2) (Word 0x1 64))
)

(* 0x00100070: ldrb w6,[x1] *)
(*    1048688: ldrb w6,[x1] *)
| 0x100070 => Some (4,
	(* (unique, 0x6680, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x6680) (Var R_X1) $;
	(* (unique, 0x25500, 1) LOAD (const, 0x1b1, 8) , (unique, 0x6680, 8) *)
	Move (V_TEMP 0x25500) (Load (Var V_MEM64) (Var (V_TEMP 0x6680)) LittleE 1) $;
	(* (register, 0x4030, 8) INT_ZEXT (unique, 0x25500, 1) *)
	Move R_X6 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25500)))
)

(* 0x00100074: ldurb w10,[x4, #-0x1] *)
(*    1048692: ldurb w10,[x4, #-0x1] *)
| 0x100074 => Some (4,
	(* (unique, 0x6980, 8) INT_ADD (register, 0x4020, 8) , (const, 0xffffffffffffffff, 8) *)
	Move (V_TEMP 0x6980) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffff 64)) $;
	(* (unique, 0x26e80, 1) LOAD (const, 0x1b1, 8) , (unique, 0x6980, 8) *)
	Move (V_TEMP 0x26e80) (Load (Var V_MEM64) (Var (V_TEMP 0x6980)) LittleE 1) $;
	(* (register, 0x4050, 8) INT_ZEXT (unique, 0x26e80, 1) *)
	Move R_X10 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x26e80)))
)

(* 0x00100078: ldrb w8,[x1, x14, LSL ] *)
(*    1048696: ldrb w8,[x1, x14, LSL ] *)
| 0x100078 => Some (4,
	(* (unique, 0x5a00, 8) COPY (register, 0x4070, 8) *)
	Move (V_TEMP 0x5a00) (Var R_X14) $;
	(* (unique, 0x7100, 8) COPY (unique, 0x5a00, 8) *)
	Move (V_TEMP 0x7100) (Var (V_TEMP 0x5a00)) $;
	(* (unique, 0x7100, 8) INT_LEFT (unique, 0x7100, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x7100) (BinOp OP_LSHIFT (Var (V_TEMP 0x7100)) (Word 0x0 64)) $;
	(* (unique, 0x7580, 8) INT_ADD (register, 0x4008, 8) , (unique, 0x7100, 8) *)
	Move (V_TEMP 0x7580) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 0x7100))) $;
	(* (unique, 0x25600, 1) LOAD (const, 0x1b1, 8) , (unique, 0x7580, 8) *)
	Move (V_TEMP 0x25600) (Load (Var V_MEM64) (Var (V_TEMP 0x7580)) LittleE 1) $;
	(* (register, 0x4040, 8) INT_ZEXT (unique, 0x25600, 1) *)
	Move R_X8 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25600)))
)

(* 0x0010007c: strb w6,[x0] *)
(*    1048700: strb w6,[x0] *)
| 0x10007c => Some (4,
	(* (unique, 0x3a900, 4) COPY (register, 0x4030, 4) *)
	Move (V_TEMP 0x3a900) (Extract 31 0 (Var R_X6)) $;
	(* (unique, 0x6680, 8) COPY (register, 0x4000, 8) *)
	Move (V_TEMP 0x6680) (Var R_X0) $;
	(* (unique, 0x3a980, 1) SUBPIECE (unique, 0x3a900, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x3a980) (Cast CAST_LOW 8 (BinOp OP_RSHIFT (Var (V_TEMP 0x3a900)) (Word 0 32))) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x6680, 8) , (unique, 0x3a980, 1) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6680)) (Cast CAST_LOW 8 (Var (V_TEMP 0x3a980))) LittleE 1)
)

(* 0x00100080: strb w8,[x0, x14, LSL ] *)
(*    1048704: strb w8,[x0, x14, LSL ] *)
| 0x100080 => Some (4,
	(* (unique, 0x3ab00, 4) COPY (register, 0x4040, 4) *)
	Move (V_TEMP 0x3ab00) (Extract 31 0 (Var R_X8)) $;
	(* (unique, 0x5a00, 8) COPY (register, 0x4070, 8) *)
	Move (V_TEMP 0x5a00) (Var R_X14) $;
	(* (unique, 0x7100, 8) COPY (unique, 0x5a00, 8) *)
	Move (V_TEMP 0x7100) (Var (V_TEMP 0x5a00)) $;
	(* (unique, 0x7100, 8) INT_LEFT (unique, 0x7100, 8) , (const, 0x0, 8) *)
	Move (V_TEMP 0x7100) (BinOp OP_LSHIFT (Var (V_TEMP 0x7100)) (Word 0x0 64)) $;
	(* (unique, 0x7580, 8) INT_ADD (register, 0x4000, 8) , (unique, 0x7100, 8) *)
	Move (V_TEMP 0x7580) (BinOp OP_PLUS (Var R_X0) (Var (V_TEMP 0x7100))) $;
	(* (unique, 0x3ab80, 1) SUBPIECE (unique, 0x3ab00, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x3ab80) (Cast CAST_LOW 8 (BinOp OP_RSHIFT (Var (V_TEMP 0x3ab00)) (Word 0 32))) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7580, 8) , (unique, 0x3ab80, 1) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7580)) (Cast CAST_LOW 8 (Var (V_TEMP 0x3ab80))) LittleE 1)
)

(* 0x00100084: sturb w10,[x5, #-0x1] *)
(*    1048708: sturb w10,[x5, #-0x1] *)
| 0x100084 => Some (4,
	(* (unique, 0x3af80, 4) COPY (register, 0x4050, 4) *)
	Move (V_TEMP 0x3af80) (Extract 31 0 (Var R_X10)) $;
	(* (unique, 0x6980, 8) INT_ADD (register, 0x4028, 8) , (const, 0xffffffffffffffff, 8) *)
	Move (V_TEMP 0x6980) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffff 64)) $;
	(* (unique, 0x3b000, 1) SUBPIECE (unique, 0x3af80, 4) , (const, 0x0, 4) *)
	Move (V_TEMP 0x3b000) (Cast CAST_LOW 8 (BinOp OP_RSHIFT (Var (V_TEMP 0x3af80)) (Word 0 32))) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x6980, 8) , (unique, 0x3b000, 1) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6980)) (Cast CAST_LOW 8 (Var (V_TEMP 0x3b000))) LittleE 1)
)

(* 0x00100088: ret *)
(*    1048712: ret *)
| 0x100088 => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

(* 0x00100090: ldp x6,x7,[x1] *)
(*    1048720: ldp x6,x7,[x1] *)
| 0x100090 => Some (4,
	(* (unique, 0x7c00, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x7c00) (Var R_X1) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7c00, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7c00)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7c00, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7c00)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4030, 8) COPY (unique, 0x24680, 8) *)
	Move R_X6 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4038, 8) COPY (unique, 0x24800, 8) *)
	Move R_X7 (Var (V_TEMP 0x24800))
)

(* 0x00100094: ldp x8,x9,[x1, #0x10] *)
(*    1048724: ldp x8,x9,[x1, #0x10] *)
| 0x100094 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4040, 8) COPY (unique, 0x24680, 8) *)
	Move R_X8 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4048, 8) COPY (unique, 0x24800, 8) *)
	Move R_X9 (Var (V_TEMP 0x24800))
)

(* 0x00100098: ldp x10,x11,[x4, #-0x20] *)
(*    1048728: ldp x10,x11,[x4, #-0x20] *)
| 0x100098 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xffffffffffffffe0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4050, 8) COPY (unique, 0x24680, 8) *)
	Move R_X10 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4058, 8) COPY (unique, 0x24800, 8) *)
	Move R_X11 (Var (V_TEMP 0x24800))
)

(* 0x0010009c: ldp x12,x13,[x4, #-0x10] *)
(*    1048732: ldp x12,x13,[x4, #-0x10] *)
| 0x10009c => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4060, 8) COPY (unique, 0x24680, 8) *)
	Move R_X12 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4068, 8) COPY (unique, 0x24800, 8) *)
	Move R_X13 (Var (V_TEMP 0x24800))
)

(* 0x001000a0: cmp x2,#0x40 *)
(*    1048736: cmp x2,#0x40 *)
| 0x1000a0 => Some (4,
	(* (unique, 0x1cc80, 8) COPY (const, 0x40, 8) *)
	Move (V_TEMP 0x1cc80) (Word 0x40 64) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (unique, 0x1cc80, 8) , (register, 0x4010, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1cc80)) (Var R_X2))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1cc80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x1cd80, 8) INT_SUB (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move (V_TEMP 0x1cd80) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x001000a4: b.hi 0x001000c0 *)
(*    1048740: b.hi 0x001000c0 *)
| 0x1000a4 => Some (4,
	(* (unique, 0xd80, 1) BOOL_NEGATE (register, 0x101, 1) *)
	Move (V_TEMP 0xd80) (UnOp OP_NOT (Var R_ZR)) $;
	(* (unique, 0xe80, 1) BOOL_AND (register, 0x102, 1) , (unique, 0xd80, 1) *)
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	(*  ---  CBRANCH (ram, 0x1000c0, 8) , (unique, 0xe80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x1000c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001000a8: stp x6,x7,[x0] *)
(*    1048744: stp x6,x7,[x0] *)
| 0x1000a8 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4030, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X6) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4038, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X7) $;
	(* (unique, 0x7c00, 8) COPY (register, 0x4000, 8) *)
	Move (V_TEMP 0x7c00) (Var R_X0) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7c00, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7c00)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7c00, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7c00)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000ac: stp x8,x9,[x0, #0x10] *)
(*    1048748: stp x8,x9,[x0, #0x10] *)
| 0x1000ac => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4040, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X8) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4048, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X9) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4000, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000b0: stp x10,x11,[x5, #-0x20] *)
(*    1048752: stp x10,x11,[x5, #-0x20] *)
| 0x1000b0 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4050, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X10) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4058, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X11) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xffffffffffffffe0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000b4: stp x12,x13,[x5, #-0x10] *)
(*    1048756: stp x12,x13,[x5, #-0x10] *)
| 0x1000b4 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4060, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X12) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4068, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X13) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000b8: ret *)
(*    1048760: ret *)
| 0x1000b8 => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

(* 0x001000c0: ldp x14,x15,[x1, #0x20] *)
(*    1048768: ldp x14,x15,[x1, #0x20] *)
| 0x1000c0 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4070, 8) COPY (unique, 0x24680, 8) *)
	Move R_X14 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4078, 8) COPY (unique, 0x24800, 8) *)
	Move R_X15 (Var (V_TEMP 0x24800))
)

(* 0x001000c4: ldp x16,x17,[x1, #0x30] *)
(*    1048772: ldp x16,x17,[x1, #0x30] *)
| 0x1000c4 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x30, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4080, 8) COPY (unique, 0x24680, 8) *)
	Move R_X16 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4088, 8) COPY (unique, 0x24800, 8) *)
	Move R_X17 (Var (V_TEMP 0x24800))
)

(* 0x001000c8: cmp x2,#0x60 *)
(*    1048776: cmp x2,#0x60 *)
| 0x1000c8 => Some (4,
	(* (unique, 0x1cc80, 8) COPY (const, 0x60, 8) *)
	Move (V_TEMP 0x1cc80) (Word 0x60 64) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (unique, 0x1cc80, 8) , (register, 0x4010, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x1cc80)) (Var R_X2))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x1cc80)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x1cd80, 8) INT_SUB (register, 0x4010, 8) , (unique, 0x1cc80, 8) *)
	Move (V_TEMP 0x1cd80) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x1cc80))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x1cd80, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x1cd80)) (Word 0x0 64))) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x001000cc: b.ls 0x001000e0 *)
(*    1048780: b.ls 0x001000e0 *)
| 0x1000cc => Some (4,
	(* (unique, 0xf00, 1) BOOL_NEGATE (register, 0x102, 1) *)
	Move (V_TEMP 0xf00) (UnOp OP_NOT (Var R_CY)) $;
	(* (unique, 0x1000, 1) BOOL_OR (unique, 0xf00, 1) , (register, 0x101, 1) *)
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	(*  ---  CBRANCH (ram, 0x1000e0, 8) , (unique, 0x1000, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x1000e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001000d0: ldp x2,x3,[x4, #-0x40] *)
(*    1048784: ldp x2,x3,[x4, #-0x40] *)
| 0x1000d0 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xffffffffffffffc0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4010, 8) COPY (unique, 0x24680, 8) *)
	Move R_X2 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4018, 8) COPY (unique, 0x24800, 8) *)
	Move R_X3 (Var (V_TEMP 0x24800))
)

(* 0x001000d4: ldp x1,x4,[x4, #-0x30] *)
(*    1048788: ldp x1,x4,[x4, #-0x30] *)
| 0x1000d4 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xffffffffffffffd0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffd0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4008, 8) COPY (unique, 0x24680, 8) *)
	Move R_X1 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4020, 8) COPY (unique, 0x24800, 8) *)
	Move R_X4 (Var (V_TEMP 0x24800))
)

(* 0x001000d8: stp x2,x3,[x5, #-0x40] *)
(*    1048792: stp x2,x3,[x5, #-0x40] *)
| 0x1000d8 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4010, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X2) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4018, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X3) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xffffffffffffffc0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffc0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000dc: stp x1,x4,[x5, #-0x30] *)
(*    1048796: stp x1,x4,[x5, #-0x30] *)
| 0x1000dc => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X1) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4020, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X4) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xffffffffffffffd0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffd0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000e0: stp x6,x7,[x0] *)
(*    1048800: stp x6,x7,[x0] *)
| 0x1000e0 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4030, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X6) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4038, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X7) $;
	(* (unique, 0x7c00, 8) COPY (register, 0x4000, 8) *)
	Move (V_TEMP 0x7c00) (Var R_X0) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7c00, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7c00)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7c00, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7c00)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000e4: stp x8,x9,[x0, #0x10] *)
(*    1048804: stp x8,x9,[x0, #0x10] *)
| 0x1000e4 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4040, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X8) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4048, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X9) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4000, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000e8: stp x14,x15,[x0, #0x20] *)
(*    1048808: stp x14,x15,[x0, #0x20] *)
| 0x1000e8 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4070, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X14) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4078, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X15) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4000, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000ec: stp x16,x17,[x0, #0x30] *)
(*    1048812: stp x16,x17,[x0, #0x30] *)
| 0x1000ec => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4080, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X16) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4088, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X17) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4000, 8) , (const, 0x30, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X0) (Word 0x30 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000f0: stp x10,x11,[x5, #-0x20] *)
(*    1048816: stp x10,x11,[x5, #-0x20] *)
| 0x1000f0 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4050, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X10) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4058, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X11) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xffffffffffffffe0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000f4: stp x12,x13,[x5, #-0x10] *)
(*    1048820: stp x12,x13,[x5, #-0x10] *)
| 0x1000f4 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4060, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X12) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4068, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X13) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x001000f8: ret *)
(*    1048824: ret *)
| 0x1000f8 => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

(* 0x00100100: ldp x12,x13,[x1] *)
(*    1048832: ldp x12,x13,[x1] *)
| 0x100100 => Some (4,
	(* (unique, 0x7c00, 8) COPY (register, 0x4008, 8) *)
	Move (V_TEMP 0x7c00) (Var R_X1) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7c00, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7c00)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7c00, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7c00)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4060, 8) COPY (unique, 0x24680, 8) *)
	Move R_X12 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4068, 8) COPY (unique, 0x24800, 8) *)
	Move R_X13 (Var (V_TEMP 0x24800))
)

(* 0x00100104: and x14,x0,#0xf *)
(*    1048836: and x14,x0,#0xf *)
| 0x100104 => Some (4,
	(* (register, 0x4070, 8) INT_AND (register, 0x4000, 8) , (const, 0xf, 8) *)
	Move R_X14 (BinOp OP_AND (Var R_X0) (Word 0xf 64))
)

(* 0x00100108: and x3,x0,#-0x10 *)
(*    1048840: and x3,x0,#-0x10 *)
| 0x100108 => Some (4,
	(* (register, 0x4018, 8) INT_AND (register, 0x4000, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move R_X3 (BinOp OP_AND (Var R_X0) (Word 0xfffffffffffffff0 64))
)

(* 0x0010010c: sub x1,x1,x14 *)
(*    1048844: sub x1,x1,x14 *)
| 0x10010c => Some (4,
	(* (register, 0x4008, 8) INT_SUB (register, 0x4008, 8) , (register, 0x4070, 8) *)
	Move R_X1 (BinOp OP_MINUS (Var R_X1) (Var R_X14))
)

(* 0x00100110: add x2,x2,x14 *)
(*    1048848: add x2,x2,x14 *)
| 0x100110 => Some (4,
	(* (unique, 0x12380, 8) COPY (register, 0x4070, 8) *)
	Move (V_TEMP 0x12380) (Var R_X14) $;
	(* (register, 0x105, 1) INT_CARRY (register, 0x4010, 8) , (unique, 0x12380, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x12380))) (Var R_X2))) $;
	(* (register, 0x106, 1) INT_SCARRY (register, 0x4010, 8) , (unique, 0x12380, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x12380))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x12380)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x12480, 8) INT_ADD (register, 0x4010, 8) , (unique, 0x12380, 8) *)
	Move (V_TEMP 0x12480) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 0x12380))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x12480, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x12480)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x12480, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x12480)) (Word 0x0 64))) $;
	(* (register, 0x4010, 8) COPY (unique, 0x12480, 8) *)
	Move R_X2 (Var (V_TEMP 0x12480))
)

(* 0x00100114: ldp x6,x7,[x1, #0x10] *)
(*    1048852: ldp x6,x7,[x1, #0x10] *)
| 0x100114 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4030, 8) COPY (unique, 0x24680, 8) *)
	Move R_X6 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4038, 8) COPY (unique, 0x24800, 8) *)
	Move R_X7 (Var (V_TEMP 0x24800))
)

(* 0x00100118: stp x12,x13,[x0] *)
(*    1048856: stp x12,x13,[x0] *)
| 0x100118 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4060, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X12) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4068, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X13) $;
	(* (unique, 0x7c00, 8) COPY (register, 0x4000, 8) *)
	Move (V_TEMP 0x7c00) (Var R_X0) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7c00, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7c00)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7c00, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7c00)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x0010011c: ldp x8,x9,[x1, #0x20] *)
(*    1048860: ldp x8,x9,[x1, #0x20] *)
| 0x10011c => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4040, 8) COPY (unique, 0x24680, 8) *)
	Move R_X8 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4048, 8) COPY (unique, 0x24800, 8) *)
	Move R_X9 (Var (V_TEMP 0x24800))
)

(* 0x00100120: ldp x10,x11,[x1, #0x30] *)
(*    1048864: ldp x10,x11,[x1, #0x30] *)
| 0x100120 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x30, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4050, 8) COPY (unique, 0x24680, 8) *)
	Move R_X10 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4058, 8) COPY (unique, 0x24800, 8) *)
	Move R_X11 (Var (V_TEMP 0x24800))
)

(* 0x00100124: ldp x12,x13,[x1, #0x40]! *)
(*    1048868: ldp x12,x13,[x1, #0x40]! *)
| 0x100124 => Some (4,
	(* (register, 0x4008, 8) INT_ADD (register, 0x4008, 8) , (const, 0x40, 8) *)
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x40 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (register, 0x4008, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var R_X1) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (register, 0x4008, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4060, 8) COPY (unique, 0x24680, 8) *)
	Move R_X12 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4068, 8) COPY (unique, 0x24800, 8) *)
	Move R_X13 (Var (V_TEMP 0x24800))
)

(* 0x00100128: subs x2,x2,#0x90 *)
(*    1048872: subs x2,x2,#0x90 *)
| 0x100128 => Some (4,
	(* (unique, 0x3e180, 8) COPY (const, 0x90, 8) *)
	Move (V_TEMP 0x3e180) (Word 0x90 64) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (unique, 0x3e180, 8) , (register, 0x4010, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x3e180)) (Var R_X2))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 8) , (unique, 0x3e180, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3e180))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3e180))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e180)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x3e280, 8) INT_SUB (register, 0x4010, 8) , (unique, 0x3e180, 8) *)
	Move (V_TEMP 0x3e280) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3e180))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x3e280, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e280)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x3e280, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e280)) (Word 0x0 64))) $;
	(* (register, 0x4010, 8) COPY (unique, 0x3e280, 8) *)
	Move R_X2 (Var (V_TEMP 0x3e280)) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x0010012c: b.ls 0x00100158 *)
(*    1048876: b.ls 0x00100158 *)
| 0x10012c => Some (4,
	(* (unique, 0xf00, 1) BOOL_NEGATE (register, 0x102, 1) *)
	Move (V_TEMP 0xf00) (UnOp OP_NOT (Var R_CY)) $;
	(* (unique, 0x1000, 1) BOOL_OR (unique, 0xf00, 1) , (register, 0x101, 1) *)
	Move (V_TEMP 0x1000) (BinOp OP_OR (Var (V_TEMP 0xf00)) (Var R_ZR)) $;
	(*  ---  CBRANCH (ram, 0x100158, 8) , (unique, 0x1000, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1000))) (
		Jmp (Word 0x100158 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100130: stp x6,x7,[x3, #0x10] *)
(*    1048880: stp x6,x7,[x3, #0x10] *)
| 0x100130 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4030, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X6) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4038, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X7) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4018, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100134: ldp x6,x7,[x1, #0x10] *)
(*    1048884: ldp x6,x7,[x1, #0x10] *)
| 0x100134 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x10 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4030, 8) COPY (unique, 0x24680, 8) *)
	Move R_X6 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4038, 8) COPY (unique, 0x24800, 8) *)
	Move R_X7 (Var (V_TEMP 0x24800))
)

(* 0x00100138: stp x8,x9,[x3, #0x20] *)
(*    1048888: stp x8,x9,[x3, #0x20] *)
| 0x100138 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4040, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X8) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4048, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X9) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4018, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x0010013c: ldp x8,x9,[x1, #0x20] *)
(*    1048892: ldp x8,x9,[x1, #0x20] *)
| 0x10013c => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x20 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4040, 8) COPY (unique, 0x24680, 8) *)
	Move R_X8 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4048, 8) COPY (unique, 0x24800, 8) *)
	Move R_X9 (Var (V_TEMP 0x24800))
)

(* 0x00100140: stp x10,x11,[x3, #0x30] *)
(*    1048896: stp x10,x11,[x3, #0x30] *)
| 0x100140 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4050, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X10) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4058, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X11) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4018, 8) , (const, 0x30, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X3) (Word 0x30 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100144: ldp x10,x11,[x1, #0x30] *)
(*    1048900: ldp x10,x11,[x1, #0x30] *)
| 0x100144 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4008, 8) , (const, 0x30, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X1) (Word 0x30 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4050, 8) COPY (unique, 0x24680, 8) *)
	Move R_X10 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4058, 8) COPY (unique, 0x24800, 8) *)
	Move R_X11 (Var (V_TEMP 0x24800))
)

(* 0x00100148: stp x12,x13,[x3, #0x40]! *)
(*    1048904: stp x12,x13,[x3, #0x40]! *)
| 0x100148 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4060, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X12) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4068, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X13) $;
	(* (register, 0x4018, 8) INT_ADD (register, 0x4018, 8) , (const, 0x40, 8) *)
	Move R_X3 (BinOp OP_PLUS (Var R_X3) (Word 0x40 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x4018, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_X3) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (register, 0x4018, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var R_X3) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x0010014c: ldp x12,x13,[x1, #0x40]! *)
(*    1048908: ldp x12,x13,[x1, #0x40]! *)
| 0x10014c => Some (4,
	(* (register, 0x4008, 8) INT_ADD (register, 0x4008, 8) , (const, 0x40, 8) *)
	Move R_X1 (BinOp OP_PLUS (Var R_X1) (Word 0x40 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (register, 0x4008, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var R_X1) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (register, 0x4008, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var R_X1) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4060, 8) COPY (unique, 0x24680, 8) *)
	Move R_X12 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4068, 8) COPY (unique, 0x24800, 8) *)
	Move R_X13 (Var (V_TEMP 0x24800))
)

(* 0x00100150: subs x2,x2,#0x40 *)
(*    1048912: subs x2,x2,#0x40 *)
| 0x100150 => Some (4,
	(* (unique, 0x3e180, 8) COPY (const, 0x40, 8) *)
	Move (V_TEMP 0x3e180) (Word 0x40 64) $;
	(* (register, 0x105, 1) INT_LESSEQUAL (unique, 0x3e180, 8) , (register, 0x4010, 8) *)
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Var (V_TEMP 0x3e180)) (Var R_X2))) $;
	(* (register, 0x106, 1) INT_SBORROW (register, 0x4010, 8) , (unique, 0x3e180, 8) *)
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3e180))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3e180))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e180)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	(* (unique, 0x3e280, 8) INT_SUB (register, 0x4010, 8) , (unique, 0x3e180, 8) *)
	Move (V_TEMP 0x3e280) (BinOp OP_MINUS (Var R_X2) (Var (V_TEMP 0x3e180))) $;
	(* (register, 0x107, 1) INT_SLESS (unique, 0x3e280, 8) , (const, 0x0, 8) *)
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e280)) (Word 0x0 64))) $;
	(* (register, 0x108, 1) INT_EQUAL (unique, 0x3e280, 8) , (const, 0x0, 8) *)
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e280)) (Word 0x0 64))) $;
	(* (register, 0x4010, 8) COPY (unique, 0x3e280, 8) *)
	Move R_X2 (Var (V_TEMP 0x3e280)) $;
	(* (register, 0x100, 1) COPY (register, 0x107, 1) *)
	Move R_NG (Var R_TMPNG) $;
	(* (register, 0x101, 1) COPY (register, 0x108, 1) *)
	Move R_ZR (Var R_TMPZR) $;
	(* (register, 0x102, 1) COPY (register, 0x105, 1) *)
	Move R_CY (Var R_TMPCY) $;
	(* (register, 0x103, 1) COPY (register, 0x106, 1) *)
	Move R_OV (Var R_TMPOV)
)

(* 0x00100154: b.hi 0x00100130 *)
(*    1048916: b.hi 0x00100130 *)
| 0x100154 => Some (4,
	(* (unique, 0xd80, 1) BOOL_NEGATE (register, 0x101, 1) *)
	Move (V_TEMP 0xd80) (UnOp OP_NOT (Var R_ZR)) $;
	(* (unique, 0xe80, 1) BOOL_AND (register, 0x102, 1) , (unique, 0xd80, 1) *)
	Move (V_TEMP 0xe80) (BinOp OP_AND (Var R_CY) (Var (V_TEMP 0xd80))) $;
	(*  ---  CBRANCH (ram, 0x100130, 8) , (unique, 0xe80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xe80))) (
		Jmp (Word 0x100130 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100158: ldp x14,x15,[x4, #-0x40] *)
(*    1048920: ldp x14,x15,[x4, #-0x40] *)
| 0x100158 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xffffffffffffffc0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffc0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4070, 8) COPY (unique, 0x24680, 8) *)
	Move R_X14 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4078, 8) COPY (unique, 0x24800, 8) *)
	Move R_X15 (Var (V_TEMP 0x24800))
)

(* 0x0010015c: stp x6,x7,[x3, #0x10] *)
(*    1048924: stp x6,x7,[x3, #0x10] *)
| 0x10015c => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4030, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X6) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4038, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X7) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4018, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X3) (Word 0x10 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100160: ldp x6,x7,[x4, #-0x30] *)
(*    1048928: ldp x6,x7,[x4, #-0x30] *)
| 0x100160 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xffffffffffffffd0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffd0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4030, 8) COPY (unique, 0x24680, 8) *)
	Move R_X6 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4038, 8) COPY (unique, 0x24800, 8) *)
	Move R_X7 (Var (V_TEMP 0x24800))
)

(* 0x00100164: stp x8,x9,[x3, #0x20] *)
(*    1048932: stp x8,x9,[x3, #0x20] *)
| 0x100164 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4040, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X8) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4048, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X9) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4018, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X3) (Word 0x20 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100168: ldp x8,x9,[x4, #-0x20] *)
(*    1048936: ldp x8,x9,[x4, #-0x20] *)
| 0x100168 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xffffffffffffffe0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xffffffffffffffe0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4040, 8) COPY (unique, 0x24680, 8) *)
	Move R_X8 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4048, 8) COPY (unique, 0x24800, 8) *)
	Move R_X9 (Var (V_TEMP 0x24800))
)

(* 0x0010016c: stp x10,x11,[x3, #0x30] *)
(*    1048940: stp x10,x11,[x3, #0x30] *)
| 0x10016c => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4050, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X10) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4058, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X11) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4018, 8) , (const, 0x30, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X3) (Word 0x30 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100170: ldp x10,x11,[x4, #-0x10] *)
(*    1048944: ldp x10,x11,[x4, #-0x10] *)
| 0x100170 => Some (4,
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4020, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X4) (Word 0xfffffffffffffff0 64)) $;
	(* (unique, 0x24680, 8) LOAD (const, 0x1b1, 8) , (unique, 0x7b80, 8) *)
	Move (V_TEMP 0x24680) (Load (Var V_MEM64) (Var (V_TEMP 0x7b80)) LittleE 8) $;
	(* (unique, 0x24700, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x24700) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(* (unique, 0x24800, 8) LOAD (const, 0x1b1, 8) , (unique, 0x24700, 8) *)
	Move (V_TEMP 0x24800) (Load (Var V_MEM64) (Var (V_TEMP 0x24700)) LittleE 8) $;
	(* (register, 0x4050, 8) COPY (unique, 0x24680, 8) *)
	Move R_X10 (Var (V_TEMP 0x24680)) $;
	(* (register, 0x4058, 8) COPY (unique, 0x24800, 8) *)
	Move R_X11 (Var (V_TEMP 0x24800))
)

(* 0x00100174: stp x12,x13,[x3, #0x40] *)
(*    1048948: stp x12,x13,[x3, #0x40] *)
| 0x100174 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4060, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X12) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4068, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X13) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4018, 8) , (const, 0x40, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X3) (Word 0x40 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100178: stp x14,x15,[x5, #-0x40] *)
(*    1048952: stp x14,x15,[x5, #-0x40] *)
| 0x100178 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4070, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X14) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4078, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X15) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xffffffffffffffc0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffc0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x0010017c: stp x6,x7,[x5, #-0x30] *)
(*    1048956: stp x6,x7,[x5, #-0x30] *)
| 0x10017c => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4030, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X6) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4038, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X7) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xffffffffffffffd0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffd0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100180: stp x8,x9,[x5, #-0x20] *)
(*    1048960: stp x8,x9,[x5, #-0x20] *)
| 0x100180 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4040, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X8) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4048, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X9) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xffffffffffffffe0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xffffffffffffffe0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100184: stp x10,x11,[x5, #-0x10] *)
(*    1048964: stp x10,x11,[x5, #-0x10] *)
| 0x100184 => Some (4,
	(* (unique, 0x3a500, 8) COPY (register, 0x4050, 8) *)
	Move (V_TEMP 0x3a500) (Var R_X10) $;
	(* (unique, 0x3a580, 8) COPY (register, 0x4058, 8) *)
	Move (V_TEMP 0x3a580) (Var R_X11) $;
	(* (unique, 0x7b80, 8) INT_ADD (register, 0x4028, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move (V_TEMP 0x7b80) (BinOp OP_PLUS (Var R_X5) (Word 0xfffffffffffffff0 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x7b80, 8) , (unique, 0x3a500, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x7b80)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a500))) LittleE 8) $;
	(* (unique, 0x3a600, 8) INT_ADD (unique, 0x7b80, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x3a600) (BinOp OP_PLUS (Var (V_TEMP 0x7b80)) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (unique, 0x3a600, 8) , (unique, 0x3a580, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x3a600)) (Cast CAST_LOW 64 (Var (V_TEMP 0x3a580))) LittleE 8)
)

(* 0x00100188: ret *)
(*    1048968: ret *)
| 0x100188 => Some (4,
	(* (register, 0x0, 8) COPY (register, 0x40f0, 8) *)
	Move R_PC (Var R_X30) $;
	(*  ---  RETURN (register, 0x0, 8) *)
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx memcpy_lo_memcpy_armv8.
Proof. Picinae_typecheck. Qed.

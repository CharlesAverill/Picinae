(* Automatically generated with pcode2coq
arch: amd64
file: libgmp.so.10.5.0
SHA256: 2d6d19962673262eba388911974a90de5b7ac14d4da32a1c9666264a4e0a71e3
function: __gmpn_copyi
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition libgmp_so_10_5_0___gmpn_copyi_amd64 : program := fun _ a => match a with

(* 0x0015b186: LEA RDI,[RDI + -0x8] *)
(*    1421702: LEA RDI,[RDI + -0x8] *)
| 0x15b186 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0xfffffffffffffff8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xfffffffffffffff8 64)) $;
	(* (register, 0x38, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDI (Var (V_TEMP 0x4780))
)

(* 0x0015b18a: SUB RDX,0x4 *)
(*    1421706: SUB RDX,0x4 *)
| 0x15b18a => Some (4,
	(* (register, 0x200, 1) INT_LESS (register, 0x10, 8) , (const, 0x4, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RDX) (Word 0x4 64))) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x10, 8) , (const, 0x4, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x4 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x4 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x10, 8) INT_SUB (register, 0x10, 8) , (const, 0x4, 8) *)
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x4 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x10, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x10, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x10, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015b18e: JC 0x0015b1bc *)
(*    1421710: JC 0x0015b1bc *)
| 0x15b18e => Some (2,
	(*  ---  CBRANCH (ram, 0x15b1bc, 8) , (register, 0x200, 1) *)
	If (Cast CAST_LOW 1 (Var R_CF)) (
		Jmp (Word 0x15b1bc 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015b190: MOV RAX,qword ptr [RSI] *)
(*    1421712: MOV RAX,qword ptr [RSI] *)
| 0x15b190 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x0, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RAX (Var (V_TEMP 0x11f00))
)

(* 0x0015b193: MOV R9,qword ptr [RSI + 0x8] *)
(*    1421715: MOV R9,qword ptr [RSI + 0x8] *)
| 0x15b193 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x0015b197: LEA RDI,[RDI + 0x20] *)
(*    1421719: LEA RDI,[RDI + 0x20] *)
| 0x15b197 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	(* (register, 0x38, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDI (Var (V_TEMP 0x4780))
)

(* 0x0015b19b: MOV R10,qword ptr [RSI + 0x10] *)
(*    1421723: MOV R10,qword ptr [RSI + 0x10] *)
| 0x15b19b => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x90, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R10 (Var (V_TEMP 0x11f00))
)

(* 0x0015b19f: MOV R11,qword ptr [RSI + 0x18] *)
(*    1421727: MOV R11,qword ptr [RSI + 0x18] *)
| 0x15b19f => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x18, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x18 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x98, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R11 (Var (V_TEMP 0x11f00))
)

(* 0x0015b1a3: LEA RSI,[RSI + 0x20] *)
(*    1421731: LEA RSI,[RSI + 0x20] *)
| 0x15b1a3 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x20, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	(* (register, 0x30, 8) COPY (unique, 0x4780, 8) *)
	Move R_RSI (Var (V_TEMP 0x4780))
)

(* 0x0015b1a7: MOV qword ptr [RDI + -0x18],RAX *)
(*    1421735: MOV qword ptr [RDI + -0x18],RAX *)
| 0x15b1a7 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0xffffffffffffffe8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffffe8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015b1ab: MOV qword ptr [RDI + -0x10],R9 *)
(*    1421739: MOV qword ptr [RDI + -0x10],R9 *)
| 0x15b1ab => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0xfffffffffffffff0, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xfffffffffffffff0 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015b1af: SUB RDX,0x4 *)
(*    1421743: SUB RDX,0x4 *)
| 0x15b1af => Some (4,
	(* (register, 0x200, 1) INT_LESS (register, 0x10, 8) , (const, 0x4, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RDX) (Word 0x4 64))) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x10, 8) , (const, 0x4, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x4 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x4 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x10, 8) INT_SUB (register, 0x10, 8) , (const, 0x4, 8) *)
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x4 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x10, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x10, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x10, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015b1b3: MOV qword ptr [RDI + -0x8],R10 *)
(*    1421747: MOV qword ptr [RDI + -0x8],R10 *)
| 0x15b1b3 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0xfffffffffffffff8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xfffffffffffffff8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x90, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R10) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015b1b7: MOV qword ptr [RDI],R11 *)
(*    1421751: MOV qword ptr [RDI],R11 *)
| 0x15b1b7 => Some (3,
	(* (unique, 0x6a80, 8) COPY (register, 0x98, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R11) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x38, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015b1ba: JNC 0x0015b190 *)
(*    1421754: JNC 0x0015b190 *)
| 0x15b1ba => Some (2,
	(* (unique, 0x12680, 1) BOOL_NEGATE (register, 0x200, 1) *)
	Move (V_TEMP 0x12680) (UnOp OP_NOT (Var R_CF)) $;
	(*  ---  CBRANCH (ram, 0x15b190, 8) , (unique, 0x12680, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12680))) (
		Jmp (Word 0x15b190 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015b1bc: SHR EDX,0x1 *)
(*    1421756: SHR EDX,0x1 *)
| 0x15b1bc => Some (2,
	(* (unique, 0x6db80, 4) INT_AND (register, 0x10, 4) , (const, 0x1, 4) *)
	Move (V_TEMP 0x6db80) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x1 32)) $;
	(* (register, 0x200, 1) INT_NOTEQUAL (unique, 0x6db80, 4) , (const, 0x0, 4) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x6db80)) (Word 0x0 32))) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x10, 4) INT_RIGHT (register, 0x10, 4) , (const, 0x1, 4) *)
	Move R_RDX (Cast CAST_SIGNED 64 (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 0x1 32))) $;
	(* (register, 0x10, 8) INT_ZEXT (register, 0x10, 4) *)
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x10, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x10, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x10, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015b1be: JNC 0x0015b1cf *)
(*    1421758: JNC 0x0015b1cf *)
| 0x15b1be => Some (2,
	(* (unique, 0x12680, 1) BOOL_NEGATE (register, 0x200, 1) *)
	Move (V_TEMP 0x12680) (UnOp OP_NOT (Var R_CF)) $;
	(*  ---  CBRANCH (ram, 0x15b1cf, 8) , (unique, 0x12680, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12680))) (
		Jmp (Word 0x15b1cf 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015b1c0: MOV RAX,qword ptr [RSI] *)
(*    1421760: MOV RAX,qword ptr [RSI] *)
| 0x15b1c0 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x0, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RAX (Var (V_TEMP 0x11f00))
)

(* 0x0015b1c3: MOV qword ptr [RDI + 0x8],RAX *)
(*    1421763: MOV qword ptr [RDI + 0x8],RAX *)
| 0x15b1c3 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015b1c7: LEA RDI,[RDI + 0x8] *)
(*    1421767: LEA RDI,[RDI + 0x8] *)
| 0x15b1c7 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (register, 0x38, 8) COPY (unique, 0x4780, 8) *)
	Move R_RDI (Var (V_TEMP 0x4780))
)

(* 0x0015b1cb: LEA RSI,[RSI + 0x8] *)
(*    1421771: LEA RSI,[RSI + 0x8] *)
| 0x15b1cb => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (register, 0x30, 8) COPY (unique, 0x4780, 8) *)
	Move R_RSI (Var (V_TEMP 0x4780))
)

(* 0x0015b1cf: SHR EDX,0x1 *)
(*    1421775: SHR EDX,0x1 *)
| 0x15b1cf => Some (2,
	(* (unique, 0x6db80, 4) INT_AND (register, 0x10, 4) , (const, 0x1, 4) *)
	Move (V_TEMP 0x6db80) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x1 32)) $;
	(* (register, 0x200, 1) INT_NOTEQUAL (unique, 0x6db80, 4) , (const, 0x0, 4) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x6db80)) (Word 0x0 32))) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x10, 4) INT_RIGHT (register, 0x10, 4) , (const, 0x1, 4) *)
	Move R_RDX (Cast CAST_SIGNED 64 (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 0x1 32))) $;
	(* (register, 0x10, 8) INT_ZEXT (register, 0x10, 4) *)
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x10, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x10, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x10, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015b1d1: JNC 0x0015b1e2 *)
(*    1421777: JNC 0x0015b1e2 *)
| 0x15b1d1 => Some (2,
	(* (unique, 0x12680, 1) BOOL_NEGATE (register, 0x200, 1) *)
	Move (V_TEMP 0x12680) (UnOp OP_NOT (Var R_CF)) $;
	(*  ---  CBRANCH (ram, 0x15b1e2, 8) , (unique, 0x12680, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12680))) (
		Jmp (Word 0x15b1e2 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015b1d3: MOV RAX,qword ptr [RSI] *)
(*    1421779: MOV RAX,qword ptr [RSI] *)
| 0x15b1d3 => Some (3,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x30, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	(* (register, 0x0, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RAX (Var (V_TEMP 0x11f00))
)

(* 0x0015b1d6: MOV R9,qword ptr [RSI + 0x8] *)
(*    1421782: MOV R9,qword ptr [RSI + 0x8] *)
| 0x15b1d6 => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x30, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4780, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	(* (register, 0x88, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R9 (Var (V_TEMP 0x11f00))
)

(* 0x0015b1da: MOV qword ptr [RDI + 0x8],RAX *)
(*    1421786: MOV qword ptr [RDI + 0x8],RAX *)
| 0x15b1da => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x8, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015b1de: MOV qword ptr [RDI + 0x10],R9 *)
(*    1421790: MOV qword ptr [RDI + 0x10],R9 *)
| 0x15b1de => Some (4,
	(* (unique, 0x4780, 8) INT_ADD (register, 0x38, 8) , (const, 0x10, 8) *)
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x88, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R9) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4780, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015b1e2: RET *)
(*    1421794: RET *)
| 0x15b1e2 => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx libgmp_so_10_5_0___gmpn_copyi_amd64.
Proof. Picinae_typecheck. Qed.


(* BEGIN BIGSTEPS GENERATED LEMMAS *)
(* Generated by: bigsteps /home/ixb/research/picinae-llm/Examples/libgmp_so_10_5_0/gmpn_copyi_amd64.v --backend compiler --timeout 600 --invariants 0x15b186 0x15b190 0x15b1bc 0x15b1cf 0x15b1e2 --exits 0x15b1e2 *)
Import X64Notations.

Lemma libgmp_so_10_5_0___gmpn_copyi_amd64_stepfrom_1421702:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b186, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b18a, s[R_RDI := s R_RDI ⊖ 8]) :: l) = None))
    (VC3: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b18e, s[R_RDI := s R_RDI ⊖ 8][R_CF := if s R_RDX <? 4 then 1 else 0][R_OF := (s R_RDX >> 63 .^ s R_RDX ⊖ 4 >> 63) .& (s R_RDX ⊖ 4 >> 63 .^ 1)][R_RDX := s R_RDX ⊖ 4][R_SF := if slt 64 (s R_RDX ⊖ 4) 0 then 1 else 0][R_ZF := if s R_RDX mod 2 ^ 64 =? 4 mod 2 ^ 64 then 1 else 0][R_PF := if popcount (msub 8 (s R_RDX) 4) mod 2 =? 0 then 1 else 0]) :: l) = None))
    (VC4: ((s R_RDX <? 4) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits true ((Addr 0x0015b1bc, s[R_RDI := s R_RDI ⊖ 8][R_CF := 1][R_OF := (s R_RDX >> 63 .^ s R_RDX ⊖ 4 >> 63) .& (s R_RDX ⊖ 4 >> 63 .^ 1)][R_RDX := s R_RDX ⊖ 4][R_SF := if slt 64 (s R_RDX ⊖ 4) 0 then 1 else 0][R_ZF := if s R_RDX mod 2 ^ 64 =? 4 then 1 else 0][R_PF := if popcount (msub 8 (s R_RDX) 4) mod 2 =? 0 then 1 else 0]) :: l)))
    (VC5: ((s R_RDX <? 4) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits true ((Addr 0x0015b190, s[R_RDI := s R_RDI ⊖ 8][R_CF := 0][R_OF := (s R_RDX >> 63 .^ s R_RDX ⊖ 4 >> 63) .& (s R_RDX ⊖ 4 >> 63 .^ 1)][R_RDX := s R_RDX ⊖ 4][R_SF := if slt 64 (s R_RDX ⊖ 4) 0 then 1 else 0][R_ZF := if s R_RDX mod 2 ^ 64 =? 4 then 1 else 0][R_PF := if popcount (msub 8 (s R_RDX) 4) mod 2 =? 0 then 1 else 0]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits false ((Addr 1421702, s)::t).
Proof.
  intros; find_vcs (1421702::1421712::1421756::1421775::1421794::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_copyi_amd64_stepfrom_1421712:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b190, s) :: t) = None))
    (VC2: (MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b193, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC3: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b197, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l) = None))
    (VC4: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b19b, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI]) :: l) = None))
    (VC5: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b19f, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]]) :: l) = None))
    (VC6: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1a3, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]]) :: l) = None))
    (VC7: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1a7, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]][R_RSI := 32 ⊕ s R_RSI]) :: l) = None))
    (VC8: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1ab, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]][R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ]]) :: l) = None))
    (VC9: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1af, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]][R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ] [Ⓠ16 + s R_RDI := s V_MEM64 Ⓠ[ 8 + s R_RSI ] ]]) :: l) = None))
    (VC10: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1b3, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]][R_RSI := 32 ⊕ s R_RSI][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ] [Ⓠ16 + s R_RDI := s V_MEM64 Ⓠ[ 8 + s R_RSI ] ]][R_CF := if s R_RDX <? 4 then 1 else 0][R_OF := (s R_RDX >> 63 .^ s R_RDX ⊖ 4 >> 63) .& (s R_RDX ⊖ 4 >> 63 .^ 1)][R_RDX := s R_RDX ⊖ 4][R_SF := if slt 64 (s R_RDX ⊖ 4) 0 then 1 else 0][R_ZF := if s R_RDX mod 2 ^ 64 =? 4 mod 2 ^ 64 then 1 else 0][R_PF := if popcount (msub 8 (s R_RDX) 4) mod 2 =? 0 then 1 else 0]) :: l) = None))
    (VC11: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1b7, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]][R_RSI := 32 ⊕ s R_RSI][R_CF := if s R_RDX <? 4 then 1 else 0][R_OF := (s R_RDX >> 63 .^ s R_RDX ⊖ 4 >> 63) .& (s R_RDX ⊖ 4 >> 63 .^ 1)][R_RDX := s R_RDX ⊖ 4][R_SF := if slt 64 (s R_RDX ⊖ 4) 0 then 1 else 0][R_ZF := if s R_RDX mod 2 ^ 64 =? 4 then 1 else 0][R_PF := if popcount (msub 8 (s R_RDX) 4) mod 2 =? 0 then 1 else 0][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ] [Ⓠ16 + s R_RDI := s V_MEM64 Ⓠ[ 8 + s R_RSI ] ] [Ⓠ24 + s R_RDI := s V_MEM64 Ⓠ[ 16 + s R_RSI ] ]]) :: l) = None))
    (VC12: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (32 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1ba, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]][R_RSI := 32 ⊕ s R_RSI][R_CF := if s R_RDX <? 4 then 1 else 0][R_OF := (s R_RDX >> 63 .^ s R_RDX ⊖ 4 >> 63) .& (s R_RDX ⊖ 4 >> 63 .^ 1)][R_RDX := s R_RDX ⊖ 4][R_SF := if slt 64 (s R_RDX ⊖ 4) 0 then 1 else 0][R_ZF := if s R_RDX mod 2 ^ 64 =? 4 then 1 else 0][R_PF := if popcount (msub 8 (s R_RDX) 4) mod 2 =? 0 then 1 else 0][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ] [Ⓠ16 + s R_RDI := s V_MEM64 Ⓠ[ 8 + s R_RSI ] ] [Ⓠ24 + s R_RDI := s V_MEM64 Ⓠ[ 16 + s R_RSI ] ] [Ⓠ32 + s R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSI ] ]]) :: l) = None))
    (VC13: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (32 ⊕ s R_RDI) 64 8 -> (s R_RDX <? 4) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits true ((Addr 0x0015b1bc, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]][R_RSI := 32 ⊕ s R_RSI][R_CF := 1][R_OF := (s R_RDX >> 63 .^ s R_RDX ⊖ 4 >> 63) .& (s R_RDX ⊖ 4 >> 63 .^ 1)][R_RDX := s R_RDX ⊖ 4][R_SF := if slt 64 (s R_RDX ⊖ 4) 0 then 1 else 0][R_ZF := if s R_RDX mod 2 ^ 64 =? 4 then 1 else 0][R_PF := if popcount (msub 8 (s R_RDX) 4) mod 2 =? 0 then 1 else 0][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ] [Ⓠ16 + s R_RDI := s V_MEM64 Ⓠ[ 8 + s R_RSI ] ] [Ⓠ24 + s R_RDI := s V_MEM64 Ⓠ[ 16 + s R_RSI ] ] [Ⓠ32 + s R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSI ] ]]) :: l)))
    (VC14: (MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSI) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (32 ⊕ s R_RDI) 64 8 -> (s R_RDX <? 4) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits true ((Addr 0x0015b190, s[R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][R_RDI := 32 ⊕ s R_RDI][R_R10 := s V_MEM64 Ⓠ[ 16 + s R_RSI ]][R_R11 := s V_MEM64 Ⓠ[ 24 + s R_RSI ]][R_RSI := 32 ⊕ s R_RSI][R_CF := 0][R_OF := (s R_RDX >> 63 .^ s R_RDX ⊖ 4 >> 63) .& (s R_RDX ⊖ 4 >> 63 .^ 1)][R_RDX := s R_RDX ⊖ 4][R_SF := if slt 64 (s R_RDX ⊖ 4) 0 then 1 else 0][R_ZF := if s R_RDX mod 2 ^ 64 =? 4 then 1 else 0][R_PF := if popcount (msub 8 (s R_RDX) 4) mod 2 =? 0 then 1 else 0][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ] [Ⓠ16 + s R_RDI := s V_MEM64 Ⓠ[ 8 + s R_RSI ] ] [Ⓠ24 + s R_RDI := s V_MEM64 Ⓠ[ 16 + s R_RSI ] ] [Ⓠ32 + s R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSI ] ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits false ((Addr 1421712, s)::t).
Proof.
  intros; find_vcs (1421702::1421712::1421756::1421775::1421794::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
  1: solve [eapply VC8; first [eassumption | reflexivity]].
  1: solve [eapply VC9; first [eassumption | reflexivity]].
  1: solve [eapply VC10; first [eassumption | reflexivity]].
  1: solve [eapply VC11; first [eassumption | reflexivity]].
  1: solve [eapply VC12; first [eassumption | reflexivity]].
  1: solve [eapply VC13; first [eassumption | reflexivity]].
  1: solve [eapply VC14; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_copyi_amd64_stepfrom_1421756:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1bc, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1be, s[R_CF := if negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) then 1 else 0][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0]) :: l) = None))
    (VC3: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1c0, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0]) :: l) = None))
    (VC4: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1c3, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0][R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC5: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1c7, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0][R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ]]) :: l) = None))
    (VC6: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1cb, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0][R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ]][R_RDI := 8 ⊕ s R_RDI]) :: l) = None))
    (VC7: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits true ((Addr 0x0015b1cf, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0][R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ]][R_RDI := 8 ⊕ s R_RDI][R_RSI := 8 ⊕ s R_RSI]) :: l)))
    (VC8: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits true ((Addr 0x0015b1cf, s[R_CF := 0][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits false ((Addr 1421756, s)::t).
Proof.
  intros; find_vcs (1421702::1421712::1421756::1421775::1421794::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
  1: solve [eapply VC8; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_copyi_amd64_stepfrom_1421775:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1cf, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1d1, s[R_CF := if negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) then 1 else 0][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0]) :: l) = None))
    (VC3: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1d3, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0]) :: l) = None))
    (VC4: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> MemAcc mem_readable s (s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1d6, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0][R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]]) :: l) = None))
    (VC5: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1da, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0][R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]]) :: l) = None))
    (VC6: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits ((Addr 0x0015b1de, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0][R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ]]) :: l) = None))
    (VC7: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = true -> MemAcc mem_readable s (s R_RSI) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSI) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RDI) 64 8 -> MemAcc mem_writable s (16 ⊕ s R_RDI) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits true ((Addr 0x0015b1e2, s[R_CF := 1][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0][R_RAX := s V_MEM64 Ⓠ[ s R_RSI ]][R_R9 := s V_MEM64 Ⓠ[ 8 + s R_RSI ]][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RDI := s V_MEM64 Ⓠ[ s R_RSI ] ] [Ⓠ16 + s R_RDI := s V_MEM64 Ⓠ[ 8 + s R_RSI ] ]]) :: l)))
    (VC8: (negb ((s R_RDX >> 0) mod 2 ^ 32 .& 1 =? 0) = false -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits true ((Addr 0x0015b1e2, s[R_CF := 0][R_OF := 0][R_RDX := scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := if popcount (scast 32 64 ((s R_RDX >> 0) mod 2 ^ 32 >> 1) mod 2 ^ 8) mod 2 =? 0 then 1 else 0]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 invs exits false ((Addr 1421775, s)::t).
Proof.
  intros; find_vcs (1421702::1421712::1421756::1421775::1421794::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
  1: solve [eapply VC8; first [eassumption | reflexivity]].
Qed.

Ltac libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep := first [ apply libgmp_so_10_5_0___gmpn_copyi_amd64_stepfrom_1421702 | apply libgmp_so_10_5_0___gmpn_copyi_amd64_stepfrom_1421712 | apply libgmp_so_10_5_0___gmpn_copyi_amd64_stepfrom_1421756 | apply libgmp_so_10_5_0___gmpn_copyi_amd64_stepfrom_1421775 ]; intros; (reflexivity || ISA_invhere).
(* END BIGSTEPS GENERATED LEMMAS *)
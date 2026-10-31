(* Automatically generated with pcode2coq
arch: amd64
file: libgmp.so.10.5.0
SHA256: 2d6d19962673262eba388911974a90de5b7ac14d4da32a1c9666264a4e0a71e3
function: __gmpn_add_n_sub_n
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 : program := fun _ a => match a with

(* 0x0015c360: PUSH R15 *)
(*    1426272: PUSH R15 *)
| 0x15c360 => Some (2,
	(* (unique, 0x27c80, 8) COPY (register, 0xb8, 8) *)
	Move (V_TEMP 0x27c80) (Var R_R15) $;
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (unique, 0x27c80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x0015c362: PUSH R14 *)
(*    1426274: PUSH R14 *)
| 0x15c362 => Some (2,
	(* (unique, 0x27c80, 8) COPY (register, 0xb0, 8) *)
	Move (V_TEMP 0x27c80) (Var R_R14) $;
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (unique, 0x27c80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x0015c364: MOV R14,RSI *)
(*    1426276: MOV R14,RSI *)
| 0x15c364 => Some (3,
	(* (register, 0xb0, 8) COPY (register, 0x30, 8) *)
	Move R_R14 (Var R_RSI)
)

(* 0x0015c367: PUSH R13 *)
(*    1426279: PUSH R13 *)
| 0x15c367 => Some (2,
	(* (unique, 0x27c80, 8) COPY (register, 0xa8, 8) *)
	Move (V_TEMP 0x27c80) (Var R_R13) $;
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (unique, 0x27c80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x0015c369: MOV R13,RDI *)
(*    1426281: MOV R13,RDI *)
| 0x15c369 => Some (3,
	(* (register, 0xa8, 8) COPY (register, 0x38, 8) *)
	Move R_R13 (Var R_RDI)
)

(* 0x0015c36c: PUSH R12 *)
(*    1426284: PUSH R12 *)
| 0x15c36c => Some (2,
	(* (unique, 0x27c80, 8) COPY (register, 0xa0, 8) *)
	Move (V_TEMP 0x27c80) (Var R_R12) $;
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (unique, 0x27c80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x0015c36e: MOV R12,R8 *)
(*    1426286: MOV R12,R8 *)
| 0x15c36e => Some (3,
	(* (register, 0xa0, 8) COPY (register, 0x80, 8) *)
	Move R_R12 (Var R_R8)
)

(* 0x0015c371: PUSH RBP *)
(*    1426289: PUSH RBP *)
| 0x15c371 => Some (1,
	(* (unique, 0x27c80, 8) COPY (register, 0x28, 8) *)
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (unique, 0x27c80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x0015c372: MOV RBP,RCX *)
(*    1426290: MOV RBP,RCX *)
| 0x15c372 => Some (3,
	(* (register, 0x28, 8) COPY (register, 0x8, 8) *)
	Move R_RBP (Var R_RCX)
)

(* 0x0015c375: PUSH RBX *)
(*    1426293: PUSH RBX *)
| 0x15c375 => Some (1,
	(* (unique, 0x27c80, 8) COPY (register, 0x18, 8) *)
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (unique, 0x27c80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x0015c376: MOV RBX,RDX *)
(*    1426294: MOV RBX,RDX *)
| 0x15c376 => Some (3,
	(* (register, 0x18, 8) COPY (register, 0x10, 8) *)
	Move R_RBX (Var R_RDX)
)

(* 0x0015c379: SUB RSP,0x578 *)
(*    1426297: SUB RSP,0x578 *)
| 0x15c379 => Some (7,
	(* (register, 0x200, 1) INT_LESS (register, 0x20, 8) , (const, 0x578, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RSP) (Word 0x578 64))) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x20, 8) , (const, 0x578, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x578 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x578 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x578 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x578, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x578 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x20, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x20, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x20, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c380: CMP RDI,RDX *)
(*    1426304: CMP RDI,RDX *)
| 0x15c380 => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0x38, 8) *)
	Move (V_TEMP 0x3f000) (Var R_RDI) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0x10, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RDX))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0x10, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0x10, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RDX)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c383: JZ 0x0015c448 *)
(*    1426307: JZ 0x0015c448 *)
| 0x15c383 => Some (6,
	(*  ---  CBRANCH (ram, 0x15c448, 8) , (register, 0x206, 1) *)
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x15c448 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c389: CMP RDI,RCX *)
(*    1426313: CMP RDI,RCX *)
| 0x15c389 => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0x38, 8) *)
	Move (V_TEMP 0x3f000) (Var R_RDI) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0x8, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RCX))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0x8, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0x8, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c38c: JZ 0x0015c448 *)
(*    1426316: JZ 0x0015c448 *)
| 0x15c38c => Some (6,
	(*  ---  CBRANCH (ram, 0x15c448, 8) , (register, 0x206, 1) *)
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x15c448 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c392: TEST R8,R8 *)
(*    1426322: TEST R8,R8 *)
| 0x15c392 => Some (3,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (unique, 0x70280, 8) INT_AND (register, 0x80, 8) , (register, 0x80, 8) *)
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_R8) (Var R_R8)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x70280, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x70280, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x70280, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c395: JLE 0x0015c5e0 *)
(*    1426325: JLE 0x0015c5e0 *)
| 0x15c395 => Some (6,
	(* (unique, 0x12e80, 1) INT_NOTEQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x12e80) (BinOp OP_NEQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x12f80, 1) BOOL_OR (register, 0x206, 1) , (unique, 0x12e80, 1) *)
	Move (V_TEMP 0x12f80) (BinOp OP_OR (Var R_ZF) (Var (V_TEMP 0x12e80))) $;
	(*  ---  CBRANCH (ram, 0x15c5e0, 8) , (unique, 0x12f80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12f80))) (
		Jmp (Word 0x15c5e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c39b: MOV R15,RSI *)
(*    1426331: MOV R15,RSI *)
| 0x15c39b => Some (3,
	(* (register, 0xb8, 8) COPY (register, 0x30, 8) *)
	Move R_R15 (Var R_RSI)
)

(* 0x0015c39e: XOR R14D,R14D *)
(*    1426334: XOR R14D,R14D *)
| 0x15c39e => Some (3,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0xb0, 4) INT_XOR (register, 0xb0, 4) , (register, 0xb0, 4) *)
	Move R_R14 (Cast CAST_SIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_R14)) (Extract 31 0 (Var R_R14)))) $;
	(* (register, 0xb0, 8) INT_ZEXT (register, 0xb0, 4) *)
	Move R_R14 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R14))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xb0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_R14)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xb0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_R14)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0xb0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_R14)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c3a1: MOV qword ptr [RSP + 0x8],0x0 *)
(*    1426337: MOV qword ptr [RSP + 0x8],0x0 *)
| 0x15c3a1 => Some (9,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Word 0x0 64) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c3aa: MOV qword ptr [RSP],0x0 *)
(*    1426346: MOV qword ptr [RSP],0x0 *)
| 0x15c3aa => Some (8,
	(* (unique, 0x6a80, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Word 0x0 64) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x20, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c3b2: NOP word ptr [RAX + RAX*0x1] *)
(*    1426354: NOP word ptr [RAX + RAX*0x1] *)
| 0x15c3b2 => Some (6,
	(* (unique, 0x5100, 8) INT_MULT (register, 0x0, 8) , (const, 0x1, 8) *)
	Move (V_TEMP 0x5100) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	(* (unique, 0x5200, 8) INT_ADD (register, 0x0, 8) , (unique, 0x5100, 8) *)
	Move (V_TEMP 0x5200) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5100)))
)

(* 0x0015c3b8: MOV RCX,R12 *)
(*    1426360: MOV RCX,R12 *)
| 0x15c3b8 => Some (3,
	(* (register, 0x8, 8) COPY (register, 0xa0, 8) *)
	Move R_RCX (Var R_R12)
)

(* 0x0015c3bb: MOV EAX,0xaa *)
(*    1426363: MOV EAX,0xaa *)
| 0x15c3bb => Some (5,
	(* (register, 0x0, 8) COPY (const, 0xaa, 8) *)
	Move R_RAX (Word 0xaa 64)
)

(* 0x0015c3c0: MOV R8,qword ptr [RSP] *)
(*    1426368: MOV R8,qword ptr [RSP] *)
| 0x15c3c0 => Some (4,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x20, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0015c3c4: SUB RCX,R14 *)
(*    1426372: SUB RCX,R14 *)
| 0x15c3c4 => Some (3,
	(* (register, 0x200, 1) INT_LESS (register, 0x8, 8) , (register, 0xb0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RCX) (Var R_R14))) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x8, 8) , (register, 0xb0, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_R14)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_R14)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x8, 8) INT_SUB (register, 0x8, 8) , (register, 0xb0, 8) *)
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_R14)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c3c7: MOV RDX,RBP *)
(*    1426375: MOV RDX,RBP *)
| 0x15c3c7 => Some (3,
	(* (register, 0x10, 8) COPY (register, 0x28, 8) *)
	Move R_RDX (Var R_RBP)
)

(* 0x0015c3ca: MOV RSI,RBX *)
(*    1426378: MOV RSI,RBX *)
| 0x15c3ca => Some (3,
	(* (register, 0x30, 8) COPY (register, 0x18, 8) *)
	Move R_RSI (Var R_RBX)
)

(* 0x0015c3cd: CMP RCX,RAX *)
(*    1426381: CMP RCX,RAX *)
| 0x15c3cd => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0x8, 8) *)
	Move (V_TEMP 0x3f000) (Var R_RCX) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RAX))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c3d0: MOV RDI,R13 *)
(*    1426384: MOV RDI,R13 *)
| 0x15c3d0 => Some (3,
	(* (register, 0x38, 8) COPY (register, 0xa8, 8) *)
	Move R_RDI (Var R_R13)
)

(* 0x0015c3d3: CMOVG RCX,RAX *)
(*    1426387: CMOVG RCX,RAX *)
| 0x15c3d3 => Some (4,
	(* (unique, 0x13000, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x13000) (UnOp OP_NOT (Var R_ZF)) $;
	(* (unique, 0x13080, 1) INT_EQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x13080) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x13180, 1) BOOL_AND (unique, 0x13000, 1) , (unique, 0x13080, 1) *)
	Move (V_TEMP 0x13180) (BinOp OP_AND (Var (V_TEMP 0x13000)) (Var (V_TEMP 0x13080))) $;
	(* (unique, 0x3dc00, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x3dc00) (Var R_RAX) $;
	(* (unique, 0x3dc80, 1) BOOL_NEGATE (unique, 0x13180, 1) *)
	Move (V_TEMP 0x3dc80) (UnOp OP_NOT (Var (V_TEMP 0x13180))) $;
	(*  ---  CBRANCH (ram, 0x15c3d7, 8) , (unique, 0x3dc80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dc80))) (
		Jmp (Word 0x15c3d7 64)
	) (* else *) (
		Nop
	) $;
	(* (register, 0x8, 8) COPY (unique, 0x3dc00, 8) *)
	Move R_RCX (Var (V_TEMP 0x3dc00))
)

(* 0x0015c3d7: ADD R14,0xaa *)
(*    1426391: ADD R14,0xaa *)
| 0x15c3d7 => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0xb0, 8) , (const, 0xaa, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R14) (Word 0xaa 64)) (Var R_R14))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0xb0, 8) , (const, 0xaa, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R14) (Word 0xaa 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xaa 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xb0, 8) INT_ADD (register, 0xb0, 8) , (const, 0xaa, 8) *)
	Move R_R14 (BinOp OP_PLUS (Var R_R14) (Word 0xaa 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xb0, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R14) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xb0, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R14) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xb0, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R14) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c3de: ADD R13,0x550 *)
(*    1426398: ADD R13,0x550 *)
| 0x15c3de => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0xa8, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R13) (Word 0x550 64)) (Var R_R13))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0xa8, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R13) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xa8, 8) INT_ADD (register, 0xa8, 8) , (const, 0x550, 8) *)
	Move R_R13 (BinOp OP_PLUS (Var R_R13) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xa8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R13) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xa8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R13) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xa8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R13) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c3e5: MOV qword ptr [RSP + 0x10],RCX *)
(*    1426405: MOV qword ptr [RSP + 0x10],RCX *)
| 0x15c3e5 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x10, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x10 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x8, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RCX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c3ea: CALL 0x0010c030 *)
(*    1426410: CALL 0x0010c030 *)
| 0x15c3ea => Some (5,
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (const, 0x15c3ef, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x15c3ef 64)) LittleE 8) $;
	(*  ---  CALL (ram, 0x10c030, 8) *)
	Jmp (Word 0x10c030 64)
)

(* 0x0015c3ef: MOV R8,qword ptr [RSP + 0x8] *)
(*    1426415: MOV R8,qword ptr [RSP + 0x8] *)
| 0x15c3ef => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0015c3f4: MOV RCX,qword ptr [RSP + 0x10] *)
(*    1426420: MOV RCX,qword ptr [RSP + 0x10] *)
| 0x15c3f4 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x10, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x10 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x8, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RCX (Var (V_TEMP 0x11f00))
)

(* 0x0015c3f9: MOV RDX,RBP *)
(*    1426425: MOV RDX,RBP *)
| 0x15c3f9 => Some (3,
	(* (register, 0x10, 8) COPY (register, 0x28, 8) *)
	Move R_RDX (Var R_RBP)
)

(* 0x0015c3fc: MOV RSI,RBX *)
(*    1426428: MOV RSI,RBX *)
| 0x15c3fc => Some (3,
	(* (register, 0x30, 8) COPY (register, 0x18, 8) *)
	Move R_RSI (Var R_RBX)
)

(* 0x0015c3ff: MOV RDI,R15 *)
(*    1426431: MOV RDI,R15 *)
| 0x15c3ff => Some (3,
	(* (register, 0x38, 8) COPY (register, 0xb8, 8) *)
	Move R_RDI (Var R_R15)
)

(* 0x0015c402: MOV qword ptr [RSP],RAX *)
(*    1426434: MOV qword ptr [RSP],RAX *)
| 0x15c402 => Some (4,
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x20, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c406: ADD RBX,0x550 *)
(*    1426438: ADD RBX,0x550 *)
| 0x15c406 => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) (Var R_RBX))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x18, 8) INT_ADD (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_RBX (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x18, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x18, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x18, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c40d: ADD RBP,0x550 *)
(*    1426445: ADD RBP,0x550 *)
| 0x15c40d => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) (Var R_RBP))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x28, 8) INT_ADD (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_RBP (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x28, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBP) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x28, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBP) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x28, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBP) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c414: ADD R15,0x550 *)
(*    1426452: ADD R15,0x550 *)
| 0x15c414 => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0xb8, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R15) (Word 0x550 64)) (Var R_R15))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0xb8, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R15) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R15) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R15) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xb8, 8) INT_ADD (register, 0xb8, 8) , (const, 0x550, 8) *)
	Move R_R15 (BinOp OP_PLUS (Var R_R15) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xb8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R15) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xb8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R15) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xb8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R15) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c41b: CALL 0x0010b8f0 *)
(*    1426459: CALL 0x0010b8f0 *)
| 0x15c41b => Some (5,
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (const, 0x15c420, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x15c420 64)) LittleE 8) $;
	(*  ---  CALL (ram, 0x10b8f0, 8) *)
	Jmp (Word 0x10b8f0 64)
)

(* 0x0015c420: CMP R12,R14 *)
(*    1426464: CMP R12,R14 *)
| 0x15c420 => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0xa0, 8) *)
	Move (V_TEMP 0x3f000) (Var R_R12) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_R14))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c423: MOV qword ptr [RSP + 0x8],RAX *)
(*    1426467: MOV qword ptr [RSP + 0x8],RAX *)
| 0x15c423 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c428: JG 0x0015c3b8 *)
(*    1426472: JG 0x0015c3b8 *)
| 0x15c428 => Some (2,
	(* (unique, 0x13000, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x13000) (UnOp OP_NOT (Var R_ZF)) $;
	(* (unique, 0x13080, 1) INT_EQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x13080) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x13180, 1) BOOL_AND (unique, 0x13000, 1) , (unique, 0x13080, 1) *)
	Move (V_TEMP 0x13180) (BinOp OP_AND (Var (V_TEMP 0x13000)) (Var (V_TEMP 0x13080))) $;
	(*  ---  CBRANCH (ram, 0x15c3b8, 8) , (unique, 0x13180, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13180))) (
		Jmp (Word 0x15c3b8 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c42a: MOV RDX,qword ptr [RSP] *)
(*    1426474: MOV RDX,qword ptr [RSP] *)
| 0x15c42a => Some (4,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x20, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x10, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RDX (Var (V_TEMP 0x11f00))
)

(* 0x0015c42e: LEA RAX,[RAX + RDX*0x2] *)
(*    1426478: LEA RAX,[RAX + RDX*0x2] *)
| 0x15c42e => Some (4,
	(* (unique, 0x4980, 8) INT_MULT (register, 0x10, 8) , (const, 0x2, 8) *)
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDX) (Word 0x2 64)) $;
	(* (unique, 0x4a80, 8) INT_ADD (register, 0x0, 8) , (unique, 0x4980, 8) *)
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4980))) $;
	(* (register, 0x0, 8) COPY (unique, 0x4a80, 8) *)
	Move R_RAX (Var (V_TEMP 0x4a80))
)

(* 0x0015c432: ADD RSP,0x578 *)
(*    1426482: ADD RSP,0x578 *)
| 0x15c432 => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0x20, 8) , (const, 0x578, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x578 64)) (Var R_RSP))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x20, 8) , (const, 0x578, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x578 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x578 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x578, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x578 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x20, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x20, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x20, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c439: POP RBX *)
(*    1426489: POP RBX *)
| 0x15c439 => Some (1,
	(* (unique, 0x55200, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	(* (unique, 0x55200, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(* (register, 0x18, 8) COPY (unique, 0x55200, 8) *)
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x0015c43a: POP RBP *)
(*    1426490: POP RBP *)
| 0x15c43a => Some (1,
	(* (unique, 0x55200, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	(* (unique, 0x55200, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(* (register, 0x28, 8) COPY (unique, 0x55200, 8) *)
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x0015c43b: POP R12 *)
(*    1426491: POP R12 *)
| 0x15c43b => Some (2,
	(* (unique, 0x55200, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	(* (unique, 0x55200, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(* (register, 0xa0, 8) COPY (unique, 0x55200, 8) *)
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x0015c43d: POP R13 *)
(*    1426493: POP R13 *)
| 0x15c43d => Some (2,
	(* (unique, 0x55200, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	(* (unique, 0x55200, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(* (register, 0xa8, 8) COPY (unique, 0x55200, 8) *)
	Move R_R13 (Var (V_TEMP 0x55200))
)

(* 0x0015c43f: POP R14 *)
(*    1426495: POP R14 *)
| 0x15c43f => Some (2,
	(* (unique, 0x55200, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	(* (unique, 0x55200, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(* (register, 0xb0, 8) COPY (unique, 0x55200, 8) *)
	Move R_R14 (Var (V_TEMP 0x55200))
)

(* 0x0015c441: POP R15 *)
(*    1426497: POP R15 *)
| 0x15c441 => Some (2,
	(* (unique, 0x55200, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	(* (unique, 0x55200, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(* (register, 0xb8, 8) COPY (unique, 0x55200, 8) *)
	Move R_R15 (Var (V_TEMP 0x55200))
)

(* 0x0015c443: RET *)
(*    1426499: RET *)
| 0x15c443 => Some (1,
	(* (register, 0x288, 8) LOAD (const, 0x1b1, 8) , (register, 0x20, 8) *)
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x20, 8) INT_ADD (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  RETURN (register, 0x288, 8) *)
	Jmp (Var R_RIP)
)

(* 0x0015c448: CMP RBX,R14 *)
(*    1426504: CMP RBX,R14 *)
| 0x15c448 => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0x18, 8) *)
	Move (V_TEMP 0x3f000) (Var R_RBX) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_R14))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c44b: JZ 0x0015c508 *)
(*    1426507: JZ 0x0015c508 *)
| 0x15c44b => Some (6,
	(*  ---  CBRANCH (ram, 0x15c508, 8) , (register, 0x206, 1) *)
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x15c508 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c451: CMP RBP,R14 *)
(*    1426513: CMP RBP,R14 *)
| 0x15c451 => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0x28, 8) *)
	Move (V_TEMP 0x3f000) (Var R_RBP) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_R14))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0xb0, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R14)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c454: JZ 0x0015c508 *)
(*    1426516: JZ 0x0015c508 *)
| 0x15c454 => Some (6,
	(*  ---  CBRANCH (ram, 0x15c508, 8) , (register, 0x206, 1) *)
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x15c508 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c45a: TEST R12,R12 *)
(*    1426522: TEST R12,R12 *)
| 0x15c45a => Some (3,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (unique, 0x70280, 8) INT_AND (register, 0xa0, 8) , (register, 0xa0, 8) *)
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_R12) (Var R_R12)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x70280, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x70280, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x70280, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c45d: JLE 0x0015c5e0 *)
(*    1426525: JLE 0x0015c5e0 *)
| 0x15c45d => Some (6,
	(* (unique, 0x12e80, 1) INT_NOTEQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x12e80) (BinOp OP_NEQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x12f80, 1) BOOL_OR (register, 0x206, 1) , (unique, 0x12e80, 1) *)
	Move (V_TEMP 0x12f80) (BinOp OP_OR (Var R_ZF) (Var (V_TEMP 0x12e80))) $;
	(*  ---  CBRANCH (ram, 0x15c5e0, 8) , (unique, 0x12f80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12f80))) (
		Jmp (Word 0x15c5e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c463: MOV R15,R13 *)
(*    1426531: MOV R15,R13 *)
| 0x15c463 => Some (3,
	(* (register, 0xb8, 8) COPY (register, 0xa8, 8) *)
	Move R_R15 (Var R_R13)
)

(* 0x0015c466: MOV qword ptr [RSP],0x0 *)
(*    1426534: MOV qword ptr [RSP],0x0 *)
| 0x15c466 => Some (8,
	(* (unique, 0x6a80, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Word 0x0 64) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x20, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c46e: XOR R13D,R13D *)
(*    1426542: XOR R13D,R13D *)
| 0x15c46e => Some (3,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0xa8, 4) INT_XOR (register, 0xa8, 4) , (register, 0xa8, 4) *)
	Move R_R13 (Cast CAST_SIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_R13)) (Extract 31 0 (Var R_R13)))) $;
	(* (register, 0xa8, 8) INT_ZEXT (register, 0xa8, 4) *)
	Move R_R13 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R13))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xa8, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_R13)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xa8, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_R13)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0xa8, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_R13)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c471: MOV qword ptr [RSP + 0x8],0x0 *)
(*    1426545: MOV qword ptr [RSP + 0x8],0x0 *)
| 0x15c471 => Some (9,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Word 0x0 64) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c47a: NOP word ptr [RAX + RAX*0x1] *)
(*    1426554: NOP word ptr [RAX + RAX*0x1] *)
| 0x15c47a => Some (6,
	(* (unique, 0x5100, 8) INT_MULT (register, 0x0, 8) , (const, 0x1, 8) *)
	Move (V_TEMP 0x5100) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	(* (unique, 0x5200, 8) INT_ADD (register, 0x0, 8) , (unique, 0x5100, 8) *)
	Move (V_TEMP 0x5200) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5100)))
)

(* 0x0015c480: MOV RCX,R12 *)
(*    1426560: MOV RCX,R12 *)
| 0x15c480 => Some (3,
	(* (register, 0x8, 8) COPY (register, 0xa0, 8) *)
	Move R_RCX (Var R_R12)
)

(* 0x0015c483: MOV EAX,0xaa *)
(*    1426563: MOV EAX,0xaa *)
| 0x15c483 => Some (5,
	(* (register, 0x0, 8) COPY (const, 0xaa, 8) *)
	Move R_RAX (Word 0xaa 64)
)

(* 0x0015c488: MOV R8,qword ptr [RSP] *)
(*    1426568: MOV R8,qword ptr [RSP] *)
| 0x15c488 => Some (4,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x20, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0015c48c: SUB RCX,R13 *)
(*    1426572: SUB RCX,R13 *)
| 0x15c48c => Some (3,
	(* (register, 0x200, 1) INT_LESS (register, 0x8, 8) , (register, 0xa8, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RCX) (Var R_R13))) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0x8, 8) , (register, 0xa8, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_R13)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_R13)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x8, 8) INT_SUB (register, 0x8, 8) , (register, 0xa8, 8) *)
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_R13)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c48f: MOV RDX,RBP *)
(*    1426575: MOV RDX,RBP *)
| 0x15c48f => Some (3,
	(* (register, 0x10, 8) COPY (register, 0x28, 8) *)
	Move R_RDX (Var R_RBP)
)

(* 0x0015c492: MOV RSI,RBX *)
(*    1426578: MOV RSI,RBX *)
| 0x15c492 => Some (3,
	(* (register, 0x30, 8) COPY (register, 0x18, 8) *)
	Move R_RSI (Var R_RBX)
)

(* 0x0015c495: CMP RCX,RAX *)
(*    1426581: CMP RCX,RAX *)
| 0x15c495 => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0x8, 8) *)
	Move (V_TEMP 0x3f000) (Var R_RCX) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RAX))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c498: MOV RDI,R14 *)
(*    1426584: MOV RDI,R14 *)
| 0x15c498 => Some (3,
	(* (register, 0x38, 8) COPY (register, 0xb0, 8) *)
	Move R_RDI (Var R_R14)
)

(* 0x0015c49b: CMOVG RCX,RAX *)
(*    1426587: CMOVG RCX,RAX *)
| 0x15c49b => Some (4,
	(* (unique, 0x13000, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x13000) (UnOp OP_NOT (Var R_ZF)) $;
	(* (unique, 0x13080, 1) INT_EQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x13080) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x13180, 1) BOOL_AND (unique, 0x13000, 1) , (unique, 0x13080, 1) *)
	Move (V_TEMP 0x13180) (BinOp OP_AND (Var (V_TEMP 0x13000)) (Var (V_TEMP 0x13080))) $;
	(* (unique, 0x3dc00, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x3dc00) (Var R_RAX) $;
	(* (unique, 0x3dc80, 1) BOOL_NEGATE (unique, 0x13180, 1) *)
	Move (V_TEMP 0x3dc80) (UnOp OP_NOT (Var (V_TEMP 0x13180))) $;
	(*  ---  CBRANCH (ram, 0x15c49f, 8) , (unique, 0x3dc80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dc80))) (
		Jmp (Word 0x15c49f 64)
	) (* else *) (
		Nop
	) $;
	(* (register, 0x8, 8) COPY (unique, 0x3dc00, 8) *)
	Move R_RCX (Var (V_TEMP 0x3dc00))
)

(* 0x0015c49f: ADD R13,0xaa *)
(*    1426591: ADD R13,0xaa *)
| 0x15c49f => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0xa8, 8) , (const, 0xaa, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R13) (Word 0xaa 64)) (Var R_R13))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0xa8, 8) , (const, 0xaa, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R13) (Word 0xaa 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xaa 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xa8, 8) INT_ADD (register, 0xa8, 8) , (const, 0xaa, 8) *)
	Move R_R13 (BinOp OP_PLUS (Var R_R13) (Word 0xaa 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xa8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R13) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xa8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R13) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xa8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R13) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c4a6: ADD R14,0x550 *)
(*    1426598: ADD R14,0x550 *)
| 0x15c4a6 => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0xb0, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R14) (Word 0x550 64)) (Var R_R14))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0xb0, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R14) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xb0, 8) INT_ADD (register, 0xb0, 8) , (const, 0x550, 8) *)
	Move R_R14 (BinOp OP_PLUS (Var R_R14) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xb0, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R14) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xb0, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R14) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xb0, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R14) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c4ad: MOV qword ptr [RSP + 0x10],RCX *)
(*    1426605: MOV qword ptr [RSP + 0x10],RCX *)
| 0x15c4ad => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x10, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x10 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x8, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RCX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c4b2: CALL 0x0010b8f0 *)
(*    1426610: CALL 0x0010b8f0 *)
| 0x15c4b2 => Some (5,
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (const, 0x15c4b7, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x15c4b7 64)) LittleE 8) $;
	(*  ---  CALL (ram, 0x10b8f0, 8) *)
	Jmp (Word 0x10b8f0 64)
)

(* 0x0015c4b7: MOV R8,qword ptr [RSP + 0x8] *)
(*    1426615: MOV R8,qword ptr [RSP + 0x8] *)
| 0x15c4b7 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0015c4bc: MOV RCX,qword ptr [RSP + 0x10] *)
(*    1426620: MOV RCX,qword ptr [RSP + 0x10] *)
| 0x15c4bc => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x10, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x10 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x8, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RCX (Var (V_TEMP 0x11f00))
)

(* 0x0015c4c1: MOV RDX,RBP *)
(*    1426625: MOV RDX,RBP *)
| 0x15c4c1 => Some (3,
	(* (register, 0x10, 8) COPY (register, 0x28, 8) *)
	Move R_RDX (Var R_RBP)
)

(* 0x0015c4c4: MOV RSI,RBX *)
(*    1426628: MOV RSI,RBX *)
| 0x15c4c4 => Some (3,
	(* (register, 0x30, 8) COPY (register, 0x18, 8) *)
	Move R_RSI (Var R_RBX)
)

(* 0x0015c4c7: MOV RDI,R15 *)
(*    1426631: MOV RDI,R15 *)
| 0x15c4c7 => Some (3,
	(* (register, 0x38, 8) COPY (register, 0xb8, 8) *)
	Move R_RDI (Var R_R15)
)

(* 0x0015c4ca: MOV qword ptr [RSP],RAX *)
(*    1426634: MOV qword ptr [RSP],RAX *)
| 0x15c4ca => Some (4,
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x20, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c4ce: ADD RBX,0x550 *)
(*    1426638: ADD RBX,0x550 *)
| 0x15c4ce => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) (Var R_RBX))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x18, 8) INT_ADD (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_RBX (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x18, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x18, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x18, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c4d5: ADD RBP,0x550 *)
(*    1426645: ADD RBP,0x550 *)
| 0x15c4d5 => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) (Var R_RBP))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x28, 8) INT_ADD (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_RBP (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x28, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBP) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x28, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBP) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x28, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBP) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c4dc: ADD R15,0x550 *)
(*    1426652: ADD R15,0x550 *)
| 0x15c4dc => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0xb8, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R15) (Word 0x550 64)) (Var R_R15))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0xb8, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R15) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R15) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R15) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xb8, 8) INT_ADD (register, 0xb8, 8) , (const, 0x550, 8) *)
	Move R_R15 (BinOp OP_PLUS (Var R_R15) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xb8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R15) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xb8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R15) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xb8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R15) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c4e3: CALL 0x0010c030 *)
(*    1426659: CALL 0x0010c030 *)
| 0x15c4e3 => Some (5,
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (const, 0x15c4e8, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x15c4e8 64)) LittleE 8) $;
	(*  ---  CALL (ram, 0x10c030, 8) *)
	Jmp (Word 0x10c030 64)
)

(* 0x0015c4e8: CMP R12,R13 *)
(*    1426664: CMP R12,R13 *)
| 0x15c4e8 => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0xa0, 8) *)
	Move (V_TEMP 0x3f000) (Var R_R12) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0xa8, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_R13))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0xa8, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R13)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R13)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0xa8, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R13)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c4eb: MOV qword ptr [RSP + 0x8],RAX *)
(*    1426667: MOV qword ptr [RSP + 0x8],RAX *)
| 0x15c4eb => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c4f0: JG 0x0015c480 *)
(*    1426672: JG 0x0015c480 *)
| 0x15c4f0 => Some (2,
	(* (unique, 0x13000, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x13000) (UnOp OP_NOT (Var R_ZF)) $;
	(* (unique, 0x13080, 1) INT_EQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x13080) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x13180, 1) BOOL_AND (unique, 0x13000, 1) , (unique, 0x13080, 1) *)
	Move (V_TEMP 0x13180) (BinOp OP_AND (Var (V_TEMP 0x13000)) (Var (V_TEMP 0x13080))) $;
	(*  ---  CBRANCH (ram, 0x15c480, 8) , (unique, 0x13180, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13180))) (
		Jmp (Word 0x15c480 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c4f2: MOV RAX,qword ptr [RSP] *)
(*    1426674: MOV RAX,qword ptr [RSP] *)
| 0x15c4f2 => Some (4,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x20, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x0, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RAX (Var (V_TEMP 0x11f00))
)

(* 0x0015c4f6: MOV RSI,qword ptr [RSP + 0x8] *)
(*    1426678: MOV RSI,qword ptr [RSP + 0x8] *)
| 0x15c4f6 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x30, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RSI (Var (V_TEMP 0x11f00))
)

(* 0x0015c4fb: LEA RAX,[RAX + RSI*0x2] *)
(*    1426683: LEA RAX,[RAX + RSI*0x2] *)
| 0x15c4fb => Some (4,
	(* (unique, 0x4980, 8) INT_MULT (register, 0x30, 8) , (const, 0x2, 8) *)
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RSI) (Word 0x2 64)) $;
	(* (unique, 0x4a80, 8) INT_ADD (register, 0x0, 8) , (unique, 0x4980, 8) *)
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4980))) $;
	(* (register, 0x0, 8) COPY (unique, 0x4a80, 8) *)
	Move R_RAX (Var (V_TEMP 0x4a80))
)

(* 0x0015c4ff: JMP 0x0015c432 *)
(*    1426687: JMP 0x0015c432 *)
| 0x15c4ff => Some (5,
	(*  ---  BRANCH (ram, 0x15c432, 8) *)
	Jmp (Word 0x15c432 64)
)

(* 0x0015c508: TEST R12,R12 *)
(*    1426696: TEST R12,R12 *)
| 0x15c508 => Some (3,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (unique, 0x70280, 8) INT_AND (register, 0xa0, 8) , (register, 0xa0, 8) *)
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_R12) (Var R_R12)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x70280, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x70280, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x70280, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c50b: JLE 0x0015c5e0 *)
(*    1426699: JLE 0x0015c5e0 *)
| 0x15c50b => Some (6,
	(* (unique, 0x12e80, 1) INT_NOTEQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x12e80) (BinOp OP_NEQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x12f80, 1) BOOL_OR (register, 0x206, 1) , (unique, 0x12e80, 1) *)
	Move (V_TEMP 0x12f80) (BinOp OP_OR (Var R_ZF) (Var (V_TEMP 0x12e80))) $;
	(*  ---  CBRANCH (ram, 0x15c5e0, 8) , (unique, 0x12f80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12f80))) (
		Jmp (Word 0x15c5e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c511: LEA RAX,[RSP + 0x20] *)
(*    1426705: LEA RAX,[RSP + 0x20] *)
| 0x15c511 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x20, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x20 64) (Var R_RSP)) $;
	(* (register, 0x0, 8) COPY (unique, 0x4e80, 8) *)
	Move R_RAX (Var (V_TEMP 0x4e80))
)

(* 0x0015c516: MOV qword ptr [RSP + 0x10],R13 *)
(*    1426710: MOV qword ptr [RSP + 0x10],R13 *)
| 0x15c516 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x10, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x10 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0xa8, 8) *)
	Move (V_TEMP 0x6a80) (Var R_R13) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c51b: MOV qword ptr [RSP + 0x8],0x0 *)
(*    1426715: MOV qword ptr [RSP + 0x8],0x0 *)
| 0x15c51b => Some (9,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Word 0x0 64) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c524: XOR R13D,R13D *)
(*    1426724: XOR R13D,R13D *)
| 0x15c524 => Some (3,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0xa8, 4) INT_XOR (register, 0xa8, 4) , (register, 0xa8, 4) *)
	Move R_R13 (Cast CAST_SIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_R13)) (Extract 31 0 (Var R_R13)))) $;
	(* (register, 0xa8, 8) INT_ZEXT (register, 0xa8, 4) *)
	Move R_R13 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R13))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xa8, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_R13)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xa8, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_R13)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0xa8, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_R13)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c527: MOV qword ptr [RSP],0x0 *)
(*    1426727: MOV qword ptr [RSP],0x0 *)
| 0x15c527 => Some (8,
	(* (unique, 0x6a80, 8) COPY (const, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Word 0x0 64) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x20, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c52f: MOV qword ptr [RSP + 0x18],RAX *)
(*    1426735: MOV qword ptr [RSP + 0x18],RAX *)
| 0x15c52f => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x18, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x18 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c534: NOP dword ptr [RAX] *)
(*    1426740: NOP dword ptr [RAX] *)
| 0x15c534 => Some (4,
	(* No pcode op *)
	Nop
)

(* 0x0015c538: MOV R15,R12 *)
(*    1426744: MOV R15,R12 *)
| 0x15c538 => Some (3,
	(* (register, 0xb8, 8) COPY (register, 0xa0, 8) *)
	Move R_R15 (Var R_R12)
)

(* 0x0015c53b: MOV EAX,0xaa *)
(*    1426747: MOV EAX,0xaa *)
| 0x15c53b => Some (5,
	(* (register, 0x0, 8) COPY (const, 0xaa, 8) *)
	Move R_RAX (Word 0xaa 64)
)

(* 0x0015c540: MOV R8,qword ptr [RSP] *)
(*    1426752: MOV R8,qword ptr [RSP] *)
| 0x15c540 => Some (4,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x20, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0015c544: SUB R15,R13 *)
(*    1426756: SUB R15,R13 *)
| 0x15c544 => Some (3,
	(* (register, 0x200, 1) INT_LESS (register, 0xb8, 8) , (register, 0xa8, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_R15) (Var R_R13))) $;
	(* (register, 0x20b, 1) INT_SBORROW (register, 0xb8, 8) , (register, 0xa8, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R15) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R15) (Var R_R13)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R15) (Var R_R13)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xb8, 8) INT_SUB (register, 0xb8, 8) , (register, 0xa8, 8) *)
	Move R_R15 (BinOp OP_MINUS (Var R_R15) (Var R_R13)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xb8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R15) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xb8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R15) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xb8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R15) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c547: MOV RDI,qword ptr [RSP + 0x18] *)
(*    1426759: MOV RDI,qword ptr [RSP + 0x18] *)
| 0x15c547 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x18, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x18 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x38, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RDI (Var (V_TEMP 0x11f00))
)

(* 0x0015c54c: MOV RDX,RBP *)
(*    1426764: MOV RDX,RBP *)
| 0x15c54c => Some (3,
	(* (register, 0x10, 8) COPY (register, 0x28, 8) *)
	Move R_RDX (Var R_RBP)
)

(* 0x0015c54f: CMP R15,RAX *)
(*    1426767: CMP R15,RAX *)
| 0x15c54f => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0xb8, 8) *)
	Move (V_TEMP 0x3f000) (Var R_R15) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RAX))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0x0, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RAX)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c552: MOV RSI,RBX *)
(*    1426770: MOV RSI,RBX *)
| 0x15c552 => Some (3,
	(* (register, 0x30, 8) COPY (register, 0x18, 8) *)
	Move R_RSI (Var R_RBX)
)

(* 0x0015c555: CMOVG R15,RAX *)
(*    1426773: CMOVG R15,RAX *)
| 0x15c555 => Some (4,
	(* (unique, 0x13000, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x13000) (UnOp OP_NOT (Var R_ZF)) $;
	(* (unique, 0x13080, 1) INT_EQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x13080) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x13180, 1) BOOL_AND (unique, 0x13000, 1) , (unique, 0x13080, 1) *)
	Move (V_TEMP 0x13180) (BinOp OP_AND (Var (V_TEMP 0x13000)) (Var (V_TEMP 0x13080))) $;
	(* (unique, 0x3dc00, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x3dc00) (Var R_RAX) $;
	(* (unique, 0x3dc80, 1) BOOL_NEGATE (unique, 0x13180, 1) *)
	Move (V_TEMP 0x3dc80) (UnOp OP_NOT (Var (V_TEMP 0x13180))) $;
	(*  ---  CBRANCH (ram, 0x15c559, 8) , (unique, 0x3dc80, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dc80))) (
		Jmp (Word 0x15c559 64)
	) (* else *) (
		Nop
	) $;
	(* (register, 0xb8, 8) COPY (unique, 0x3dc00, 8) *)
	Move R_R15 (Var (V_TEMP 0x3dc00))
)

(* 0x0015c559: ADD R13,0xaa *)
(*    1426777: ADD R13,0xaa *)
| 0x15c559 => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0xa8, 8) , (const, 0xaa, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R13) (Word 0xaa 64)) (Var R_R13))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0xa8, 8) , (const, 0xaa, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R13) (Word 0xaa 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xaa 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xa8, 8) INT_ADD (register, 0xa8, 8) , (const, 0xaa, 8) *)
	Move R_R13 (BinOp OP_PLUS (Var R_R13) (Word 0xaa 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xa8, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R13) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xa8, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R13) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xa8, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R13) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c560: MOV RCX,R15 *)
(*    1426784: MOV RCX,R15 *)
| 0x15c560 => Some (3,
	(* (register, 0x8, 8) COPY (register, 0xb8, 8) *)
	Move R_RCX (Var R_R15)
)

(* 0x0015c563: CALL 0x0010c030 *)
(*    1426787: CALL 0x0010c030 *)
| 0x15c563 => Some (5,
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (const, 0x15c568, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x15c568 64)) LittleE 8) $;
	(*  ---  CALL (ram, 0x10c030, 8) *)
	Jmp (Word 0x10c030 64)
)

(* 0x0015c568: MOV R8,qword ptr [RSP + 0x8] *)
(*    1426792: MOV R8,qword ptr [RSP + 0x8] *)
| 0x15c568 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x80, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x0015c56d: MOV RCX,R15 *)
(*    1426797: MOV RCX,R15 *)
| 0x15c56d => Some (3,
	(* (register, 0x8, 8) COPY (register, 0xb8, 8) *)
	Move R_RCX (Var R_R15)
)

(* 0x0015c570: MOV RDX,RBP *)
(*    1426800: MOV RDX,RBP *)
| 0x15c570 => Some (3,
	(* (register, 0x10, 8) COPY (register, 0x28, 8) *)
	Move R_RDX (Var R_RBP)
)

(* 0x0015c573: MOV RSI,RBX *)
(*    1426803: MOV RSI,RBX *)
| 0x15c573 => Some (3,
	(* (register, 0x30, 8) COPY (register, 0x18, 8) *)
	Move R_RSI (Var R_RBX)
)

(* 0x0015c576: MOV RDI,R14 *)
(*    1426806: MOV RDI,R14 *)
| 0x15c576 => Some (3,
	(* (register, 0x38, 8) COPY (register, 0xb0, 8) *)
	Move R_RDI (Var R_R14)
)

(* 0x0015c579: MOV qword ptr [RSP],RAX *)
(*    1426809: MOV qword ptr [RSP],RAX *)
| 0x15c579 => Some (4,
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (register, 0x20, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c57d: ADD RBX,0x550 *)
(*    1426813: ADD RBX,0x550 *)
| 0x15c57d => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) (Var R_RBX))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x18, 8) INT_ADD (register, 0x18, 8) , (const, 0x550, 8) *)
	Move R_RBX (BinOp OP_PLUS (Var R_RBX) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x18, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x18, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x18, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c584: ADD RBP,0x550 *)
(*    1426820: ADD RBP,0x550 *)
| 0x15c584 => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) (Var R_RBP))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x28, 8) INT_ADD (register, 0x28, 8) , (const, 0x550, 8) *)
	Move R_RBP (BinOp OP_PLUS (Var R_RBP) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x28, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RBP) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x28, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RBP) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x28, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RBP) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c58b: ADD R14,0x550 *)
(*    1426827: ADD R14,0x550 *)
| 0x15c58b => Some (7,
	(* (register, 0x200, 1) INT_CARRY (register, 0xb0, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R14) (Word 0x550 64)) (Var R_R14))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0xb0, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R14) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R14) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0xb0, 8) INT_ADD (register, 0xb0, 8) , (const, 0x550, 8) *)
	Move R_R14 (BinOp OP_PLUS (Var R_R14) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0xb0, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R14) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0xb0, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R14) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0xb0, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R14) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c592: CALL 0x0010b8f0 *)
(*    1426834: CALL 0x0010b8f0 *)
| 0x15c592 => Some (5,
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (const, 0x15c597, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x15c597 64)) LittleE 8) $;
	(*  ---  CALL (ram, 0x10b8f0, 8) *)
	Jmp (Word 0x10b8f0 64)
)

(* 0x0015c597: MOV RDX,R15 *)
(*    1426839: MOV RDX,R15 *)
| 0x15c597 => Some (3,
	(* (register, 0x10, 8) COPY (register, 0xb8, 8) *)
	Move R_RDX (Var R_R15)
)

(* 0x0015c59a: MOV R15,qword ptr [RSP + 0x10] *)
(*    1426842: MOV R15,qword ptr [RSP + 0x10] *)
| 0x15c59a => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x10, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x10 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0xb8, 8) COPY (unique, 0x11f00, 8) *)
	Move R_R15 (Var (V_TEMP 0x11f00))
)

(* 0x0015c59f: MOV RSI,qword ptr [RSP + 0x18] *)
(*    1426847: MOV RSI,qword ptr [RSP + 0x18] *)
| 0x15c59f => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x18, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x18 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x30, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RSI (Var (V_TEMP 0x11f00))
)

(* 0x0015c5a4: MOV qword ptr [RSP + 0x8],RAX *)
(*    1426852: MOV qword ptr [RSP + 0x8],RAX *)
| 0x15c5a4 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c5a9: MOV RDI,R15 *)
(*    1426857: MOV RDI,R15 *)
| 0x15c5a9 => Some (3,
	(* (register, 0x38, 8) COPY (register, 0xb8, 8) *)
	Move R_RDI (Var R_R15)
)

(* 0x0015c5ac: CALL 0x0010bbe0 *)
(*    1426860: CALL 0x0010bbe0 *)
| 0x15c5ac => Some (5,
	(* (register, 0x20, 8) INT_SUB (register, 0x20, 8) , (const, 0x8, 8) *)
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	(*  ---  STORE (const, 0x1b1, 8) , (register, 0x20, 8) , (const, 0x15c5b1, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x15c5b1 64)) LittleE 8) $;
	(*  ---  CALL (ram, 0x10bbe0, 8) *)
	Jmp (Word 0x10bbe0 64)
)

(* 0x0015c5b1: MOV RAX,R15 *)
(*    1426865: MOV RAX,R15 *)
| 0x15c5b1 => Some (3,
	(* (register, 0x0, 8) COPY (register, 0xb8, 8) *)
	Move R_RAX (Var R_R15)
)

(* 0x0015c5b4: ADD RAX,0x550 *)
(*    1426868: ADD RAX,0x550 *)
| 0x15c5b4 => Some (6,
	(* (register, 0x200, 1) INT_CARRY (register, 0x0, 8) , (const, 0x550, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Word 0x550 64)) (Var R_RAX))) $;
	(* (register, 0x20b, 1) INT_SCARRY (register, 0x0, 8) , (const, 0x550, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x550 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x550 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (register, 0x0, 8) INT_ADD (register, 0x0, 8) , (const, 0x550, 8) *)
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x550 64)) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (register, 0x0, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c5ba: CMP R12,R13 *)
(*    1426874: CMP R12,R13 *)
| 0x15c5ba => Some (3,
	(* (unique, 0x3f000, 8) COPY (register, 0xa0, 8) *)
	Move (V_TEMP 0x3f000) (Var R_R12) $;
	(* (register, 0x200, 1) INT_LESS (unique, 0x3f000, 8) , (register, 0xa8, 8) *)
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_R13))) $;
	(* (register, 0x20b, 1) INT_SBORROW (unique, 0x3f000, 8) , (register, 0xa8, 8) *)
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R13)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R13)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	(* (unique, 0x3f100, 8) INT_SUB (unique, 0x3f000, 8) , (register, 0xa8, 8) *)
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R13)) $;
	(* (register, 0x207, 1) INT_SLESS (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (register, 0x206, 1) INT_EQUAL (unique, 0x3f100, 8) , (const, 0x0, 8) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	(* (unique, 0x2c180, 8) INT_AND (unique, 0x3f100, 8) , (const, 0xff, 8) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 8) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c5bd: MOV qword ptr [RSP + 0x10],RAX *)
(*    1426877: MOV qword ptr [RSP + 0x10],RAX *)
| 0x15c5bd => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x10, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x10 64) (Var R_RSP)) $;
	(* (unique, 0x6a80, 8) COPY (register, 0x0, 8) *)
	Move (V_TEMP 0x6a80) (Var R_RAX) $;
	(*  ---  STORE (const, 0x1b1, 4) , (unique, 0x4e80, 8) , (unique, 0x6a80, 8) *)
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0015c5c2: JG 0x0015c538 *)
(*    1426882: JG 0x0015c538 *)
| 0x15c5c2 => Some (6,
	(* (unique, 0x13000, 1) BOOL_NEGATE (register, 0x206, 1) *)
	Move (V_TEMP 0x13000) (UnOp OP_NOT (Var R_ZF)) $;
	(* (unique, 0x13080, 1) INT_EQUAL (register, 0x20b, 1) , (register, 0x207, 1) *)
	Move (V_TEMP 0x13080) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	(* (unique, 0x13180, 1) BOOL_AND (unique, 0x13000, 1) , (unique, 0x13080, 1) *)
	Move (V_TEMP 0x13180) (BinOp OP_AND (Var (V_TEMP 0x13000)) (Var (V_TEMP 0x13080))) $;
	(*  ---  CBRANCH (ram, 0x15c538, 8) , (unique, 0x13180, 1) *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13180))) (
		Jmp (Word 0x15c538 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015c5c8: MOV RAX,qword ptr [RSP + 0x8] *)
(*    1426888: MOV RAX,qword ptr [RSP + 0x8] *)
| 0x15c5c8 => Some (5,
	(* (unique, 0x4e80, 8) INT_ADD (const, 0x8, 8) , (register, 0x20, 8) *)
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (unique, 0x4e80, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	(* (register, 0x0, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RAX (Var (V_TEMP 0x11f00))
)

(* 0x0015c5cd: MOV RDI,qword ptr [RSP] *)
(*    1426893: MOV RDI,qword ptr [RSP] *)
| 0x15c5cd => Some (4,
	(* (unique, 0x11f00, 8) LOAD (const, 0x1b1, 4) , (register, 0x20, 8) *)
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	(* (register, 0x38, 8) COPY (unique, 0x11f00, 8) *)
	Move R_RDI (Var (V_TEMP 0x11f00))
)

(* 0x0015c5d1: LEA RAX,[RAX + RDI*0x2] *)
(*    1426897: LEA RAX,[RAX + RDI*0x2] *)
| 0x15c5d1 => Some (4,
	(* (unique, 0x4980, 8) INT_MULT (register, 0x38, 8) , (const, 0x2, 8) *)
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDI) (Word 0x2 64)) $;
	(* (unique, 0x4a80, 8) INT_ADD (register, 0x0, 8) , (unique, 0x4980, 8) *)
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4980))) $;
	(* (register, 0x0, 8) COPY (unique, 0x4a80, 8) *)
	Move R_RAX (Var (V_TEMP 0x4a80))
)

(* 0x0015c5d5: JMP 0x0015c432 *)
(*    1426901: JMP 0x0015c432 *)
| 0x15c5d5 => Some (5,
	(*  ---  BRANCH (ram, 0x15c432, 8) *)
	Jmp (Word 0x15c432 64)
)

(* 0x0015c5e0: XOR EAX,EAX *)
(*    1426912: XOR EAX,EAX *)
| 0x15c5e0 => Some (2,
	(* (register, 0x200, 1) COPY (const, 0x0, 1) *)
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x20b, 1) COPY (const, 0x0, 1) *)
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	(* (register, 0x0, 4) INT_XOR (register, 0x0, 4) , (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	(* (register, 0x0, 8) INT_ZEXT (register, 0x0, 4) *)
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	(* (register, 0x207, 1) INT_SLESS (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (register, 0x206, 1) INT_EQUAL (register, 0x0, 4) , (const, 0x0, 4) *)
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	(* (unique, 0x2c180, 4) INT_AND (register, 0x0, 4) , (const, 0xff, 4) *)
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	(* (unique, 0x2c200, 1) POPCOUNT (unique, 0x2c180, 4) *)
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	(* (unique, 0x2c280, 1) INT_AND (unique, 0x2c200, 1) , (const, 0x1, 1) *)
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	(* (register, 0x202, 1) INT_EQUAL (unique, 0x2c280, 1) , (const, 0x0, 1) *)
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0015c5e2: JMP 0x0015c432 *)
(*    1426914: JMP 0x0015c432 *)
| 0x15c5e2 => Some (5,
	(*  ---  BRANCH (ram, 0x15c432, 8) *)
	Jmp (Word 0x15c432 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64.
Proof. Picinae_typecheck. Qed.


(* BEGIN BIGSTEPS GENERATED LEMMAS *)
(* Generated by: bigsteps Examples/libgmp_so_10_5_0/gmpn_add_n_sub_n_amd64.v --backend compiler --timeout 600 --ignore R_PF R_AF --invariants 0x15c360 0x15c448 0x15c508 0x15c3b8 0x15c480 0x15c538 0x15c3ef 0x15c420 0x15c4b7 0x15c4e8 0x15c568 0x15c597 0x15c5b1 0x15c432 0x15c443 0x10c030 0x10b8f0 0x10bbe0 --exits 0x15c443 0x10c030 0x10b8f0 0x10bbe0 *)
Import X64Notations.
Local Ltac ignore_vars v ::= constr:(match v with R_PF | R_AF => true | _ => false end).

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426272:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c360, s) :: t) = None))
    (VC2: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c362, s[R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ]]) :: l) = None))
    (VC3: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c364, s[R_RSP := s R_RSP ⊖ 16][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ]]) :: l) = None))
    (VC4: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c367, s[R_RSP := s R_RSP ⊖ 16][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ]][R_R14 := s R_RSI]) :: l) = None))
    (VC5: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c369, s[R_R14 := s R_RSI][R_RSP := s R_RSP ⊖ 24][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ]]) :: l) = None))
    (VC6: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c36c, s[R_R14 := s R_RSI][R_RSP := s R_RSP ⊖ 24][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ]][R_R13 := s R_RDI]) :: l) = None))
    (VC7: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c36e, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_RSP := s R_RSP ⊖ 32][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ]]) :: l) = None))
    (VC8: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c371, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_RSP := s R_RSP ⊖ 32][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ]][R_R12 := s R_R8]) :: l) = None))
    (VC9: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c372, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RSP := s R_RSP ⊖ 40][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ]]) :: l) = None))
    (VC10: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c375, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RSP := s R_RSP ⊖ 40][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ]][R_RBP := s R_RCX]) :: l) = None))
    (VC11: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c376, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][R_RSP := s R_RSP ⊖ 48][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]]) :: l) = None))
    (VC12: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c379, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][R_RSP := s R_RSP ⊖ 48][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX]) :: l) = None))
    (VC13: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c380, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_CF := if s R_RSP ⊖ 48 <? 0x000578 then 1 else 0][R_OF := (s R_RSP ⊖ 48 >> 63 .^ s R_RSP ⊖ 0x0005a8 >> 63) .& (s R_RSP ⊖ 0x0005a8 >> 63 .^ 1)][R_RSP := s R_RSP ⊖ 0x0005a8][R_SF := if slt 64 (s R_RSP ⊖ 48 ⊖ 0x000578) 0 then 1 else 0][R_ZF := if s R_RSP mod 2 ^ 64 =? 0x0005a8 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC14: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c383, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := if s R_RDI <? s R_RDX then 1 else 0][R_OF := ((s R_RDI >> 63 .^ s R_RDI ⊖ s R_RDX >> 63) .& (s R_RDI ⊖ s R_RDX >> 63 .^ s R_RDX >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RDI ⊖ s R_RDX) 0 then 1 else 0][R_ZF := if s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC15: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> forall n0 : N, (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c448, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := if s R_RDI <? s R_RDX then 1 else 0][R_OF := ((s R_RDI >> 63 .^ s R_RDI ⊖ s R_RDX >> 63) .& (s R_RDI ⊖ s R_RDX >> 63 .^ s R_RDX >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RDI ⊖ s R_RDX) 0 then 1 else 0][R_ZF := 1][R_PF := n0]) :: l)))
    (VC16: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> forall n0 : N, (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c389, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := if s R_RDI <? s R_RDX then 1 else 0][R_OF := ((s R_RDI >> 63 .^ s R_RDI ⊖ s R_RDX >> 63) .& (s R_RDI ⊖ s R_RDX >> 63 .^ s R_RDX >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RDI ⊖ s R_RDX) 0 then 1 else 0][R_ZF := 0][R_PF := n0]) :: l) = None))
    (VC17: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c38c, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := if s R_RDI <? s R_RCX then 1 else 0][R_OF := ((s R_RDI >> 63 .^ s R_RDI ⊖ s R_RCX >> 63) .& (s R_RDI ⊖ s R_RCX >> 63 .^ s R_RCX >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RDI ⊖ s R_RCX) 0 then 1 else 0][R_ZF := if s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC18: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> forall n : N, (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c448, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := if s R_RDI <? s R_RCX then 1 else 0][R_OF := ((s R_RDI >> 63 .^ s R_RDI ⊖ s R_RCX >> 63) .& (s R_RDI ⊖ s R_RCX >> 63 .^ s R_RCX >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RDI ⊖ s R_RCX) 0 then 1 else 0][R_ZF := 1][R_PF := n]) :: l)))
    (VC19: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> forall n : N, (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c392, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := if s R_RDI <? s R_RCX then 1 else 0][R_OF := ((s R_RDI >> 63 .^ s R_RDI ⊖ s R_RCX >> 63) .& (s R_RDI ⊖ s R_RCX >> 63 .^ s R_RCX >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RDI ⊖ s R_RCX) 0 then 1 else 0][R_ZF := 0][R_PF := n]) :: l) = None))
    (VC20: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c395, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0][R_ZF := if s R_R8 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC21: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> forall n0 : N, (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c39b, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0][R_ZF := if s R_R8 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC22: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> forall n0 : N, (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c39e, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0][R_ZF := if s R_R8 =? 0 then 1 else 0][R_PF := n0][R_R15 := s R_RSI]) :: l) = None))
    (VC23: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = 0 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3a1, s[R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_R15 := s R_RSI][R_CF := 0][R_OF := 0][R_R14 := scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC24: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = 0 -> forall n : N, MemAcc mem_writable s (s R_RSP ⊖ 0x0005a0) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3aa, s[R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_R15 := s R_RSI][R_CF := 0][R_OF := 0][R_R14 := scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ] [Ⓠs R_RSP ⊖ 0x0005a0 := 0 ]]) :: l) = None))
    (VC25: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = 0 -> forall n : N, MemAcc mem_writable s (s R_RSP ⊖ 0x0005a0) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 0x0005a8) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3b2, s[R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_R15 := s R_RSI][R_CF := 0][R_OF := 0][R_R14 := scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ] [Ⓠs R_RSP ⊖ 0x0005a0 := 0 ] [Ⓠs R_RSP ⊖ 0x0005a8 := 0 ]]) :: l) = None))
    (VC26: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = 0 -> forall n : N, MemAcc mem_writable s (s R_RSP ⊖ 0x0005a0) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 0x0005a8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c3b8, s[R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_R15 := s R_RSI][R_CF := 0][R_OF := 0][R_R14 := scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RSI >> 0) mod 2 ^ 32 .^ (s R_RSI >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ] [Ⓠs R_RSP ⊖ 0x0005a0 := 0 ] [Ⓠs R_RSP ⊖ 0x0005a8 := 0 ]]) :: l)))
    (VC27: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> forall (n0 : N) (p : positive), (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5e0, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0][R_ZF := if s R_R8 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC28: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> forall p : positive, (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5e2, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := 0][R_OF := 0][R_RAX := scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC29: (MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 16) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 24) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 32) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 40) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 48) 64 8 -> (s R_RDI mod 2 ^ 64 =? s R_RDX mod 2 ^ 64) = false -> (s R_RDI mod 2 ^ 64 =? s R_RCX mod 2 ^ 64) = false -> forall p : positive, (if s R_R8 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R8 .& s R_R8) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall (n : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c432, s[R_R14 := s R_RSI][R_R13 := s R_RDI][R_R12 := s R_R8][R_RBP := s R_RCX][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := s R_R15 ] [Ⓠs R_RSP ⊖ 16 := s R_R14 ] [Ⓠs R_RSP ⊖ 24 := s R_R13 ] [Ⓠs R_RSP ⊖ 32 := s R_R12 ] [Ⓠs R_RSP ⊖ 40 := s R_RBP ] [Ⓠs R_RSP ⊖ 48 := s R_RBX ]][R_RBX := s R_RDX][R_RSP := s R_RSP ⊖ 0x0005a8][R_CF := 0][R_OF := 0][R_RAX := scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426272, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
  1: solve [eapply VC15; first [eassumption | reflexivity]].
  1: solve [eapply VC16; first [eassumption | reflexivity]].
  1: solve [eapply VC17; first [eassumption | reflexivity]].
  1: solve [eapply VC18; first [eassumption | reflexivity]].
  1: solve [eapply VC19; first [eassumption | reflexivity]].
  1: solve [eapply VC20; first [eassumption | reflexivity]].
  1: solve [eapply VC21; first [eassumption | reflexivity]].
  1: solve [eapply VC22; first [eassumption | reflexivity]].
  1: solve [eapply VC23; first [eassumption | reflexivity]].
  1: solve [eapply VC24; first [eassumption | reflexivity]].
  1: solve [eapply VC25; first [eassumption | reflexivity]].
  1: solve [eapply VC26; first [eassumption | reflexivity]].
  1: solve [eapply VC27; first [eassumption | reflexivity]].
  1: solve [eapply VC28; first [eassumption | reflexivity]].
  1: solve [eapply VC29; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426504:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c448, s) :: t) = None))
    (VC2: (forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c44b, s[R_CF := if s R_RBX <? s R_R14 then 1 else 0][R_OF := ((s R_RBX >> 63 .^ s R_RBX ⊖ s R_R14 >> 63) .& (s R_RBX ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RBX ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n : N, (s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c508, s[R_CF := if s R_RBX <? s R_R14 then 1 else 0][R_OF := ((s R_RBX >> 63 .^ s R_RBX ⊖ s R_R14 >> 63) .& (s R_RBX ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RBX ⊖ s R_R14) 0 then 1 else 0][R_ZF := 1][R_PF := n]) :: l)))
    (VC4: (forall n : N, (s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c451, s[R_CF := if s R_RBX <? s R_R14 then 1 else 0][R_OF := ((s R_RBX >> 63 .^ s R_RBX ⊖ s R_R14 >> 63) .& (s R_RBX ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RBX ⊖ s R_R14) 0 then 1 else 0][R_ZF := 0][R_PF := n]) :: l) = None))
    (VC5: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c454, s[R_CF := if s R_RBP <? s R_R14 then 1 else 0][R_OF := ((s R_RBP >> 63 .^ s R_RBP ⊖ s R_R14 >> 63) .& (s R_RBP ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RBP ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC6: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall n0 : N, (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = true -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c508, s[R_CF := if s R_RBP <? s R_R14 then 1 else 0][R_OF := ((s R_RBP >> 63 .^ s R_RBP ⊖ s R_R14 >> 63) .& (s R_RBP ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RBP ⊖ s R_R14) 0 then 1 else 0][R_ZF := 1][R_PF := n0]) :: l)))
    (VC7: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall n0 : N, (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c45a, s[R_CF := if s R_RBP <? s R_R14 then 1 else 0][R_OF := ((s R_RBP >> 63 .^ s R_RBP ⊖ s R_R14 >> 63) .& (s R_RBP ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RBP ⊖ s R_R14) 0 then 1 else 0][R_ZF := 0][R_PF := n0]) :: l) = None))
    (VC8: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c45d, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC9: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall n : N, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c463, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC10: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall n : N, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c466, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n][R_R15 := s R_R13]) :: l) = None))
    (VC11: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall n : N, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c46e, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n][R_R15 := s R_R13][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := 0 ]]) :: l) = None))
    (VC12: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c471, s[R_R15 := s R_R13][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := 0 ]][R_CF := 0][R_OF := 0][R_R13 := scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC13: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall n0 : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c47a, s[R_R15 := s R_R13][R_CF := 0][R_OF := 0][R_R13 := scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := 0 ] [Ⓠ8 + s R_RSP := 0 ]]) :: l) = None))
    (VC14: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall n0 : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c480, s[R_R15 := s R_R13][R_CF := 0][R_OF := 0][R_R13 := scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := 0 ] [Ⓠ8 + s R_RSP := 0 ]]) :: l)))
    (VC15: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall (n : N) (p : positive), (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5e0, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC16: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall p : positive, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5e2, s[R_CF := 0][R_OF := 0][R_RAX := scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC17: ((s R_RBX mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> (s R_RBP mod 2 ^ 64 =? s R_R14 mod 2 ^ 64) = false -> forall p : positive, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall (n0 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c432, s[R_CF := 0][R_OF := 0][R_RAX := scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426504, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
  1: solve [eapply VC15; first [eassumption | reflexivity]].
  1: solve [eapply VC16; first [eassumption | reflexivity]].
  1: solve [eapply VC17; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426696:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c508, s) :: t) = None))
    (VC2: (forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c50b, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n : N, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c511, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC4: (forall n : N, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c516, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n][R_RAX := 32 ⊕ s R_RSP]) :: l) = None))
    (VC5: (forall n : N, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c51b, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n][R_RAX := 32 ⊕ s R_RSP][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R13 ]]) :: l) = None))
    (VC6: (forall n : N, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c524, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n][R_RAX := 32 ⊕ s R_RSP][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R13 ] [Ⓠ8 + s R_RSP := 0 ]]) :: l) = None))
    (VC7: ((if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c527, s[R_RAX := 32 ⊕ s R_RSP][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R13 ] [Ⓠ8 + s R_RSP := 0 ]][R_CF := 0][R_OF := 0][R_R13 := scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC8: ((if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall n0 : N, MemAcc mem_writable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c52f, s[R_RAX := 32 ⊕ s R_RSP][R_CF := 0][R_OF := 0][R_R13 := scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R13 ] [Ⓠ8 + s R_RSP := 0 ] [Ⓠs R_RSP := 0 ]]) :: l) = None))
    (VC9: ((if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall n0 : N, MemAcc mem_writable s (s R_RSP) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c534, s[R_RAX := 32 ⊕ s R_RSP][R_CF := 0][R_OF := 0][R_R13 := scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R13 ] [Ⓠ8 + s R_RSP := 0 ] [Ⓠs R_RSP := 0 ] [Ⓠ24 + s R_RSP := 32 + s R_RSP ]]) :: l) = None))
    (VC10: ((if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = 0 -> MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall n0 : N, MemAcc mem_writable s (s R_RSP) 64 8 -> MemAcc mem_writable s (24 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c538, s[R_RAX := 32 ⊕ s R_RSP][R_CF := 0][R_OF := 0][R_R13 := scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_R13 >> 0) mod 2 ^ 32 .^ (s R_R13 >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R13 ] [Ⓠ8 + s R_RSP := 0 ] [Ⓠs R_RSP := 0 ] [Ⓠ24 + s R_RSP := 32 + s R_RSP ]]) :: l)))
    (VC11: (forall (n : N) (p : positive), (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5e0, s[R_CF := 0][R_OF := 0][R_SF := if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0][R_ZF := if s R_R12 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC12: (forall p : positive, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5e2, s[R_CF := 0][R_OF := 0][R_RAX := scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC13: (forall p : positive, (if s R_R12 =? 0 then 1 else 0) .| (if negb (0 =? (if slt 64 (s R_R12 .& s R_R12) 0 then 1 else 0)) then 1 else 0) = N.pos p -> forall (n0 : N) (l : list (exit * store)), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c432, s[R_CF := 0][R_OF := 0][R_RAX := scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32][R_SF := if slt 32 (((scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) >> 0) mod 2 ^ 32 >> 0) mod 2 ^ 32) 0 then 1 else 0][R_ZF := if scast 32 64 ((s R_RAX >> 0) mod 2 ^ 32 .^ (s R_RAX >> 0) mod 2 ^ 32) mod 2 ^ 32 =? 0 then 1 else 0][R_PF := n0]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426696, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426360:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3b8, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3bb, s[R_RCX := s R_R12]) :: l) = None))
    (VC3: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3c0, s[R_RCX := s R_R12][R_RAX := 170]) :: l) = None))
    (VC4: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3c4, s[R_RCX := s R_R12][R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]]) :: l) = None))
    (VC5: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3c7, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_RCX := s R_R12 ⊖ s R_R14][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC6: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3ca, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_RCX := s R_R12 ⊖ s R_R14][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n][R_RDX := s R_RBP]) :: l) = None))
    (VC7: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3cd, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_RCX := s R_R12 ⊖ s R_R14][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n][R_RDX := s R_RBP][R_RSI := s R_RBX]) :: l) = None))
    (VC8: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3d0, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R14][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if s R_R12 ⊖ s R_R14 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0][R_ZF := if (s R_R12 ⊖ s R_R14) mod 2 ^ 64 =? 170 mod 2 ^ 64 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC9: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3d3, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R14][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if s R_R12 ⊖ s R_R14 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R14 =? 170 then 1 else 0][R_PF := n0][R_RDI := s R_R13]) :: l) = None))
    (VC10: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall n0 : N, N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3d7, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if s R_R12 ⊖ s R_R14 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R14 =? 170 then 1 else 0][R_PF := n0][R_RDI := s R_R13][R_RCX := 170]) :: l) = None))
    (VC11: (MemAcc mem_readable s (s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = 0 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3de, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R13][R_RCX := 170][R_CF := if 170 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((170 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 170 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC12: (MemAcc mem_readable s (s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = 0 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3e5, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R13][R_RCX := 170][R_R14 := 170 ⊕ s R_R14][R_CF := if 0x000550 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((0x000550 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 0x000550 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC13: (MemAcc mem_readable s (s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = 0 -> forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3ea, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R13][R_RCX := 170][R_R14 := 170 ⊕ s R_R14][R_CF := if 0x000550 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((0x000550 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 0x000550 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 170 ]]) :: l) = None))
    (VC14: (MemAcc mem_readable s (s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = 0 -> forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010c030, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R13][R_RCX := 170][R_R14 := 170 ⊕ s R_R14][R_CF := if 0x000550 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((0x000550 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 0x000550 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n0][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 170 ] [Ⓠs R_RSP ⊖ 8 := 0x0015c3ef ]]) :: l)))
    (VC15: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n0 : N) (p : positive), N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3d7, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R14][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if s R_R12 ⊖ s R_R14 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R14 =? 170 then 1 else 0][R_PF := n0][R_RDI := s R_R13]) :: l) = None))
    (VC16: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3de, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R14][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R13][R_CF := if 170 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((170 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 170 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC17: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3e5, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R14][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R13][R_R14 := 170 ⊕ s R_R14][R_CF := if 0x000550 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((0x000550 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 0x000550 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC18: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3ea, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R14][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R13][R_R14 := 170 ⊕ s R_R14][R_CF := if 0x000550 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((0x000550 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 0x000550 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R12 ⊖ s R_R14 ]]) :: l) = None))
    (VC19: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R12 ⊖ s R_R14 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R14 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R14 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R14 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010c030, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R14][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R13][R_R14 := 170 ⊕ s R_R14][R_CF := if 0x000550 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((0x000550 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 0x000550 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n0][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R12 ⊖ s R_R14 ] [Ⓠs R_RSP ⊖ 8 := 0x0015c3ef ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426360, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
  1: solve [eapply VC15; first [eassumption | reflexivity]].
  1: solve [eapply VC16; first [eassumption | reflexivity]].
  1: solve [eapply VC17; first [eassumption | reflexivity]].
  1: solve [eapply VC18; first [eassumption | reflexivity]].
  1: solve [eapply VC19; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426560:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c480, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c483, s[R_RCX := s R_R12]) :: l) = None))
    (VC3: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c488, s[R_RCX := s R_R12][R_RAX := 170]) :: l) = None))
    (VC4: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c48c, s[R_RCX := s R_R12][R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]]) :: l) = None))
    (VC5: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c48f, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_RCX := s R_R12 ⊖ s R_R13][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC6: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c492, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_RCX := s R_R12 ⊖ s R_R13][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][R_RDX := s R_RBP]) :: l) = None))
    (VC7: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c495, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_RCX := s R_R12 ⊖ s R_R13][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][R_RDX := s R_RBP][R_RSI := s R_RBX]) :: l) = None))
    (VC8: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c498, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R13][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if s R_R12 ⊖ s R_R13 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0][R_ZF := if (s R_R12 ⊖ s R_R13) mod 2 ^ 64 =? 170 mod 2 ^ 64 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC9: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c49b, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R13][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if s R_R12 ⊖ s R_R13 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R13 =? 170 then 1 else 0][R_PF := n0][R_RDI := s R_R14]) :: l) = None))
    (VC10: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall n0 : N, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c49f, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if s R_R12 ⊖ s R_R13 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R13 =? 170 then 1 else 0][R_PF := n0][R_RDI := s R_R14][R_RCX := 170]) :: l) = None))
    (VC11: (MemAcc mem_readable s (s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4a6, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_RCX := 170][R_CF := if 170 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((170 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 170 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC12: (MemAcc mem_readable s (s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4ad, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_RCX := 170][R_R13 := 170 ⊕ s R_R13][R_CF := if 0x000550 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((0x000550 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 0x000550 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC13: (MemAcc mem_readable s (s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4b2, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_RCX := 170][R_R13 := 170 ⊕ s R_R13][R_CF := if 0x000550 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((0x000550 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 0x000550 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 170 ]]) :: l) = None))
    (VC14: (MemAcc mem_readable s (s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010b8f0, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_RCX := 170][R_R13 := 170 ⊕ s R_R13][R_CF := if 0x000550 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((0x000550 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 0x000550 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n0][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 170 ] [Ⓠs R_RSP ⊖ 8 := 0x0015c4b7 ]]) :: l)))
    (VC15: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n0 : N) (p : positive), N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c49f, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R13][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if s R_R12 ⊖ s R_R13 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R13 =? 170 then 1 else 0][R_PF := n0][R_RDI := s R_R14]) :: l) = None))
    (VC16: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4a6, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R13][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_CF := if 170 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((170 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 170 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC17: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4ad, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R13][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_R13 := 170 ⊕ s R_R13][R_CF := if 0x000550 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((0x000550 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 0x000550 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC18: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4b2, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R13][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_R13 := 170 ⊕ s R_R13][R_CF := if 0x000550 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((0x000550 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 0x000550 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R12 ⊖ s R_R13 ]]) :: l) = None))
    (VC19: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010b8f0, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RCX := s R_R12 ⊖ s R_R13][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_R13 := 170 ⊕ s R_R13][R_CF := if 0x000550 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((0x000550 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 0x000550 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n0][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := s R_R12 ⊖ s R_R13 ] [Ⓠs R_RSP ⊖ 8 := 0x0015c4b7 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426560, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
  1: solve [eapply VC15; first [eassumption | reflexivity]].
  1: solve [eapply VC16; first [eassumption | reflexivity]].
  1: solve [eapply VC17; first [eassumption | reflexivity]].
  1: solve [eapply VC18; first [eassumption | reflexivity]].
  1: solve [eapply VC19; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426744:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c538, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c53b, s[R_R15 := s R_R12]) :: l) = None))
    (VC3: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c540, s[R_R15 := s R_R12][R_RAX := 170]) :: l) = None))
    (VC4: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c544, s[R_R15 := s R_R12][R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]]) :: l) = None))
    (VC5: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c547, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_R15 := s R_R12 ⊖ s R_R13][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC6: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall n : N, MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c54c, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_R15 := s R_R12 ⊖ s R_R13][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]]) :: l) = None))
    (VC7: (MemAcc mem_readable s (s R_RSP) 64 8 -> forall n : N, MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c54f, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_R15 := s R_R12 ⊖ s R_R13][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP]) :: l) = None))
    (VC8: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c552, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_R15 := s R_R12 ⊖ s R_R13][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_CF := if s R_R12 ⊖ s R_R13 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0][R_ZF := if (s R_R12 ⊖ s R_R13) mod 2 ^ 64 =? 170 mod 2 ^ 64 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC9: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c555, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_R15 := s R_R12 ⊖ s R_R13][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_CF := if s R_R12 ⊖ s R_R13 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R13 =? 170 then 1 else 0][R_PF := n0][R_RSI := s R_RBX]) :: l) = None))
    (VC10: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall n0 : N, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c559, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_CF := if s R_R12 ⊖ s R_R13 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R13 =? 170 then 1 else 0][R_PF := n0][R_RSI := s R_RBX][R_R15 := 170]) :: l) = None))
    (VC11: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c560, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_R15 := 170][R_CF := if 170 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((170 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 170 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC12: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c563, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_R15 := 170][R_CF := if 170 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((170 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 170 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n][R_RCX := 170]) :: l) = None))
    (VC13: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = 0 -> forall n : N, MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010c030, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_R15 := 170][R_CF := if 170 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((170 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 170 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n][R_RCX := 170][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := 0x0015c568 ]]) :: l)))
    (VC14: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall (n0 : N) (p : positive), N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c559, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_R15 := s R_R12 ⊖ s R_R13][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_CF := if s R_R12 ⊖ s R_R13 <? 170 then 1 else 0][R_OF := (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1)][R_SF := if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0][R_ZF := if s R_R12 ⊖ s R_R13 =? 170 then 1 else 0][R_PF := n0][R_RSI := s R_RBX]) :: l) = None))
    (VC15: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c560, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_R15 := s R_R12 ⊖ s R_R13][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if 170 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((170 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 170 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC16: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c563, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_R15 := s R_R12 ⊖ s R_R13][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if 170 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((170 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 170 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n][R_RCX := s R_R12 ⊖ s R_R13]) :: l) = None))
    (VC17: (MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall p : positive, N.lnot (if (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R12 ⊖ s R_R13 ⊖ 170 >> 63) .& (s R_R12 ⊖ s R_R13 ⊖ 170 >> 63 .^ 1) =? (if slt 64 (s R_R12 ⊖ s R_R13 ⊖ 170) 0 then 1 else 0) then if s R_R12 ⊖ s R_R13 =? 170 then 0 else 1 else 0) 1 = N.pos p -> forall n : N, MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010c030, s[R_RAX := 170][R_R8 := s V_MEM64 Ⓠ[ s R_RSP ]][R_R15 := s R_R12 ⊖ s R_R13][R_RDI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_CF := if 170 ⊕ s R_R13 <? s R_R13 then 1 else 0][R_OF := ((170 + s R_R13 >> 63 .^ s R_R13 >> 63) .& (s R_R13 >> 63 .^ 1)) mod 2][R_R13 := 170 ⊕ s R_R13][R_SF := if slt 64 (s R_R13 ⊕ 170) 0 then 1 else 0][R_ZF := if 170 ⊕ s R_R13 =? 0 then 1 else 0][R_PF := n][R_RCX := s R_R12 ⊖ s R_R13][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠs R_RSP ⊖ 8 := 0x0015c568 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426744, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
  1: solve [eapply VC15; first [eassumption | reflexivity]].
  1: solve [eapply VC16; first [eassumption | reflexivity]].
  1: solve [eapply VC17; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426415:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3ef, s) :: t) = None))
    (VC2: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3f4, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]]) :: l) = None))
    (VC3: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3f9, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]]) :: l) = None))
    (VC4: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3fc, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP]) :: l) = None))
    (VC5: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c3ff, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX]) :: l) = None))
    (VC6: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c402, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15]) :: l) = None))
    (VC7: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c406, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]]) :: l) = None))
    (VC8: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c40d, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_CF := if 0x000550 ⊕ s R_RBX <? s R_RBX then 1 else 0][R_OF := ((0x000550 + s R_RBX >> 63 .^ s R_RBX >> 63) .& (s R_RBX >> 63 .^ 1)) mod 2][R_RBX := 0x000550 ⊕ s R_RBX][R_SF := if slt 64 (s R_RBX ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_RBX =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC9: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c414, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_RBX := 0x000550 ⊕ s R_RBX][R_CF := if 0x000550 ⊕ s R_RBP <? s R_RBP then 1 else 0][R_OF := ((0x000550 + s R_RBP >> 63 .^ s R_RBP >> 63) .& (s R_RBP >> 63 .^ 1)) mod 2][R_RBP := 0x000550 ⊕ s R_RBP][R_SF := if slt 64 (s R_RBP ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_RBP =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC10: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c41b, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_RBX := 0x000550 ⊕ s R_RBX][R_RBP := 0x000550 ⊕ s R_RBP][R_CF := if 0x000550 ⊕ s R_R15 <? s R_R15 then 1 else 0][R_OF := ((0x000550 + s R_R15 >> 63 .^ s R_R15 >> 63) .& (s R_R15 >> 63 .^ 1)) mod 2][R_R15 := 0x000550 ⊕ s R_R15][R_SF := if slt 64 (s R_R15 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R15 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC11: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall n : N, MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010b8f0, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][R_RBX := 0x000550 ⊕ s R_RBX][R_RBP := 0x000550 ⊕ s R_RBP][R_CF := if 0x000550 ⊕ s R_R15 <? s R_R15 then 1 else 0][R_OF := ((0x000550 + s R_R15 >> 63 .^ s R_R15 >> 63) .& (s R_R15 >> 63 .^ 1)) mod 2][R_R15 := 0x000550 ⊕ s R_R15][R_SF := if slt 64 (s R_R15 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R15 =? 0 then 1 else 0][R_PF := n][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ] [Ⓠs R_RSP ⊖ 8 := 0x0015c420 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426415, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426464:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c420, s) :: t) = None))
    (VC2: (forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c423, s[R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c428, s[R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]]) :: l) = None))
    (VC4: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c42a, s[R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]]) :: l) = None))
    (VC5: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c42e, s[R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]][R_RDX := s V_MEM64 Ⓠ[ s R_RSP ]]) :: l) = None))
    (VC6: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c432, s[R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]][R_RDX := s V_MEM64 Ⓠ[ s R_RSP ]][R_RAX := s R_RAX ⊕ s V_MEM64 Ⓠ[ s R_RSP ] * 2]) :: l)))
    (VC7: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall p : positive, (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 0 else 1 else 0) = N.pos p -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c3b8, s[R_CF := if s R_R12 <? s R_R14 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R14 >> 63) .& (s R_R12 ⊖ s R_R14 >> 63 .^ s R_R14 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R14) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R14 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426464, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426615:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4b7, s) :: t) = None))
    (VC2: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4bc, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]]) :: l) = None))
    (VC3: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4c1, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]]) :: l) = None))
    (VC4: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4c4, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP]) :: l) = None))
    (VC5: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4c7, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX]) :: l) = None))
    (VC6: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4ca, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15]) :: l) = None))
    (VC7: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4ce, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]]) :: l) = None))
    (VC8: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4d5, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_CF := if 0x000550 ⊕ s R_RBX <? s R_RBX then 1 else 0][R_OF := ((0x000550 + s R_RBX >> 63 .^ s R_RBX >> 63) .& (s R_RBX >> 63 .^ 1)) mod 2][R_RBX := 0x000550 ⊕ s R_RBX][R_SF := if slt 64 (s R_RBX ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_RBX =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC9: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4dc, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_RBX := 0x000550 ⊕ s R_RBX][R_CF := if 0x000550 ⊕ s R_RBP <? s R_RBP then 1 else 0][R_OF := ((0x000550 + s R_RBP >> 63 .^ s R_RBP >> 63) .& (s R_RBP >> 63 .^ 1)) mod 2][R_RBP := 0x000550 ⊕ s R_RBP][R_SF := if slt 64 (s R_RBP ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_RBP =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC10: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4e3, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_RBX := 0x000550 ⊕ s R_RBX][R_RBP := 0x000550 ⊕ s R_RBP][R_CF := if 0x000550 ⊕ s R_R15 <? s R_R15 then 1 else 0][R_OF := ((0x000550 + s R_R15 >> 63 .^ s R_R15 >> 63) .& (s R_R15 >> 63 .^ 1)) mod 2][R_R15 := 0x000550 ⊕ s R_R15][R_SF := if slt 64 (s R_R15 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R15 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC11: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall n : N, MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010c030, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R15][R_RBX := 0x000550 ⊕ s R_RBX][R_RBP := 0x000550 ⊕ s R_RBP][R_CF := if 0x000550 ⊕ s R_R15 <? s R_R15 then 1 else 0][R_OF := ((0x000550 + s R_R15 >> 63 .^ s R_R15 >> 63) .& (s R_R15 >> 63 .^ 1)) mod 2][R_R15 := 0x000550 ⊕ s R_R15][R_SF := if slt 64 (s R_R15 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R15 =? 0 then 1 else 0][R_PF := n][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ] [Ⓠs R_RSP ⊖ 8 := 0x0015c4e8 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426615, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426664:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4e8, s) :: t) = None))
    (VC2: (forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4eb, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4f0, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]]) :: l) = None))
    (VC4: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4f2, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]]) :: l) = None))
    (VC5: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4f6, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]][R_RAX := s V_MEM64 Ⓠ[ s R_RSP ]]) :: l) = None))
    (VC6: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4fb, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]][R_RAX := s V_MEM64 Ⓠ[ s R_RSP ]][R_RSI := s R_RAX mod 2 ^ 64]) :: l) = None))
    (VC7: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c4ff, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]][R_RSI := s R_RAX mod 2 ^ 64][R_RAX := s V_MEM64 Ⓠ[ s R_RSP ] ⊕ s R_RAX * 2]) :: l) = None))
    (VC8: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (s R_RSP) 64 8 -> MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c432, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]][R_RSI := s R_RAX mod 2 ^ 64][R_RAX := s V_MEM64 Ⓠ[ s R_RSP ] ⊕ s R_RAX * 2]) :: l)))
    (VC9: (forall n : N, MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall p : positive, (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = N.pos p -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c480, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426664, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426792:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c568, s) :: t) = None))
    (VC2: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c56d, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]]) :: l) = None))
    (VC3: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c570, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15]) :: l) = None))
    (VC4: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c573, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15][R_RDX := s R_RBP]) :: l) = None))
    (VC5: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c576, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15][R_RDX := s R_RBP][R_RSI := s R_RBX]) :: l) = None))
    (VC6: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c579, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14]) :: l) = None))
    (VC7: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c57d, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]]) :: l) = None))
    (VC8: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c584, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_CF := if 0x000550 ⊕ s R_RBX <? s R_RBX then 1 else 0][R_OF := ((0x000550 + s R_RBX >> 63 .^ s R_RBX >> 63) .& (s R_RBX >> 63 .^ 1)) mod 2][R_RBX := 0x000550 ⊕ s R_RBX][R_SF := if slt 64 (s R_RBX ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_RBX =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC9: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c58b, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_RBX := 0x000550 ⊕ s R_RBX][R_CF := if 0x000550 ⊕ s R_RBP <? s R_RBP then 1 else 0][R_OF := ((0x000550 + s R_RBP >> 63 .^ s R_RBP >> 63) .& (s R_RBP >> 63 .^ 1)) mod 2][R_RBP := 0x000550 ⊕ s R_RBP][R_SF := if slt 64 (s R_RBP ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_RBP =? 0 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC10: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c592, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ]][R_RBX := 0x000550 ⊕ s R_RBX][R_RBP := 0x000550 ⊕ s R_RBP][R_CF := if 0x000550 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((0x000550 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 0x000550 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC11: (MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP) 64 8 -> forall n : N, MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010b8f0, s[R_R8 := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RCX := s R_R15][R_RDX := s R_RBP][R_RSI := s R_RBX][R_RDI := s R_R14][R_RBX := 0x000550 ⊕ s R_RBX][R_RBP := 0x000550 ⊕ s R_RBP][R_CF := if 0x000550 ⊕ s R_R14 <? s R_R14 then 1 else 0][R_OF := ((0x000550 + s R_R14 >> 63 .^ s R_R14 >> 63) .& (s R_R14 >> 63 .^ 1)) mod 2][R_R14 := 0x000550 ⊕ s R_R14][R_SF := if slt 64 (s R_R14 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R14 =? 0 then 1 else 0][R_PF := n][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠs R_RSP := s R_RAX ] [Ⓠs R_RSP ⊖ 8 := 0x0015c597 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426792, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426839:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c597, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c59a, s[R_RDX := s R_R15]) :: l) = None))
    (VC3: (MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c59f, s[R_RDX := s R_R15][R_R15 := s V_MEM64 Ⓠ[ 16 + s R_RSP ]]) :: l) = None))
    (VC4: (MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5a4, s[R_RDX := s R_R15][R_R15 := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RSI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]]) :: l) = None))
    (VC5: (MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5a9, s[R_RDX := s R_R15][R_R15 := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RSI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]]) :: l) = None))
    (VC6: (MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5ac, s[R_RDX := s R_R15][R_R15 := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RSI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ]][R_RDI := s V_MEM64 Ⓠ[ 16 + s R_RSP ]]) :: l) = None))
    (VC7: (MemAcc mem_readable s (16 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (24 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_writable s (s R_RSP ⊖ 8) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0010bbe0, s[R_RDX := s R_R15][R_R15 := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RSI := s V_MEM64 Ⓠ[ 24 + s R_RSP ]][R_RDI := s V_MEM64 Ⓠ[ 16 + s R_RSP ]][R_RSP := s R_RSP ⊖ 8][V_MEM64 := s V_MEM64 [Ⓠ8 + s R_RSP := s R_RAX ] [Ⓠs R_RSP ⊖ 8 := 0x0015c5b1 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426839, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
  Unshelve.
  1: solve [eapply VC1; first [eassumption | reflexivity]].
  1: solve [eapply VC2; first [eassumption | reflexivity]].
  1: solve [eapply VC3; first [eassumption | reflexivity]].
  1: solve [eapply VC4; first [eassumption | reflexivity]].
  1: solve [eapply VC5; first [eassumption | reflexivity]].
  1: solve [eapply VC6; first [eassumption | reflexivity]].
  1: solve [eapply VC7; first [eassumption | reflexivity]].
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426865:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5b1, s) :: t) = None))
    (VC2: (forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5b4, s[R_RAX := s R_R15]) :: l) = None))
    (VC3: (forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5ba, s[R_CF := if 0x000550 ⊕ s R_R15 <? s R_R15 then 1 else 0][R_OF := ((0x000550 + s R_R15 >> 63 .^ s R_R15 >> 63) .& (s R_R15 >> 63 .^ 1)) mod 2][R_RAX := 0x000550 ⊕ s R_R15][R_SF := if slt 64 (s R_R15 ⊕ 0x000550) 0 then 1 else 0][R_ZF := if 0x000550 ⊕ s R_R15 =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC4: (forall (n0 : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5bd, s[R_RAX := 0x000550 ⊕ s R_R15][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n0]) :: l) = None))
    (VC5: (forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5c2, s[R_RAX := 0x000550 ⊕ s R_R15][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 0x000550 + s R_R15 ]]) :: l) = None))
    (VC6: (forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5c8, s[R_RAX := 0x000550 ⊕ s R_R15][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 0x000550 + s R_R15 ]]) :: l) = None))
    (VC7: (forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5cd, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 0x000550 + s R_R15 ]][R_RAX := s V_MEM64 Ⓠ[ 8 + s R_RSP ]]) :: l) = None))
    (VC8: (forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5d1, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 0x000550 + s R_R15 ]][R_RAX := s V_MEM64 Ⓠ[ 8 + s R_RSP ]][R_RDI := s V_MEM64 Ⓠ[ s R_RSP ]]) :: l) = None))
    (VC9: (forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c5d5, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 0x000550 + s R_R15 ]][R_RDI := s V_MEM64 Ⓠ[ s R_RSP ]][R_RAX := s V_MEM64 Ⓠ[ 8 + s R_RSP ] ⊕ s V_MEM64 Ⓠ[ s R_RSP ] * 2]) :: l) = None))
    (VC10: (forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = 0 -> MemAcc mem_readable s (8 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (s R_RSP) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c432, s[R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 0x000550 + s R_R15 ]][R_RDI := s V_MEM64 Ⓠ[ s R_RSP ]][R_RAX := s V_MEM64 Ⓠ[ 8 + s R_RSP ] ⊕ s V_MEM64 Ⓠ[ s R_RSP ] * 2]) :: l)))
    (VC11: (forall n0 : N, MemAcc mem_writable s (16 ⊕ s R_RSP) 64 8 -> forall p : positive, (if ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2 =? (if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0) then if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 0 else 1 else 0) = N.pos p -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c538, s[R_RAX := 0x000550 ⊕ s R_R15][R_CF := if s R_R12 <? s R_R13 then 1 else 0][R_OF := ((s R_R12 >> 63 .^ s R_R12 ⊖ s R_R13 >> 63) .& (s R_R12 ⊖ s R_R13 >> 63 .^ s R_R13 >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_R12 ⊖ s R_R13) 0 then 1 else 0][R_ZF := if s R_R12 mod 2 ^ 64 =? s R_R13 mod 2 ^ 64 then 1 else 0][R_PF := n0][V_MEM64 := s V_MEM64 [Ⓠ16 + s R_RSP := 0x000550 + s R_R15 ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426865, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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
Qed.

Lemma libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426482:
  forall invs exits s t
    (VC1: (forall t : list (exit * X64Arch.store), effinv false libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c432, s) :: t) = None))
    (VC2: (forall (n : N) (l : list (exit * store)), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c439, s[R_CF := if 0x000578 ⊕ s R_RSP <? s R_RSP then 1 else 0][R_OF := ((0x000578 + s R_RSP >> 63 .^ s R_RSP >> 63) .& (s R_RSP >> 63 .^ 1)) mod 2][R_RSP := 0x000578 ⊕ s R_RSP][R_SF := if slt 64 (s R_RSP ⊕ 0x000578) 0 then 1 else 0][R_ZF := if 0x000578 ⊕ s R_RSP =? 0 then 1 else 0][R_PF := n]) :: l) = None))
    (VC3: (forall n : N, MemAcc mem_readable s (0x000578 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c43a, s[R_CF := if 0x000578 ⊕ s R_RSP <? s R_RSP then 1 else 0][R_OF := ((0x000578 + s R_RSP >> 63 .^ s R_RSP >> 63) .& (s R_RSP >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RSP ⊕ 0x000578) 0 then 1 else 0][R_ZF := if 0x000578 ⊕ s R_RSP =? 0 then 1 else 0][R_PF := n][R_RSP := 0x000580 ⊕ s R_RSP][R_RBX := s V_MEM64 Ⓠ[ 0x000578 + s R_RSP ]]) :: l) = None))
    (VC4: (forall n : N, MemAcc mem_readable s (0x000578 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000580 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c43b, s[R_CF := if 0x000578 ⊕ s R_RSP <? s R_RSP then 1 else 0][R_OF := ((0x000578 + s R_RSP >> 63 .^ s R_RSP >> 63) .& (s R_RSP >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RSP ⊕ 0x000578) 0 then 1 else 0][R_ZF := if 0x000578 ⊕ s R_RSP =? 0 then 1 else 0][R_PF := n][R_RBX := s V_MEM64 Ⓠ[ 0x000578 + s R_RSP ]][R_RSP := 0x000588 ⊕ s R_RSP][R_RBP := s V_MEM64 Ⓠ[ 0x000580 + s R_RSP ]]) :: l) = None))
    (VC5: (forall n : N, MemAcc mem_readable s (0x000578 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000580 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000588 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c43d, s[R_CF := if 0x000578 ⊕ s R_RSP <? s R_RSP then 1 else 0][R_OF := ((0x000578 + s R_RSP >> 63 .^ s R_RSP >> 63) .& (s R_RSP >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RSP ⊕ 0x000578) 0 then 1 else 0][R_ZF := if 0x000578 ⊕ s R_RSP =? 0 then 1 else 0][R_PF := n][R_RBX := s V_MEM64 Ⓠ[ 0x000578 + s R_RSP ]][R_RBP := s V_MEM64 Ⓠ[ 0x000580 + s R_RSP ]][R_RSP := 0x000590 ⊕ s R_RSP][R_R12 := s V_MEM64 Ⓠ[ 0x000588 + s R_RSP ]]) :: l) = None))
    (VC6: (forall n : N, MemAcc mem_readable s (0x000578 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000580 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000588 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000590 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c43f, s[R_CF := if 0x000578 ⊕ s R_RSP <? s R_RSP then 1 else 0][R_OF := ((0x000578 + s R_RSP >> 63 .^ s R_RSP >> 63) .& (s R_RSP >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RSP ⊕ 0x000578) 0 then 1 else 0][R_ZF := if 0x000578 ⊕ s R_RSP =? 0 then 1 else 0][R_PF := n][R_RBX := s V_MEM64 Ⓠ[ 0x000578 + s R_RSP ]][R_RBP := s V_MEM64 Ⓠ[ 0x000580 + s R_RSP ]][R_R12 := s V_MEM64 Ⓠ[ 0x000588 + s R_RSP ]][R_RSP := 0x000598 ⊕ s R_RSP][R_R13 := s V_MEM64 Ⓠ[ 0x000590 + s R_RSP ]]) :: l) = None))
    (VC7: (forall n : N, MemAcc mem_readable s (0x000578 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000580 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000588 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000590 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000598 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), effinv true libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits ((Addr 0x0015c441, s[R_CF := if 0x000578 ⊕ s R_RSP <? s R_RSP then 1 else 0][R_OF := ((0x000578 + s R_RSP >> 63 .^ s R_RSP >> 63) .& (s R_RSP >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RSP ⊕ 0x000578) 0 then 1 else 0][R_ZF := if 0x000578 ⊕ s R_RSP =? 0 then 1 else 0][R_PF := n][R_RBX := s V_MEM64 Ⓠ[ 0x000578 + s R_RSP ]][R_RBP := s V_MEM64 Ⓠ[ 0x000580 + s R_RSP ]][R_R12 := s V_MEM64 Ⓠ[ 0x000588 + s R_RSP ]][R_R13 := s V_MEM64 Ⓠ[ 0x000590 + s R_RSP ]][R_RSP := 0x0005a0 ⊕ s R_RSP][R_R14 := s V_MEM64 Ⓠ[ 0x000598 + s R_RSP ]]) :: l) = None))
    (VC8: (forall n : N, MemAcc mem_readable s (0x000578 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000580 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000588 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000590 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x000598 ⊕ s R_RSP) 64 8 -> MemAcc mem_readable s (0x0005a0 ⊕ s R_RSP) 64 8 -> forall l : list (exit * store), nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits true ((Addr 0x0015c443, s[R_CF := if 0x000578 ⊕ s R_RSP <? s R_RSP then 1 else 0][R_OF := ((0x000578 + s R_RSP >> 63 .^ s R_RSP >> 63) .& (s R_RSP >> 63 .^ 1)) mod 2][R_SF := if slt 64 (s R_RSP ⊕ 0x000578) 0 then 1 else 0][R_ZF := if 0x000578 ⊕ s R_RSP =? 0 then 1 else 0][R_PF := n][R_RBX := s V_MEM64 Ⓠ[ 0x000578 + s R_RSP ]][R_RBP := s V_MEM64 Ⓠ[ 0x000580 + s R_RSP ]][R_R12 := s V_MEM64 Ⓠ[ 0x000588 + s R_RSP ]][R_R13 := s V_MEM64 Ⓠ[ 0x000590 + s R_RSP ]][R_R14 := s V_MEM64 Ⓠ[ 0x000598 + s R_RSP ]][R_RSP := 0x0005a8 ⊕ s R_RSP][R_R15 := s V_MEM64 Ⓠ[ 0x0005a0 + s R_RSP ]]) :: l)))
  ,
  nextinv libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 invs exits false ((Addr 1426482, s)::t).
Proof.
  intros; find_vcs (1426272::1426504::1426696::1426360::1426560::1426744::1426415::1426464::1426615::1426664::1426792::1426839::1426865::1426482::1426499::1097776::1095920::1096672::nil).
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

Ltac libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_bigstep := first [ apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426272 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426504 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426696 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426360 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426560 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426744 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426415 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426464 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426615 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426664 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426792 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426839 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426865 | apply libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64_stepfrom_1426482 ]; intros; (reflexivity || ISA_invhere).
(* END BIGSTEPS GENERATED LEMMAS *)
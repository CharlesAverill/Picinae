(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: memmove
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition memmove_amd64 : program := fun _ a => match a with

(* 0x00134680: MOV RAX,RDI *)
(*    1263232: MOV RAX,RDI *)
| 0x134680 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x00134683: CMP RDI,RSI *)
(*    1263235: CMP RDI,RSI *)
| 0x134683 => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RDI) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RSI))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RSI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134686: JZ 0x00134790 *)
(*    1263238: JZ 0x00134790 *)
| 0x134686 => Some (6,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x134790 64)
	) (* else *) (
		Nop
	)
)

(* 0x0013468c: MOV RCX,RSI *)
(*    1263244: MOV RCX,RSI *)
| 0x13468c => Some (3,
	Move R_RCX (Var R_RSI)
)

(* 0x0013468f: SUB RCX,RDX *)
(*    1263247: SUB RCX,RDX *)
| 0x13468f => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RCX) (Var R_RDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134692: SUB RCX,RDI *)
(*    1263250: SUB RCX,RDI *)
| 0x134692 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RCX) (Var R_RDI))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134695: MOV RDI,RDX *)
(*    1263253: MOV RDI,RDX *)
| 0x134695 => Some (3,
	Move R_RDI (Var R_RDX)
)

(* 0x00134698: NEG RDI *)
(*    1263256: NEG RDI *)
| 0x134698 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var R_RDI) (Word 0x0 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 64) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 64) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 64) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (UnOp OP_NEG (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013469b: ADD RDI,RDI *)
(*    1263259: ADD RDI,RDI *)
| 0x13469b => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Var R_RDI)) (Var R_RDI))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013469e: CMP RDI,RCX *)
(*    1263262: CMP RDI,RCX *)
| 0x13469e => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RDI) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RCX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346a1: JNC 0x001346be *)
(*    1263265: JNC 0x001346be *)
| 0x1346a1 => Some (2,
	Move (V_TEMP 0x12680) (UnOp OP_NOT (Var R_CF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12680))) (
		Jmp (Word 0x1346be 64)
	) (* else *) (
		Nop
	)
)

(* 0x001346a3: MOV RCX,RSI *)
(*    1263267: MOV RCX,RSI *)
| 0x1346a3 => Some (3,
	Move R_RCX (Var R_RSI)
)

(* 0x001346a6: XOR RCX,RAX *)
(*    1263270: XOR RCX,RAX *)
| 0x1346a6 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_XOR (Var R_RCX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346a9: CMP RAX,RSI *)
(*    1263273: CMP RAX,RSI *)
| 0x1346a9 => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RAX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RSI))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RSI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346ac: JNC 0x00134733 *)
(*    1263276: JNC 0x00134733 *)
| 0x1346ac => Some (6,
	Move (V_TEMP 0x12680) (UnOp OP_NOT (Var R_CF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12680))) (
		Jmp (Word 0x134733 64)
	) (* else *) (
		Nop
	)
)

(* 0x001346b2: AND ECX,0x7 *)
(*    1263282: AND ECX,0x7 *)
| 0x1346b2 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x7 32))) (Word 0 64)) (BinOp OP_AND (Var R_RCX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346b5: MOV RDI,RAX *)
(*    1263285: MOV RDI,RAX *)
| 0x1346b5 => Some (3,
	Move R_RDI (Var R_RAX)
)

(* 0x001346b8: JZ 0x001346c6 *)
(*    1263288: JZ 0x001346c6 *)
| 0x1346b8 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x1346c6 64)
	) (* else *) (
		Nop
	)
)

(* 0x001346ba: XOR ECX,ECX *)
(*    1263290: XOR ECX,ECX *)
| 0x1346ba => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_RCX)))) (Word 0 64)) (BinOp OP_AND (Var R_RCX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346bc: JMP 0x0013472d *)
(*    1263292: JMP 0x0013472d *)
| 0x1346bc => Some (2,
	Jmp (Word 0x13472d 64)
)

(* 0x001346be: MOV RDI,RAX *)
(*    1263294: MOV RDI,RAX *)
| 0x1346be => Some (3,
	Move R_RDI (Var R_RAX)
)

(* 0x001346c1: JMP 0x00123a40 *)
(*    1263297: JMP 0x00123a40 *)
| 0x1346c1 => Some (5,
	Jmp (Word 0x123a40 64)
)

(* 0x001346c6: MOV RCX,RDI *)
(*    1263302: MOV RCX,RDI *)
| 0x1346c6 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001346c9: AND ECX,0x7 *)
(*    1263305: AND ECX,0x7 *)
| 0x1346c9 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x7 32))) (Word 0 64)) (BinOp OP_AND (Var R_RCX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346cc: JZ 0x001346de *)
(*    1263308: JZ 0x001346de *)
| 0x1346cc => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x1346de 64)
	) (* else *) (
		Nop
	)
)

(* 0x001346ce: TEST RDX,RDX *)
(*    1263310: TEST RDX,RDX *)
| 0x1346ce => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RDX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346d1: JZ 0x00134790 *)
(*    1263313: JZ 0x00134790 *)
| 0x1346d1 => Some (6,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x134790 64)
	) (* else *) (
		Nop
	)
)

(* 0x001346d7: MOVSB RDI,RSI *)
(*    1263319: MOVSB RDI,RSI *)
| 0x1346d7 => Some (1,
	Move (V_TEMP 0x11180) (Var R_RDI) $;
	Move (V_TEMP 0x11200) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x11280) (Cast CAST_UNSIGNED 64 (Var R_DF)) $;
	Move (V_TEMP 0x11300) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 0x11280))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 0x11200)) (Var (V_TEMP 0x11300))) $;
	Move (V_TEMP 0x10580) (Var R_RSI) $;
	Move (V_TEMP 0x10600) (BinOp OP_PLUS (Var R_RSI) (Word 0x1 64)) $;
	Move (V_TEMP 0x10680) (Cast CAST_UNSIGNED 64 (Var R_DF)) $;
	Move (V_TEMP 0x10700) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 0x10680))) $;
	Move R_RSI (BinOp OP_MINUS (Var (V_TEMP 0x10600)) (Var (V_TEMP 0x10700))) $;
	Move (V_TEMP 0x10800) (Load (Var V_MEM64) (Var (V_TEMP 0x10580)) LittleE 1) $;
	Move (V_TEMP 0x11400) (Var (V_TEMP 0x10800)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x11180)) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x11400))) LittleE 1)
)

(* 0x001346d8: SUB RDX,0x1 *)
(*    1263320: SUB RDX,0x1 *)
| 0x1346d8 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RDX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346dc: JMP 0x001346c6 *)
(*    1263324: JMP 0x001346c6 *)
| 0x1346dc => Some (2,
	Jmp (Word 0x1346c6 64)
)

(* 0x001346de: MOV R9,RDX *)
(*    1263326: MOV R9,RDX *)
| 0x1346de => Some (3,
	Move R_R9 (Var R_RDX)
)

(* 0x001346e1: AND R9,-0x8 *)
(*    1263329: AND R9,-0x8 *)
| 0x1346e1 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R9 (BinOp OP_AND (Var R_R9) (Word 0xfffffffffffffff8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R9) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R9) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_R9) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x001346e5: JMP 0x0013470c *)
(*    1263333: JMP 0x0013470c *)
| 0x1346e5 => Some (2,
	Jmp (Word 0x13470c 64)
)

(* 0x00134700: MOV R8,qword ptr [RSI + RCX*0x1] *)
(*    1263360: MOV R8,qword ptr [RSI + RCX*0x1] *)
| 0x134700 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 8) $;
	Move R_R8 (Var (V_TEMP 0x11f00))
)

(* 0x00134704: MOV qword ptr [RDI + RCX*0x1],R8 *)
(*    1263364: MOV qword ptr [RDI + RCX*0x1],R8 *)
| 0x134704 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6a80) (Var R_R8) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x00134708: ADD RCX,0x8 *)
(*    1263368: ADD RCX,0x8 *)
| 0x134708 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RCX) (Word 0x8 64)) (Var R_RCX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RCX) (Word 0x8 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_PLUS (Var R_RCX) (Word 0x8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013470c: CMP RCX,R9 *)
(*    1263372: CMP RCX,R9 *)
| 0x13470c => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_R9))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R9)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R9)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R9) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R9)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013470f: JNZ 0x00134700 *)
(*    1263375: JNZ 0x00134700 *)
| 0x13470f => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x134700 64)
	) (* else *) (
		Nop
	)
)

(* 0x00134711: ADD RSI,RCX *)
(*    1263377: ADD RSI,RCX *)
| 0x134711 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) (Var R_RSI))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134714: ADD RDI,RCX *)
(*    1263380: ADD RDI,RCX *)
| 0x134714 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Var R_RCX)) (Var R_RDI))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134717: SUB RDX,RCX *)
(*    1263383: SUB RDX,RCX *)
| 0x134717 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RDX) (Var R_RCX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013471a: JMP 0x001346ba *)
(*    1263386: JMP 0x001346ba *)
| 0x13471a => Some (2,
	Jmp (Word 0x1346ba 64)
)

(* 0x00134720: MOVZX R8D,byte ptr [RSI + RCX*0x1] *)
(*    1263392: MOVZX R8D,byte ptr [RSI + RCX*0x1] *)
| 0x134720 => Some (5,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x00134725: MOV byte ptr [RDI + RCX*0x1],R8B *)
(*    1263397: MOV byte ptr [RDI + RCX*0x1],R8B *)
| 0x134725 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6900) (Extract 7 0 (Var R_R8)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x6900))) LittleE 1)
)

(* 0x00134729: ADD RCX,0x1 *)
(*    1263401: ADD RCX,0x1 *)
| 0x134729 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_RCX) (Word 0x1 64)) (Var R_RCX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RCX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_PLUS (Var R_RCX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013472d: CMP RDX,RCX *)
(*    1263405: CMP RDX,RCX *)
| 0x13472d => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_RCX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134730: JNZ 0x00134720 *)
(*    1263408: JNZ 0x00134720 *)
| 0x134730 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x134720 64)
	) (* else *) (
		Nop
	)
)

(* 0x00134732: RET *)
(*    1263410: RET *)
| 0x134732 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00134733: AND ECX,0x7 *)
(*    1263411: AND ECX,0x7 *)
| 0x134733 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x7 32))) (Word 0 64)) (BinOp OP_AND (Var R_RCX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134736: JNZ 0x0013478b *)
(*    1263414: JNZ 0x0013478b *)
| 0x134736 => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x13478b 64)
	) (* else *) (
		Nop
	)
)

(* 0x00134738: LEA RCX,[RAX + RDX*0x1] *)
(*    1263416: LEA RCX,[RAX + RDX*0x1] *)
| 0x134738 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4980))) $;
	Move R_RCX (Var (V_TEMP 0x4a80))
)

(* 0x0013473c: AND ECX,0x7 *)
(*    1263420: AND ECX,0x7 *)
| 0x13473c => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x7 32))) (Word 0 64)) (BinOp OP_AND (Var R_RCX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013473f: JZ 0x00134753 *)
(*    1263423: JZ 0x00134753 *)
| 0x13473f => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x134753 64)
	) (* else *) (
		Nop
	)
)

(* 0x00134741: TEST RDX,RDX *)
(*    1263425: TEST RDX,RDX *)
| 0x134741 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RDX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134744: JZ 0x00134790 *)
(*    1263428: JZ 0x00134790 *)
| 0x134744 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x134790 64)
	) (* else *) (
		Nop
	)
)

(* 0x00134746: SUB RDX,0x1 *)
(*    1263430: SUB RDX,0x1 *)
| 0x134746 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RDX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013474a: MOVZX ECX,byte ptr [RSI + RDX*0x1] *)
(*    1263434: MOVZX ECX,byte ptr [RSI + RDX*0x1] *)
| 0x13474a => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x0013474e: MOV byte ptr [RAX + RDX*0x1],CL *)
(*    1263438: MOV byte ptr [RAX + RDX*0x1],CL *)
| 0x13474e => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6900) (Extract 7 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x6900))) LittleE 1)
)

(* 0x00134751: JMP 0x00134738 *)
(*    1263441: JMP 0x00134738 *)
| 0x134751 => Some (2,
	Jmp (Word 0x134738 64)
)

(* 0x00134753: MOV R8,RDX *)
(*    1263443: MOV R8,RDX *)
| 0x134753 => Some (3,
	Move R_R8 (Var R_RDX)
)

(* 0x00134756: MOV RCX,RDX *)
(*    1263446: MOV RCX,RDX *)
| 0x134756 => Some (3,
	Move R_RCX (Var R_RDX)
)

(* 0x00134759: AND R8D,0x7 *)
(*    1263449: AND R8D,0x7 *)
| 0x134759 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R8 (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_R8)) (Word 0x7 32))) (Word 0 64)) (BinOp OP_AND (Var R_R8) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_R8)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_R8)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_R8)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013475d: JMP 0x0013476c *)
(*    1263453: JMP 0x0013476c *)
| 0x13475d => Some (2,
	Jmp (Word 0x13476c 64)
)

(* 0x00134760: SUB RCX,0x8 *)
(*    1263456: SUB RCX,0x8 *)
| 0x134760 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RCX) (Word 0x8 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Word 0x8 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Word 0x8 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134764: MOV RDI,qword ptr [RSI + RCX*0x1] *)
(*    1263460: MOV RDI,qword ptr [RSI + RCX*0x1] *)
| 0x134764 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x11f00))
)

(* 0x00134768: MOV qword ptr [RAX + RCX*0x1],RDI *)
(*    1263464: MOV qword ptr [RAX + RCX*0x1],RDI *)
| 0x134768 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6a80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a80))) LittleE 8)
)

(* 0x0013476c: CMP RCX,R8 *)
(*    1263468: CMP RCX,R8 *)
| 0x13476c => Some (3,
	Move (V_TEMP 0x3f000) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x3f000)) (Var R_R8))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f000)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R8)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R8)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f100) (BinOp OP_MINUS (Var (V_TEMP 0x3f000)) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x3f100)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x3f100)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013476f: JNZ 0x00134760 *)
(*    1263471: JNZ 0x00134760 *)
| 0x13476f => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x134760 64)
	) (* else *) (
		Nop
	)
)

(* 0x00134771: AND EDX,0x7 *)
(*    1263473: AND EDX,0x7 *)
| 0x134771 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x7 32))) (Word 0 64)) (BinOp OP_AND (Var R_RDX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134774: JMP 0x0013478b *)
(*    1263476: JMP 0x0013478b *)
| 0x134774 => Some (2,
	Jmp (Word 0x13478b 64)
)

(* 0x00134780: SUB RDX,0x1 *)
(*    1263488: SUB RDX,0x1 *)
| 0x134780 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_RDX) (Word 0x1 64))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x00134784: MOVZX ECX,byte ptr [RSI + RDX*0x1] *)
(*    1263492: MOVZX ECX,byte ptr [RSI + RDX*0x1] *)
| 0x134784 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSI) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x11d80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x11d80))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00134788: MOV byte ptr [RAX + RDX*0x1],CL *)
(*    1263496: MOV byte ptr [RAX + RDX*0x1],CL *)
| 0x134788 => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6900) (Extract 7 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x6900))) LittleE 1)
)

(* 0x0013478b: TEST RDX,RDX *)
(*    1263499: TEST RDX,RDX *)
| 0x13478b => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var R_RDX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c180) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c200) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c180)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x2c200)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x2c280)) (Word 0x0 8)))
)

(* 0x0013478e: JNZ 0x00134780 *)
(*    1263502: JNZ 0x00134780 *)
| 0x13478e => Some (2,
	Move (V_TEMP 0x12780) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x134780 64)
	) (* else *) (
		Nop
	)
)

(* 0x00134790: RET *)
(*    1263504: RET *)
| 0x134790 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx memmove_amd64.
Proof. Picinae_typecheck. Qed.

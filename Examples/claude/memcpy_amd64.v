(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: memcpy at 0x1c4870
function: FUN_001c4980 at 0x1c4980
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition memcpy_amd64 : program := fun _ a => match a with

(* ---- memcpy ---- *)

(* 0x001c4870: ENDBR64 *)
(*    1853552: ENDBR64 *)
| 0x1c4870 => Some (4,
	Nop
)

(* 0x001c4874: MOV RAX,RDI *)
(*    1853556: MOV RAX,RDI *)
| 0x1c4874 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x001c4877: CMP RDX,0x10 *)
(*    1853559: CMP RDX,0x10 *)
| 0x1c4877 => Some (4,
	Move (V_TEMP 0x3eb00) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3eb00)) (Word 0x10 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3eb00)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x10 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3ec00) (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ec00)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c487b: JC 0x001c49b0 *)
(*    1853563: JC 0x001c49b0 *)
| 0x1c487b => Some (6,
	If (Var R_CF) (
		Jmp (Word 0x1c49b0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4881: MOVUPS XMM0,xmmword ptr [RSI] *)
(*    1853569: MOVUPS XMM0,xmmword ptr [RSI] *)
| 0x1c4881 => Some (3,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x001c4884: CMP RDX,0x20 *)
(*    1853572: CMP RDX,0x20 *)
| 0x1c4884 => Some (4,
	Move (V_TEMP 0x3eb00) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3eb00)) (Word 0x20 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3eb00)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x20 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x20 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3ec00) (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x20 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ec00)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4888: JA 0x001c4a1d *)
(*    1853576: JA 0x001c4a1d *)
| 0x1c4888 => Some (6,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4a1d 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c488e: MOVUPS XMM1,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*    1853582: MOVUPS XMM1,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x1c488e => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4893: MOVUPS xmmword ptr [RDI],XMM0 *)
(*    1853587: MOVUPS xmmword ptr [RDI],XMM0 *)
| 0x1c4893 => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4896: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM1 *)
(*    1853590: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM1 *)
| 0x1c4896 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c489b: RET *)
(*    1853595: RET *)
| 0x1c489b => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* ---- FUN_001c4980 ---- *)

(* 0x001c4980: ENDBR64 *)
(*    1853824: ENDBR64 *)
| 0x1c4980 => Some (4,
	Nop
)

(* 0x001c4984: MOV RAX,RDI *)
(*    1853828: MOV RAX,RDI *)
| 0x1c4984 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x001c4987: CMP RDX,0x10 *)
(*    1853831: CMP RDX,0x10 *)
| 0x1c4987 => Some (4,
	Move (V_TEMP 0x3eb00) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3eb00)) (Word 0x10 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3eb00)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x10 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3ec00) (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ec00)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c498b: JC 0x001c49b0 *)
(*    1853835: JC 0x001c49b0 *)
| 0x1c498b => Some (2,
	If (Var R_CF) (
		Jmp (Word 0x1c49b0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c498d: MOVUPS XMM0,xmmword ptr [RSI] *)
(*    1853837: MOVUPS XMM0,xmmword ptr [RSI] *)
| 0x1c498d => Some (3,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x001c4990: CMP RDX,0x20 *)
(*    1853840: CMP RDX,0x20 *)
| 0x1c4990 => Some (4,
	Move (V_TEMP 0x3eb00) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3eb00)) (Word 0x20 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3eb00)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x20 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x20 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3ec00) (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x20 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ec00)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4994: JA 0x001c4a10 *)
(*    1853844: JA 0x001c4a10 *)
| 0x1c4994 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4a10 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4996: MOVUPS XMM1,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*    1853846: MOVUPS XMM1,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x1c4996 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c499b: MOVUPS xmmword ptr [RDI],XMM0 *)
(*    1853851: MOVUPS xmmword ptr [RDI],XMM0 *)
| 0x1c499b => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c499e: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM1 *)
(*    1853854: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM1 *)
| 0x1c499e => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c49a3: RET *)
(*    1853859: RET *)
| 0x1c49a3 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c49b0: CMP EDX,0x8 *)
(*    1853872: CMP EDX,0x8 *)
| 0x1c49b0 => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x8 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x8 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x8 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x8 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c49b3: JNC 0x001c49e0 *)
(*    1853875: JNC 0x001c49e0 *)
| 0x1c49b3 => Some (2,
	Move (V_TEMP 0x12780) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x1c49e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c49b5: CMP EDX,0x4 *)
(*    1853877: CMP EDX,0x4 *)
| 0x1c49b5 => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x4 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x4 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x4 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c49b8: JNC 0x001c49d0 *)
(*    1853880: JNC 0x001c49d0 *)
| 0x1c49b8 => Some (2,
	Move (V_TEMP 0x12780) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x1c49d0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c49ba: CMP EDX,0x1 *)
(*    1853882: CMP EDX,0x1 *)
| 0x1c49ba => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c49bd: JL 0x001c49cf *)
(*    1853885: JL 0x001c49cf *)
| 0x1c49bd => Some (2,
	Move (V_TEMP 0x12e00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12e00))) (
		Jmp (Word 0x1c49cf 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c49bf: MOV CL,byte ptr [RSI] *)
(*    1853887: MOV CL,byte ptr [RSI] *)
| 0x1c49bf => Some (2,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RSI) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c49c1: JZ 0x001c49cd *)
(*    1853889: JZ 0x001c49cd *)
| 0x1c49c1 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c49cd 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c49c3: MOVZX ESI,word ptr [RSI + RDX*0x1 + -0x2] *)
(*    1853891: MOVZX ESI,word ptr [RSI + RDX*0x1 + -0x2] *)
| 0x1c49c3 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffffe 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x11f00) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 2) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x11f00)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001c49c8: MOV word ptr [RDI + RDX*0x1 + -0x2],SI *)
(*    1853896: MOV word ptr [RDI + RDX*0x1 + -0x2],SI *)
| 0x1c49c8 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffffe 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RSI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x001c49cd: MOV byte ptr [RDI],CL *)
(*    1853901: MOV byte ptr [RDI],CL *)
| 0x1c49cd => Some (2,
	Move (V_TEMP 0x6a00) (Extract 7 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6a00)) LittleE 1)
)

(* 0x001c49cf: RET *)
(*    1853903: RET *)
| 0x1c49cf => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c49d0: MOV ECX,dword ptr [RSI + RDX*0x1 + -0x4] *)
(*    1853904: MOV ECX,dword ptr [RSI + RDX*0x1 + -0x4] *)
| 0x1c49d0 => Some (4,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffffc 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 4) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001c49d4: MOV ESI,dword ptr [RSI] *)
(*    1853908: MOV ESI,dword ptr [RSI] *)
| 0x1c49d4 => Some (2,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RSI) LittleE 4) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0x11f80))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001c49d6: MOV dword ptr [RDI + RDX*0x1 + -0x4],ECX *)
(*    1853910: MOV dword ptr [RDI + RDX*0x1 + -0x4],ECX *)
| 0x1c49d6 => Some (4,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffffc 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x001c49da: MOV dword ptr [RDI],ESI *)
(*    1853914: MOV dword ptr [RDI],ESI *)
| 0x1c49da => Some (2,
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RSI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x001c49dc: RET *)
(*    1853916: RET *)
| 0x1c49dc => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c49e0: MOV RCX,qword ptr [RSI + RDX*0x1 + -0x8] *)
(*    1853920: MOV RCX,qword ptr [RSI + RDX*0x1 + -0x8] *)
| 0x1c49e0 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff8 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 8) $;
	Move R_RCX (Var (V_TEMP 0x12000))
)

(* 0x001c49e5: MOV RSI,qword ptr [RSI] *)
(*    1853925: MOV RSI,qword ptr [RSI] *)
| 0x1c49e5 => Some (3,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	Move R_RSI (Var (V_TEMP 0x12000))
)

(* 0x001c49e8: MOV qword ptr [RDI],RSI *)
(*    1853928: MOV qword ptr [RDI],RSI *)
| 0x1c49e8 => Some (3,
	Move (V_TEMP 0x6b80) (Var R_RSI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x001c49eb: MOV qword ptr [RDI + RDX*0x1 + -0x8],RCX *)
(*    1853931: MOV qword ptr [RDI + RDX*0x1 + -0x8],RCX *)
| 0x1c49eb => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff8 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6b80) (Var R_RCX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x001c49f0: RET *)
(*    1853936: RET *)
| 0x1c49f0 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c49f1: MOVUPS XMM2,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*    1853937: MOVUPS XMM2,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x1c49f1 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c49f6: MOVUPS XMM3,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
(*    1853942: MOVUPS XMM3,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x1c49f6 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c49fb: MOVUPS xmmword ptr [RDI],XMM0 *)
(*    1853947: MOVUPS xmmword ptr [RDI],XMM0 *)
| 0x1c49fb => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c49fe: MOVUPS xmmword ptr [RDI + 0x10],XMM1 *)
(*    1853950: MOVUPS xmmword ptr [RDI + 0x10],XMM1 *)
| 0x1c49fe => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a02: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM2 *)
(*    1853954: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM2 *)
| 0x1c4a02 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a07: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x20],XMM3 *)
(*    1853959: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x20],XMM3 *)
| 0x1c4a07 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a0c: RET *)
(*    1853964: RET *)
| 0x1c4a0c => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c4a10: CMP RDX,qword ptr [0x0031a3f8] *)
(*    1853968: CMP RDX,qword ptr [0x0031a3f8] *)
| 0x1c4a10 => Some (7,
	Move (V_TEMP 0x3f880) (Load (Var V_MEM64) (Word 0x31a3f8 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var (V_TEMP 0x3f880))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f880)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f980) (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f980)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4a17: JA 0x001c4b81 *)
(*    1853975: JA 0x001c4b81 *)
| 0x1c4a17 => Some (6,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4b81 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4a1d: CMP RDX,0x80 *)
(*    1853981: CMP RDX,0x80 *)
| 0x1c4a1d => Some (7,
	Move (V_TEMP 0x3e680) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e680)) (Word 0x80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e680)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0x80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0x80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3e780) (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0x80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e780)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e780)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e780)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4a24: JA 0x001c4a70 *)
(*    1853988: JA 0x001c4a70 *)
| 0x1c4a24 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4a70 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4a26: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
(*    1853990: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
| 0x1c4a26 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4a2a: CMP RDX,0x40 *)
(*    1853994: CMP RDX,0x40 *)
| 0x1c4a2a => Some (4,
	Move (V_TEMP 0x3eb00) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3eb00)) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3eb00)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3ec00) (BinOp OP_MINUS (Var (V_TEMP 0x3eb00)) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ec00)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ec00)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4a2e: JBE 0x001c49f1 *)
(*    1853998: JBE 0x001c49f1 *)
| 0x1c4a2e => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1c49f1 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4a30: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
(*    1854000: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
| 0x1c4a30 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4a34: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
(*    1854004: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
| 0x1c4a34 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4a38: MOVUPS XMM4,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*    1854008: MOVUPS XMM4,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x1c4a38 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM4))))
)

(* 0x001c4a3d: MOVUPS XMM5,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
(*    1854013: MOVUPS XMM5,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x1c4a3d => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM5 (Concat (Extract 255 32 (Var R_YMM5)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM5 (Concat (Extract 255 64 (Var R_YMM5)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 96 (Var R_YMM5)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM5))))
)

(* 0x001c4a42: MOVUPS XMM6,xmmword ptr [RSI + RDX*0x1 + -0x30] *)
(*    1854018: MOVUPS XMM6,xmmword ptr [RSI + RDX*0x1 + -0x30] *)
| 0x1c4a42 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffd0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM6 (Concat (Extract 255 32 (Var R_YMM6)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM6 (Concat (Extract 255 64 (Var R_YMM6)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 96 (Var R_YMM6)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM6))))
)

(* 0x001c4a47: MOVUPS XMM7,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
(*    1854023: MOVUPS XMM7,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x1c4a47 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM7 (Concat (Extract 255 32 (Var R_YMM7)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM7 (Concat (Extract 255 64 (Var R_YMM7)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 96 (Var R_YMM7)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM7))))
)

(* 0x001c4a4c: MOVUPS xmmword ptr [RDI],XMM0 *)
(*    1854028: MOVUPS xmmword ptr [RDI],XMM0 *)
| 0x1c4a4c => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a4f: MOVUPS xmmword ptr [RDI + 0x10],XMM1 *)
(*    1854031: MOVUPS xmmword ptr [RDI + 0x10],XMM1 *)
| 0x1c4a4f => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a53: MOVUPS xmmword ptr [RDI + 0x20],XMM2 *)
(*    1854035: MOVUPS xmmword ptr [RDI + 0x20],XMM2 *)
| 0x1c4a53 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a57: MOVUPS xmmword ptr [RDI + 0x30],XMM3 *)
(*    1854039: MOVUPS xmmword ptr [RDI + 0x30],XMM3 *)
| 0x1c4a57 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a5b: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM4 *)
(*    1854043: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM4 *)
| 0x1c4a5b => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM4)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a60: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x20],XMM5 *)
(*    1854048: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x20],XMM5 *)
| 0x1c4a60 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM5)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a65: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x30],XMM6 *)
(*    1854053: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x30],XMM6 *)
| 0x1c4a65 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffd0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM6)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a6a: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x40],XMM7 *)
(*    1854058: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x40],XMM7 *)
| 0x1c4a6a => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM7)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4a6f: RET *)
(*    1854063: RET *)
| 0x1c4a6f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c4a70: MOV RCX,RDI *)
(*    1854064: MOV RCX,RDI *)
| 0x1c4a70 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001c4a73: SUB RCX,RSI *)
(*    1854067: SUB RCX,RSI *)
| 0x1c4a73 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RCX) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4a76: CMP RCX,RDX *)
(*    1854070: CMP RCX,RDX *)
| 0x1c4a76 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4a79: JC 0x001c4b10 *)
(*    1854073: JC 0x001c4b10 *)
| 0x1c4a79 => Some (6,
	If (Var R_CF) (
		Jmp (Word 0x1c4b10 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4a7f: CMP RDX,qword ptr [0x003215a8] *)
(*    1854079: CMP RDX,qword ptr [0x003215a8] *)
| 0x1c4a7f => Some (7,
	Move (V_TEMP 0x3f880) (Load (Var V_MEM64) (Word 0x3215a8 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var (V_TEMP 0x3f880))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f880)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f980) (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f980)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4a86: JA 0x001c4bad *)
(*    1854086: JA 0x001c4bad *)
| 0x1c4a86 => Some (6,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4bad 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4a8c: LEA R8,[RCX + RDX*0x1] *)
(*    1854092: LEA R8,[RCX + RDX*0x1] *)
| 0x1c4a8c => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RCX) (Var (V_TEMP 0x4980))) $;
	Move R_R8 (Var (V_TEMP 0x4a80))
)

(* 0x001c4a90: XOR R8,RCX *)
(*    1854096: XOR R8,RCX *)
| 0x1c4a90 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R8 (BinOp OP_XOR (Var R_R8) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R8) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R8) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4a93: SHR R8,0x3f *)
(*    1854099: SHR R8,0x3f *)
| 0x1c4a93 => Some (4,
	Move (V_TEMP 0x6e800) (BinOp OP_AND (Word 0x3f 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6e880) (Var R_R8) $;
	Move R_R8 (BinOp OP_RSHIFT (Var R_R8) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e800)))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e880)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e800)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e880)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R8) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R8) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001c4a97: AND ECX,0xf00 *)
(*    1854103: AND ECX,0xf00 *)
| 0x1c4a97 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xf00 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4a9d: ADD ECX,R8D *)
(*    1854109: ADD ECX,R8D *)
| 0x1c4a9d => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_R8))) (Extract 31 0 (Var R_RCX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_R8))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_R8)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_R8)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4aa0: JZ 0x001c4b15 *)
(*    1854112: JZ 0x001c4b15 *)
| 0x1c4aa0 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c4b15 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4aa2: MOVUPS XMM5,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*    1854114: MOVUPS XMM5,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x1c4aa2 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM5 (Concat (Extract 255 32 (Var R_YMM5)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM5 (Concat (Extract 255 64 (Var R_YMM5)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 96 (Var R_YMM5)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM5))))
)

(* 0x001c4aa7: MOVUPS XMM6,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
(*    1854119: MOVUPS XMM6,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x1c4aa7 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM6 (Concat (Extract 255 32 (Var R_YMM6)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM6 (Concat (Extract 255 64 (Var R_YMM6)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 96 (Var R_YMM6)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM6))))
)

(* 0x001c4aac: MOV RCX,RDI *)
(*    1854124: MOV RCX,RDI *)
| 0x1c4aac => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001c4aaf: OR RDI,0xf *)
(*    1854127: OR RDI,0xf *)
| 0x1c4aaf => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_OR (Var R_RDI) (Word 0xf 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ab3: MOVUPS XMM7,xmmword ptr [RSI + RDX*0x1 + -0x30] *)
(*    1854131: MOVUPS XMM7,xmmword ptr [RSI + RDX*0x1 + -0x30] *)
| 0x1c4ab3 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffd0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM7 (Concat (Extract 255 32 (Var R_YMM7)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM7 (Concat (Extract 255 64 (Var R_YMM7)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 96 (Var R_YMM7)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM7))))
)

(* 0x001c4ab8: MOVUPS XMM8,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
(*    1854136: MOVUPS XMM8,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x1c4ab8 => Some (6,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM8 (Concat (Extract 255 32 (Var R_YMM8)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM8 (Concat (Extract 255 64 (Var R_YMM8)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM8)))) $;
	Move R_YMM8 (Concat (Extract 255 96 (Var R_YMM8)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM8)))) $;
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM8))))
)

(* 0x001c4abe: SUB RSI,RCX *)
(*    1854142: SUB RSI,RCX *)
| 0x1c4abe => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ac1: INC RDI *)
(*    1854145: INC RDI *)
| 0x1c4ac1 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ac4: ADD RSI,RDI *)
(*    1854148: ADD RSI,RDI *)
| 0x1c4ac4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ac7: LEA RDX,[RCX + RDX*0x1 + -0x40] *)
(*    1854151: LEA RDX,[RCX + RDX*0x1 + -0x40] *)
| 0x1c4ac7 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RCX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RDX (Var (V_TEMP 0x5080))
)

(* 0x001c4acc: NOP dword ptr [RAX] *)
(*    1854156: NOP dword ptr [RAX] *)
| 0x1c4acc => Some (4,
	Nop
)

(* 0x001c4ad0: MOVUPS XMM1,xmmword ptr [RSI] *)
(*    1854160: MOVUPS XMM1,xmmword ptr [RSI] *)
| 0x1c4ad0 => Some (3,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4ad3: MOVUPS XMM2,xmmword ptr [RSI + 0x10] *)
(*    1854163: MOVUPS XMM2,xmmword ptr [RSI + 0x10] *)
| 0x1c4ad3 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4ad7: MOVUPS XMM3,xmmword ptr [RSI + 0x20] *)
(*    1854167: MOVUPS XMM3,xmmword ptr [RSI + 0x20] *)
| 0x1c4ad7 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4adb: MOVUPS XMM4,xmmword ptr [RSI + 0x30] *)
(*    1854171: MOVUPS XMM4,xmmword ptr [RSI + 0x30] *)
| 0x1c4adb => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM4))))
)

(* 0x001c4adf: SUB RSI,-0x40 *)
(*    1854175: SUB RSI,-0x40 *)
| 0x1c4adf => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ae3: MOVAPS xmmword ptr [RDI],XMM1 *)
(*    1854179: MOVAPS xmmword ptr [RDI],XMM1 *)
| 0x1c4ae3 => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4ae6: MOVAPS xmmword ptr [RDI + 0x10],XMM2 *)
(*    1854182: MOVAPS xmmword ptr [RDI + 0x10],XMM2 *)
| 0x1c4ae6 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4aea: MOVAPS xmmword ptr [RDI + 0x20],XMM3 *)
(*    1854186: MOVAPS xmmword ptr [RDI + 0x20],XMM3 *)
| 0x1c4aea => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4aee: MOVAPS xmmword ptr [RDI + 0x30],XMM4 *)
(*    1854190: MOVAPS xmmword ptr [RDI + 0x30],XMM4 *)
| 0x1c4aee => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM4)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4af2: SUB RDI,-0x40 *)
(*    1854194: SUB RDI,-0x40 *)
| 0x1c4af2 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4af6: CMP RDX,RDI *)
(*    1854198: CMP RDX,RDI *)
| 0x1c4af6 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4af9: JA 0x001c4ad0 *)
(*    1854201: JA 0x001c4ad0 *)
| 0x1c4af9 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4ad0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4afb: MOVUPS xmmword ptr [RDX + 0x30],XMM5 *)
(*    1854203: MOVUPS xmmword ptr [RDX + 0x30],XMM5 *)
| 0x1c4afb => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM5)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4aff: MOVUPS xmmword ptr [RDX + 0x20],XMM6 *)
(*    1854207: MOVUPS xmmword ptr [RDX + 0x20],XMM6 *)
| 0x1c4aff => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM6)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b03: MOVUPS xmmword ptr [RDX + 0x10],XMM7 *)
(*    1854211: MOVUPS xmmword ptr [RDX + 0x10],XMM7 *)
| 0x1c4b03 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM7)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b07: MOVUPS xmmword ptr [RDX],XMM8 *)
(*    1854215: MOVUPS xmmword ptr [RDX],XMM8 *)
| 0x1c4b07 => Some (4,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM8)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDX) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b0b: MOVUPS xmmword ptr [RCX],XMM0 *)
(*    1854219: MOVUPS xmmword ptr [RCX],XMM0 *)
| 0x1c4b0b => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RCX) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b0e: RET *)
(*    1854222: RET *)
| 0x1c4b0e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c4b10: TEST RCX,RCX *)
(*    1854224: TEST RCX,RCX *)
| 0x1c4b10 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RCX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b13: JZ 0x001c4b0e *)
(*    1854227: JZ 0x001c4b0e *)
| 0x1c4b13 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c4b0e 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4b15: MOVUPS XMM5,xmmword ptr [RSI + 0x10] *)
(*    1854229: MOVUPS XMM5,xmmword ptr [RSI + 0x10] *)
| 0x1c4b15 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM5 (Concat (Extract 255 32 (Var R_YMM5)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM5 (Concat (Extract 255 64 (Var R_YMM5)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 96 (Var R_YMM5)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM5))))
)

(* 0x001c4b19: MOVUPS XMM6,xmmword ptr [RSI + 0x20] *)
(*    1854233: MOVUPS XMM6,xmmword ptr [RSI + 0x20] *)
| 0x1c4b19 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM6 (Concat (Extract 255 32 (Var R_YMM6)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM6 (Concat (Extract 255 64 (Var R_YMM6)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 96 (Var R_YMM6)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM6))))
)

(* 0x001c4b1d: LEA RCX,[RDI + RDX*0x1 + -0x41] *)
(*    1854237: LEA RCX,[RDI + RDX*0x1 + -0x41] *)
| 0x1c4b1d => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffbf 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RCX (Var (V_TEMP 0x5080))
)

(* 0x001c4b22: MOVUPS XMM7,xmmword ptr [RSI + 0x30] *)
(*    1854242: MOVUPS XMM7,xmmword ptr [RSI + 0x30] *)
| 0x1c4b22 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM7 (Concat (Extract 255 32 (Var R_YMM7)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM7 (Concat (Extract 255 64 (Var R_YMM7)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 96 (Var R_YMM7)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM7))))
)

(* 0x001c4b26: MOVUPS XMM8,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*    1854246: MOVUPS XMM8,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x1c4b26 => Some (6,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM8 (Concat (Extract 255 32 (Var R_YMM8)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM8 (Concat (Extract 255 64 (Var R_YMM8)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM8)))) $;
	Move R_YMM8 (Concat (Extract 255 96 (Var R_YMM8)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM8)))) $;
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM8))))
)

(* 0x001c4b2c: SUB RSI,RDI *)
(*    1854252: SUB RSI,RDI *)
| 0x1c4b2c => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b2f: AND RCX,-0x10 *)
(*    1854255: AND RCX,-0x10 *)
| 0x1c4b2f => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_AND (Var R_RCX) (Word 0xfffffffffffffff0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b33: ADD RSI,RCX *)
(*    1854259: ADD RSI,RCX *)
| 0x1c4b33 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b36: NOP word ptr CS:[RAX + RAX*0x1] *)
(*    1854262: NOP word ptr CS:[RAX + RAX*0x1] *)
| 0x1c4b36 => Some (10,
	Move (V_TEMP 0x5580) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5680) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5580)))
)

(* 0x001c4b40: MOVUPS XMM1,xmmword ptr [RSI + 0x30] *)
(*    1854272: MOVUPS XMM1,xmmword ptr [RSI + 0x30] *)
| 0x1c4b40 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4b44: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
(*    1854276: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
| 0x1c4b44 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4b48: MOVUPS XMM3,xmmword ptr [RSI + 0x10] *)
(*    1854280: MOVUPS XMM3,xmmword ptr [RSI + 0x10] *)
| 0x1c4b48 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4b4c: MOVUPS XMM4,xmmword ptr [RSI] *)
(*    1854284: MOVUPS XMM4,xmmword ptr [RSI] *)
| 0x1c4b4c => Some (3,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM4))))
)

(* 0x001c4b4f: ADD RSI,-0x40 *)
(*    1854287: ADD RSI,-0x40 *)
| 0x1c4b4f => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b53: MOVAPS xmmword ptr [RCX + 0x30],XMM1 *)
(*    1854291: MOVAPS xmmword ptr [RCX + 0x30],XMM1 *)
| 0x1c4b53 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RCX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b57: MOVAPS xmmword ptr [RCX + 0x20],XMM2 *)
(*    1854295: MOVAPS xmmword ptr [RCX + 0x20],XMM2 *)
| 0x1c4b57 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RCX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b5b: MOVAPS xmmword ptr [RCX + 0x10],XMM3 *)
(*    1854299: MOVAPS xmmword ptr [RCX + 0x10],XMM3 *)
| 0x1c4b5b => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RCX) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b5f: MOVAPS xmmword ptr [RCX],XMM4 *)
(*    1854303: MOVAPS xmmword ptr [RCX],XMM4 *)
| 0x1c4b5f => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM4)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RCX) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b62: ADD RCX,-0x40 *)
(*    1854306: ADD RCX,-0x40 *)
| 0x1c4b62 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RCX) (Word 0xffffffffffffffc0 64)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RCX) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_PLUS (Var R_RCX) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b66: CMP RDI,RCX *)
(*    1854310: CMP RDI,RCX *)
| 0x1c4b66 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RDI) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b69: JC 0x001c4b40 *)
(*    1854313: JC 0x001c4b40 *)
| 0x1c4b69 => Some (2,
	If (Var R_CF) (
		Jmp (Word 0x1c4b40 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4b6b: MOVUPS xmmword ptr [RDI],XMM0 *)
(*    1854315: MOVUPS xmmword ptr [RDI],XMM0 *)
| 0x1c4b6b => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b6e: MOVUPS xmmword ptr [RDI + 0x10],XMM5 *)
(*    1854318: MOVUPS xmmword ptr [RDI + 0x10],XMM5 *)
| 0x1c4b6e => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM5)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b72: MOVUPS xmmword ptr [RDI + 0x20],XMM6 *)
(*    1854322: MOVUPS xmmword ptr [RDI + 0x20],XMM6 *)
| 0x1c4b72 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM6)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b76: MOVUPS xmmword ptr [RDI + 0x30],XMM7 *)
(*    1854326: MOVUPS xmmword ptr [RDI + 0x30],XMM7 *)
| 0x1c4b76 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM7)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b7a: MOVUPS xmmword ptr [RDX + RDI*0x1 + -0x10],XMM8 *)
(*    1854330: MOVUPS xmmword ptr [RDX + RDI*0x1 + -0x10],XMM8 *)
| 0x1c4b7a => Some (6,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM8)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4b80: RET *)
(*    1854336: RET *)
| 0x1c4b80 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c4b81: MOV RCX,RDI *)
(*    1854337: MOV RCX,RDI *)
| 0x1c4b81 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001c4b84: SUB RCX,RSI *)
(*    1854340: SUB RCX,RSI *)
| 0x1c4b84 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RCX) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b87: CMP RCX,RDX *)
(*    1854343: CMP RCX,RDX *)
| 0x1c4b87 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b8a: JC 0x001c4b10 *)
(*    1854346: JC 0x001c4b10 *)
| 0x1c4b8a => Some (2,
	If (Var R_CF) (
		Jmp (Word 0x1c4b10 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4b8c: CMP RDX,qword ptr [0x003215a0] *)
(*    1854348: CMP RDX,qword ptr [0x003215a0] *)
| 0x1c4b8c => Some (7,
	Move (V_TEMP 0x3f880) (Load (Var V_MEM64) (Word 0x3215a0 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var (V_TEMP 0x3f880))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f880)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f980) (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f980)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4b93: JNC 0x001c4ba0 *)
(*    1854355: JNC 0x001c4ba0 *)
| 0x1c4b93 => Some (2,
	Move (V_TEMP 0x12780) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x1c4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4b95: MOV RCX,RDX *)
(*    1854357: MOV RCX,RDX *)
| 0x1c4b95 => Some (3,
	Move R_RCX (Var R_RDX)
)

(* 0x001c4b98: MOVSB.REP RDI,RSI *)
(*    1854360: MOVSB.REP RDI,RSI *)
| 0x1c4b98 => Some (2,
	Move (V_TEMP 0x13500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13500))) (
		Jmp (Word 0x1c4b9a 64)
	) (* else *) (
		Nop
	) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x11280) (Var R_RDI) $;
	Move (V_TEMP 0x11300) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x11380) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 0x11400) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 0x11380))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 0x11300)) (Var (V_TEMP 0x11400))) $;
	Move (V_TEMP 0x10680) (Var R_RSI) $;
	Move (V_TEMP 0x10700) (BinOp OP_PLUS (Var R_RSI) (Word 0x1 64)) $;
	Move (V_TEMP 0x10780) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 0x10800) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 0x10780))) $;
	Move R_RSI (BinOp OP_MINUS (Var (V_TEMP 0x10700)) (Var (V_TEMP 0x10800))) $;
	Move (V_TEMP 0x10900) (Load (Var V_MEM64) (Var (V_TEMP 0x10680)) LittleE 1) $;
	Move (V_TEMP 0x11500) (Var (V_TEMP 0x10900)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x11280)) (Var (V_TEMP 0x11500)) LittleE 1) $;
	Jmp (Word 0x1c4b98 64)
)

(* 0x001c4b9a: RET *)
(*    1854362: RET *)
| 0x1c4b9a => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c4ba0: CMP RDX,qword ptr [0x0031a3f8] *)
(*    1854368: CMP RDX,qword ptr [0x0031a3f8] *)
| 0x1c4ba0 => Some (7,
	Move (V_TEMP 0x3f880) (Load (Var V_MEM64) (Word 0x31a3f8 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var (V_TEMP 0x3f880))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f880)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f980) (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0x3f880))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f980)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ba7: JC 0x001c4a8c *)
(*    1854375: JC 0x001c4a8c *)
| 0x1c4ba7 => Some (6,
	If (Var R_CF) (
		Jmp (Word 0x1c4a8c 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4bad: NEG RCX *)
(*    1854381: NEG RCX *)
| 0x1c4bad => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_RCX) (Word 0x0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 64) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 64) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 64) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (UnOp OP_NEG (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4bb0: CMP RDX,RCX *)
(*    1854384: CMP RDX,RCX *)
| 0x1c4bb0 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4bb3: JA 0x001c4aa2 *)
(*    1854387: JA 0x001c4aa2 *)
| 0x1c4bb3 => Some (6,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4aa2 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4bb9: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
(*    1854393: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
| 0x1c4bb9 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4bbd: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
(*    1854397: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
| 0x1c4bbd => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4bc1: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
(*    1854401: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
| 0x1c4bc1 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4bc5: MOVUPS xmmword ptr [RDI],XMM0 *)
(*    1854405: MOVUPS xmmword ptr [RDI],XMM0 *)
| 0x1c4bc5 => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4bc8: MOVUPS xmmword ptr [RDI + 0x10],XMM1 *)
(*    1854408: MOVUPS xmmword ptr [RDI + 0x10],XMM1 *)
| 0x1c4bc8 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4bcc: MOVUPS xmmword ptr [RDI + 0x20],XMM2 *)
(*    1854412: MOVUPS xmmword ptr [RDI + 0x20],XMM2 *)
| 0x1c4bcc => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4bd0: MOVUPS xmmword ptr [RDI + 0x30],XMM3 *)
(*    1854416: MOVUPS xmmword ptr [RDI + 0x30],XMM3 *)
| 0x1c4bd0 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4bd4: MOV R8,RDI *)
(*    1854420: MOV R8,RDI *)
| 0x1c4bd4 => Some (3,
	Move R_R8 (Var R_RDI)
)

(* 0x001c4bd7: AND R8,0x3f *)
(*    1854423: AND R8,0x3f *)
| 0x1c4bd7 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R8 (BinOp OP_AND (Var R_R8) (Word 0x3f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R8) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R8) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4bdb: SUB R8,0x40 *)
(*    1854427: SUB R8,0x40 *)
| 0x1c4bdb => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_R8) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_R8 (BinOp OP_MINUS (Var R_R8) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R8) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R8) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4bdf: SUB RSI,R8 *)
(*    1854431: SUB RSI,R8 *)
| 0x1c4bdf => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_R8)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_R8)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_R8)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4be2: SUB RDI,R8 *)
(*    1854434: SUB RDI,R8 *)
| 0x1c4be2 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Var R_R8)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Var R_R8)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Var R_R8)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4be5: ADD RDX,R8 *)
(*    1854437: ADD RDX,R8 *)
| 0x1c4be5 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDX) (Var R_R8)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDX) (Var R_R8)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_PLUS (Var R_RDX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4be8: NOT ECX *)
(*    1854440: NOT ECX *)
| 0x1c4be8 => Some (2,
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (UnOp OP_NOT (Extract 31 0 (Var R_RCX)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001c4bea: TEST ECX,0xf80 *)
(*    1854442: TEST ECX,0xf80 *)
| 0x1c4bea => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70080) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xf80 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70080)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70080)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70080)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4bf0: JZ 0x001c4d30 *)
(*    1854448: JZ 0x001c4d30 *)
| 0x1c4bf0 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x1c4d30 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4bf6: MOV R10,RDX *)
(*    1854454: MOV R10,RDX *)
| 0x1c4bf6 => Some (3,
	Move R_R10 (Var R_RDX)
)

(* 0x001c4bf9: SHR R10,0x4 *)
(*    1854457: SHR R10,0x4 *)
| 0x1c4bf9 => Some (4,
	Move (V_TEMP 0x6e800) (BinOp OP_AND (Word 0x4 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6e880) (Var R_R10) $;
	Move R_R10 (BinOp OP_RSHIFT (Var R_R10) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e800)))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e880)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e800)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e880)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001c4bfd: CMP R10,qword ptr [0x003215a8] *)
(*    1854461: CMP R10,qword ptr [0x003215a8] *)
| 0x1c4bfd => Some (7,
	Move (V_TEMP 0x3f880) (Load (Var V_MEM64) (Word 0x3215a8 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_R10) (Var (V_TEMP 0x3f880))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x3f880))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f880)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f980) (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0x3f880))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f980)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f980)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4c04: JNC 0x001c4d30 *)
(*    1854468: JNC 0x001c4d30 *)
| 0x1c4c04 => Some (6,
	Move (V_TEMP 0x12780) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x1c4d30 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4c0a: AND EDX,0x1fff *)
(*    1854474: AND EDX,0x1fff *)
| 0x1c4c0a => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x1fff 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4c10: SHR R10,0x9 *)
(*    1854480: SHR R10,0x9 *)
| 0x1c4c10 => Some (4,
	Move (V_TEMP 0x6e800) (BinOp OP_AND (Word 0x9 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6e880) (Var R_R10) $;
	Move R_R10 (BinOp OP_RSHIFT (Var R_R10) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e800)))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e880)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e800)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e880)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001c4c14: NOP dword ptr CS:[RAX + RAX*0x1] *)
(*    1854484: NOP dword ptr CS:[RAX + RAX*0x1] *)
| 0x1c4c14 => Some (11,
	Move (V_TEMP 0x5580) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5680) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5580)))
)

(* 0x001c4c1f: NOP *)
(*    1854495: NOP *)
| 0x1c4c1f => Some (1,
	Nop
)

(* 0x001c4c20: MOV ECX,0x40 *)
(*    1854496: MOV ECX,0x40 *)
| 0x1c4c20 => Some (5,
	Move R_RCX (Word 0x40 64)
)

(* 0x001c4c25: NOP dword ptr [RSI + 0x40] *)
(*    1854501: NOP dword ptr [RSI + 0x40] *)
| 0x1c4c25 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64))
)

(* 0x001c4c29: NOP dword ptr [RSI + 0x80] *)
(*    1854505: NOP dword ptr [RSI + 0x80] *)
| 0x1c4c29 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x80 64))
)

(* 0x001c4c30: NOP dword ptr [RSI + 0x1040] *)
(*    1854512: NOP dword ptr [RSI + 0x1040] *)
| 0x1c4c30 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1040 64))
)

(* 0x001c4c37: NOP dword ptr [RSI + 0x1080] *)
(*    1854519: NOP dword ptr [RSI + 0x1080] *)
| 0x1c4c37 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1080 64))
)

(* 0x001c4c3e: MOVUPS XMM0,xmmword ptr [RSI] *)
(*    1854526: MOVUPS XMM0,xmmword ptr [RSI] *)
| 0x1c4c3e => Some (3,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x001c4c41: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
(*    1854529: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
| 0x1c4c41 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4c45: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
(*    1854533: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
| 0x1c4c45 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4c49: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
(*    1854537: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
| 0x1c4c49 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4c4d: MOVUPS XMM4,xmmword ptr [RSI + 0x1000] *)
(*    1854541: MOVUPS XMM4,xmmword ptr [RSI + 0x1000] *)
| 0x1c4c4d => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM4))))
)

(* 0x001c4c54: MOVUPS XMM5,xmmword ptr [RSI + 0x1010] *)
(*    1854548: MOVUPS XMM5,xmmword ptr [RSI + 0x1010] *)
| 0x1c4c54 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1010 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM5 (Concat (Extract 255 32 (Var R_YMM5)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM5 (Concat (Extract 255 64 (Var R_YMM5)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 96 (Var R_YMM5)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM5))))
)

(* 0x001c4c5b: MOVUPS XMM6,xmmword ptr [RSI + 0x1020] *)
(*    1854555: MOVUPS XMM6,xmmword ptr [RSI + 0x1020] *)
| 0x1c4c5b => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1020 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM6 (Concat (Extract 255 32 (Var R_YMM6)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM6 (Concat (Extract 255 64 (Var R_YMM6)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 96 (Var R_YMM6)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM6))))
)

(* 0x001c4c62: MOVUPS XMM7,xmmword ptr [RSI + 0x1030] *)
(*    1854562: MOVUPS XMM7,xmmword ptr [RSI + 0x1030] *)
| 0x1c4c62 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1030 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM7 (Concat (Extract 255 32 (Var R_YMM7)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM7 (Concat (Extract 255 64 (Var R_YMM7)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 96 (Var R_YMM7)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM7))))
)

(* 0x001c4c69: SUB RSI,-0x40 *)
(*    1854569: SUB RSI,-0x40 *)
| 0x1c4c69 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4c6d: MOVNTDQ xmmword ptr [RDI],XMM0 *)
(*    1854573: MOVNTDQ xmmword ptr [RDI],XMM0 *)
| 0x1c4c6d => Some (4,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4c71: MOVNTDQ xmmword ptr [RDI + 0x10],XMM1 *)
(*    1854577: MOVNTDQ xmmword ptr [RDI + 0x10],XMM1 *)
| 0x1c4c71 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4c76: MOVNTDQ xmmword ptr [RDI + 0x20],XMM2 *)
(*    1854582: MOVNTDQ xmmword ptr [RDI + 0x20],XMM2 *)
| 0x1c4c76 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4c7b: MOVNTDQ xmmword ptr [RDI + 0x30],XMM3 *)
(*    1854587: MOVNTDQ xmmword ptr [RDI + 0x30],XMM3 *)
| 0x1c4c7b => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4c80: MOVNTDQ xmmword ptr [RDI + 0x1000],XMM4 *)
(*    1854592: MOVNTDQ xmmword ptr [RDI + 0x1000],XMM4 *)
| 0x1c4c80 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM4)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4c88: MOVNTDQ xmmword ptr [RDI + 0x1010],XMM5 *)
(*    1854600: MOVNTDQ xmmword ptr [RDI + 0x1010],XMM5 *)
| 0x1c4c88 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x1010 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM5)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4c90: MOVNTDQ xmmword ptr [RDI + 0x1020],XMM6 *)
(*    1854608: MOVNTDQ xmmword ptr [RDI + 0x1020],XMM6 *)
| 0x1c4c90 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x1020 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM6)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4c98: MOVNTDQ xmmword ptr [RDI + 0x1030],XMM7 *)
(*    1854616: MOVNTDQ xmmword ptr [RDI + 0x1030],XMM7 *)
| 0x1c4c98 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x1030 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM7)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4ca0: SUB RDI,-0x40 *)
(*    1854624: SUB RDI,-0x40 *)
| 0x1c4ca0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ca4: DEC ECX *)
(*    1854628: DEC ECX *)
| 0x1c4ca4 => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ca6: JNZ 0x001c4c25 *)
(*    1854630: JNZ 0x001c4c25 *)
| 0x1c4ca6 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1c4c25 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4cac: ADD RDI,0x1000 *)
(*    1854636: ADD RDI,0x1000 *)
| 0x1c4cac => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1000 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4cb3: ADD RSI,0x1000 *)
(*    1854643: ADD RSI,0x1000 *)
| 0x1c4cb3 => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1000 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4cba: DEC R10 *)
(*    1854650: DEC R10 *)
| 0x1c4cba => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_R10 (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4cbd: JNZ 0x001c4c20 *)
(*    1854653: JNZ 0x001c4c20 *)
| 0x1c4cbd => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1c4c20 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4cc3: SFENCE *)
(*    1854659: SFENCE *)
| 0x1c4cc3 => Some (3,
	Nop
)

(* 0x001c4cc6: CMP EDX,0x40 *)
(*    1854662: CMP EDX,0x40 *)
| 0x1c4cc6 => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x40 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4cc9: JBE 0x001c4d01 *)
(*    1854665: JBE 0x001c4d01 *)
| 0x1c4cc9 => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1c4d01 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4ccb: NOP dword ptr [RSI + 0x40] *)
(*    1854667: NOP dword ptr [RSI + 0x40] *)
| 0x1c4ccb => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64))
)

(* 0x001c4ccf: NOP dword ptr [RDI + 0x40] *)
(*    1854671: NOP dword ptr [RDI + 0x40] *)
| 0x1c4ccf => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64))
)

(* 0x001c4cd3: MOVUPS XMM0,xmmword ptr [RSI] *)
(*    1854675: MOVUPS XMM0,xmmword ptr [RSI] *)
| 0x1c4cd3 => Some (3,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x001c4cd6: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
(*    1854678: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
| 0x1c4cd6 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4cda: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
(*    1854682: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
| 0x1c4cda => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4cde: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
(*    1854686: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
| 0x1c4cde => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4ce2: SUB RSI,-0x40 *)
(*    1854690: SUB RSI,-0x40 *)
| 0x1c4ce2 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ce6: ADD EDX,-0x40 *)
(*    1854694: ADD EDX,-0x40 *)
| 0x1c4ce6 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffffc0 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffffc0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffc0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffffc0 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ce9: MOVAPS xmmword ptr [RDI],XMM0 *)
(*    1854697: MOVAPS xmmword ptr [RDI],XMM0 *)
| 0x1c4ce9 => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4cec: MOVAPS xmmword ptr [RDI + 0x10],XMM1 *)
(*    1854700: MOVAPS xmmword ptr [RDI + 0x10],XMM1 *)
| 0x1c4cec => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4cf0: MOVAPS xmmword ptr [RDI + 0x20],XMM2 *)
(*    1854704: MOVAPS xmmword ptr [RDI + 0x20],XMM2 *)
| 0x1c4cf0 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4cf4: MOVAPS xmmword ptr [RDI + 0x30],XMM3 *)
(*    1854708: MOVAPS xmmword ptr [RDI + 0x30],XMM3 *)
| 0x1c4cf4 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4cf8: SUB RDI,-0x40 *)
(*    1854712: SUB RDI,-0x40 *)
| 0x1c4cf8 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4cfc: CMP EDX,0x40 *)
(*    1854716: CMP EDX,0x40 *)
| 0x1c4cfc => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x40 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4cff: JA 0x001c4ccb *)
(*    1854719: JA 0x001c4ccb *)
| 0x1c4cff => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4ccb 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4d01: MOVUPS XMM0,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
(*    1854721: MOVUPS XMM0,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x1c4d01 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x001c4d06: MOVUPS XMM1,xmmword ptr [RSI + RDX*0x1 + -0x30] *)
(*    1854726: MOVUPS XMM1,xmmword ptr [RSI + RDX*0x1 + -0x30] *)
| 0x1c4d06 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffd0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4d0b: MOVUPS XMM2,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
(*    1854731: MOVUPS XMM2,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x1c4d0b => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4d10: MOVUPS XMM3,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*    1854736: MOVUPS XMM3,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x1c4d10 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4d15: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x40],XMM0 *)
(*    1854741: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x40],XMM0 *)
| 0x1c4d15 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4d1a: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x30],XMM1 *)
(*    1854746: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x30],XMM1 *)
| 0x1c4d1a => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffd0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4d1f: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x20],XMM2 *)
(*    1854751: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x20],XMM2 *)
| 0x1c4d1f => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4d24: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM3 *)
(*    1854756: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM3 *)
| 0x1c4d24 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4d29: RET *)
(*    1854761: RET *)
| 0x1c4d29 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001c4d30: MOV R10,RDX *)
(*    1854768: MOV R10,RDX *)
| 0x1c4d30 => Some (3,
	Move R_R10 (Var R_RDX)
)

(* 0x001c4d33: AND EDX,0x3fff *)
(*    1854771: AND EDX,0x3fff *)
| 0x1c4d33 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x3fff 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4d39: SHR R10,0xe *)
(*    1854777: SHR R10,0xe *)
| 0x1c4d39 => Some (4,
	Move (V_TEMP 0x6e800) (BinOp OP_AND (Word 0xe 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6e880) (Var R_R10) $;
	Move R_R10 (BinOp OP_RSHIFT (Var R_R10) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6e800)))) $;
	Move (V_TEMP 0x2f780) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f800) (BinOp OP_MINUS (Var (V_TEMP 0x6e800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f880) (BinOp OP_RSHIFT (Var (V_TEMP 0x6e880)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f800)))) $;
	Move (V_TEMP 0x2f900) (BinOp OP_AND (Var (V_TEMP 0x2f880)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2fa00) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f900)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fa80) (BinOp OP_XOR (Var (V_TEMP 0x2f780)) (Word 1 8)) $;
	Move (V_TEMP 0x2fb00) (BinOp OP_AND (Var (V_TEMP 0x2fa80)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2fb80) (BinOp OP_AND (Var (V_TEMP 0x2f780)) (Var (V_TEMP 0x2fa00))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2fb00)) (Var (V_TEMP 0x2fb80)))) $;
	Move (V_TEMP 0x2fd00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6e800)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2fe00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6e880)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2fe80) (BinOp OP_XOR (Var (V_TEMP 0x2fd00)) (Word 1 8)) $;
	Move (V_TEMP 0x2ff00) (BinOp OP_AND (Var (V_TEMP 0x2fe80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ff80) (BinOp OP_AND (Var (V_TEMP 0x2fd00)) (Var (V_TEMP 0x2fe00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ff00)) (Var (V_TEMP 0x2ff80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e800)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001c4d3d: NOP dword ptr [RAX] *)
(*    1854781: NOP dword ptr [RAX] *)
| 0x1c4d3d => Some (3,
	Nop
)

(* 0x001c4d40: MOV ECX,0x40 *)
(*    1854784: MOV ECX,0x40 *)
| 0x1c4d40 => Some (5,
	Move R_RCX (Word 0x40 64)
)

(* 0x001c4d45: NOP dword ptr [RSI + 0x40] *)
(*    1854789: NOP dword ptr [RSI + 0x40] *)
| 0x1c4d45 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64))
)

(* 0x001c4d49: NOP dword ptr [RSI + 0x1040] *)
(*    1854793: NOP dword ptr [RSI + 0x1040] *)
| 0x1c4d49 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1040 64))
)

(* 0x001c4d50: NOP dword ptr [RSI + 0x2040] *)
(*    1854800: NOP dword ptr [RSI + 0x2040] *)
| 0x1c4d50 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x2040 64))
)

(* 0x001c4d57: NOP dword ptr [RSI + 0x3040] *)
(*    1854807: NOP dword ptr [RSI + 0x3040] *)
| 0x1c4d57 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x3040 64))
)

(* 0x001c4d5e: MOVUPS XMM0,xmmword ptr [RSI] *)
(*    1854814: MOVUPS XMM0,xmmword ptr [RSI] *)
| 0x1c4d5e => Some (3,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x001c4d61: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
(*    1854817: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
| 0x1c4d61 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4d65: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
(*    1854821: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
| 0x1c4d65 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4d69: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
(*    1854825: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
| 0x1c4d69 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4d6d: MOVUPS XMM4,xmmword ptr [RSI + 0x1000] *)
(*    1854829: MOVUPS XMM4,xmmword ptr [RSI + 0x1000] *)
| 0x1c4d6d => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM4)))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM4))))
)

(* 0x001c4d74: MOVUPS XMM5,xmmword ptr [RSI + 0x1010] *)
(*    1854836: MOVUPS XMM5,xmmword ptr [RSI + 0x1010] *)
| 0x1c4d74 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1010 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM5 (Concat (Extract 255 32 (Var R_YMM5)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM5 (Concat (Extract 255 64 (Var R_YMM5)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 96 (Var R_YMM5)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM5)))) $;
	Move R_YMM5 (Concat (Extract 255 128 (Var R_YMM5)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM5))))
)

(* 0x001c4d7b: MOVUPS XMM6,xmmword ptr [RSI + 0x1020] *)
(*    1854843: MOVUPS XMM6,xmmword ptr [RSI + 0x1020] *)
| 0x1c4d7b => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1020 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM6 (Concat (Extract 255 32 (Var R_YMM6)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM6 (Concat (Extract 255 64 (Var R_YMM6)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 96 (Var R_YMM6)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM6)))) $;
	Move R_YMM6 (Concat (Extract 255 128 (Var R_YMM6)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM6))))
)

(* 0x001c4d82: MOVUPS XMM7,xmmword ptr [RSI + 0x1030] *)
(*    1854850: MOVUPS XMM7,xmmword ptr [RSI + 0x1030] *)
| 0x1c4d82 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x1030 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM7 (Concat (Extract 255 32 (Var R_YMM7)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM7 (Concat (Extract 255 64 (Var R_YMM7)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 96 (Var R_YMM7)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM7)))) $;
	Move R_YMM7 (Concat (Extract 255 128 (Var R_YMM7)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM7))))
)

(* 0x001c4d89: MOVUPS XMM8,xmmword ptr [RSI + 0x2000] *)
(*    1854857: MOVUPS XMM8,xmmword ptr [RSI + 0x2000] *)
| 0x1c4d89 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x2000 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM8 (Concat (Extract 255 32 (Var R_YMM8)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM8 (Concat (Extract 255 64 (Var R_YMM8)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM8)))) $;
	Move R_YMM8 (Concat (Extract 255 96 (Var R_YMM8)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM8)))) $;
	Move R_YMM8 (Concat (Extract 255 128 (Var R_YMM8)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM8))))
)

(* 0x001c4d91: MOVUPS XMM9,xmmword ptr [RSI + 0x2010] *)
(*    1854865: MOVUPS XMM9,xmmword ptr [RSI + 0x2010] *)
| 0x1c4d91 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x2010 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM9 (Concat (Extract 255 32 (Var R_YMM9)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM9 (Concat (Extract 255 64 (Var R_YMM9)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM9)))) $;
	Move R_YMM9 (Concat (Extract 255 96 (Var R_YMM9)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM9)))) $;
	Move R_YMM9 (Concat (Extract 255 128 (Var R_YMM9)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM9))))
)

(* 0x001c4d99: MOVUPS XMM10,xmmword ptr [RSI + 0x2020] *)
(*    1854873: MOVUPS XMM10,xmmword ptr [RSI + 0x2020] *)
| 0x1c4d99 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x2020 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM10 (Concat (Extract 255 32 (Var R_YMM10)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM10 (Concat (Extract 255 64 (Var R_YMM10)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM10)))) $;
	Move R_YMM10 (Concat (Extract 255 96 (Var R_YMM10)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM10)))) $;
	Move R_YMM10 (Concat (Extract 255 128 (Var R_YMM10)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM10))))
)

(* 0x001c4da1: MOVUPS XMM11,xmmword ptr [RSI + 0x2030] *)
(*    1854881: MOVUPS XMM11,xmmword ptr [RSI + 0x2030] *)
| 0x1c4da1 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x2030 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM11 (Concat (Extract 255 32 (Var R_YMM11)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM11 (Concat (Extract 255 64 (Var R_YMM11)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM11)))) $;
	Move R_YMM11 (Concat (Extract 255 96 (Var R_YMM11)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM11)))) $;
	Move R_YMM11 (Concat (Extract 255 128 (Var R_YMM11)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM11))))
)

(* 0x001c4da9: MOVUPS XMM12,xmmword ptr [RSI + 0x3000] *)
(*    1854889: MOVUPS XMM12,xmmword ptr [RSI + 0x3000] *)
| 0x1c4da9 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x3000 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM12 (Concat (Extract 255 32 (Var R_YMM12)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM12 (Concat (Extract 255 64 (Var R_YMM12)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM12)))) $;
	Move R_YMM12 (Concat (Extract 255 96 (Var R_YMM12)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM12)))) $;
	Move R_YMM12 (Concat (Extract 255 128 (Var R_YMM12)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM12))))
)

(* 0x001c4db1: MOVUPS XMM13,xmmword ptr [RSI + 0x3010] *)
(*    1854897: MOVUPS XMM13,xmmword ptr [RSI + 0x3010] *)
| 0x1c4db1 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x3010 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM13 (Concat (Extract 255 32 (Var R_YMM13)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM13 (Concat (Extract 255 64 (Var R_YMM13)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM13)))) $;
	Move R_YMM13 (Concat (Extract 255 96 (Var R_YMM13)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM13)))) $;
	Move R_YMM13 (Concat (Extract 255 128 (Var R_YMM13)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM13))))
)

(* 0x001c4db9: MOVUPS XMM14,xmmword ptr [RSI + 0x3020] *)
(*    1854905: MOVUPS XMM14,xmmword ptr [RSI + 0x3020] *)
| 0x1c4db9 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x3020 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM14 (Concat (Extract 255 32 (Var R_YMM14)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM14 (Concat (Extract 255 64 (Var R_YMM14)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM14)))) $;
	Move R_YMM14 (Concat (Extract 255 96 (Var R_YMM14)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM14)))) $;
	Move R_YMM14 (Concat (Extract 255 128 (Var R_YMM14)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM14))))
)

(* 0x001c4dc1: MOVUPS XMM15,xmmword ptr [RSI + 0x3030] *)
(*    1854913: MOVUPS XMM15,xmmword ptr [RSI + 0x3030] *)
| 0x1c4dc1 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RSI) (Word 0x3030 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4880)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM15 (Concat (Extract 255 32 (Var R_YMM15)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM15 (Concat (Extract 255 64 (Var R_YMM15)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM15)))) $;
	Move R_YMM15 (Concat (Extract 255 96 (Var R_YMM15)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM15)))) $;
	Move R_YMM15 (Concat (Extract 255 128 (Var R_YMM15)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM15))))
)

(* 0x001c4dc9: SUB RSI,-0x40 *)
(*    1854921: SUB RSI,-0x40 *)
| 0x1c4dc9 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4dcd: MOVNTDQ xmmword ptr [RDI],XMM0 *)
(*    1854925: MOVNTDQ xmmword ptr [RDI],XMM0 *)
| 0x1c4dcd => Some (4,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4dd1: MOVNTDQ xmmword ptr [RDI + 0x10],XMM1 *)
(*    1854929: MOVNTDQ xmmword ptr [RDI + 0x10],XMM1 *)
| 0x1c4dd1 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4dd6: MOVNTDQ xmmword ptr [RDI + 0x20],XMM2 *)
(*    1854934: MOVNTDQ xmmword ptr [RDI + 0x20],XMM2 *)
| 0x1c4dd6 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4ddb: MOVNTDQ xmmword ptr [RDI + 0x30],XMM3 *)
(*    1854939: MOVNTDQ xmmword ptr [RDI + 0x30],XMM3 *)
| 0x1c4ddb => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4de0: MOVNTDQ xmmword ptr [RDI + 0x1000],XMM4 *)
(*    1854944: MOVNTDQ xmmword ptr [RDI + 0x1000],XMM4 *)
| 0x1c4de0 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM4)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4de8: MOVNTDQ xmmword ptr [RDI + 0x1010],XMM5 *)
(*    1854952: MOVNTDQ xmmword ptr [RDI + 0x1010],XMM5 *)
| 0x1c4de8 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x1010 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM5)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4df0: MOVNTDQ xmmword ptr [RDI + 0x1020],XMM6 *)
(*    1854960: MOVNTDQ xmmword ptr [RDI + 0x1020],XMM6 *)
| 0x1c4df0 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x1020 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM6)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4df8: MOVNTDQ xmmword ptr [RDI + 0x1030],XMM7 *)
(*    1854968: MOVNTDQ xmmword ptr [RDI + 0x1030],XMM7 *)
| 0x1c4df8 => Some (8,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x1030 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM7)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e00: MOVNTDQ xmmword ptr [RDI + 0x2000],XMM8 *)
(*    1854976: MOVNTDQ xmmword ptr [RDI + 0x2000],XMM8 *)
| 0x1c4e00 => Some (9,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x2000 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM8)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e09: MOVNTDQ xmmword ptr [RDI + 0x2010],XMM9 *)
(*    1854985: MOVNTDQ xmmword ptr [RDI + 0x2010],XMM9 *)
| 0x1c4e09 => Some (9,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x2010 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM9)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e12: MOVNTDQ xmmword ptr [RDI + 0x2020],XMM10 *)
(*    1854994: MOVNTDQ xmmword ptr [RDI + 0x2020],XMM10 *)
| 0x1c4e12 => Some (9,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x2020 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM10)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e1b: MOVNTDQ xmmword ptr [RDI + 0x2030],XMM11 *)
(*    1855003: MOVNTDQ xmmword ptr [RDI + 0x2030],XMM11 *)
| 0x1c4e1b => Some (9,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x2030 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM11)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e24: MOVNTDQ xmmword ptr [RDI + 0x3000],XMM12 *)
(*    1855012: MOVNTDQ xmmword ptr [RDI + 0x3000],XMM12 *)
| 0x1c4e24 => Some (9,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x3000 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM12)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e2d: MOVNTDQ xmmword ptr [RDI + 0x3010],XMM13 *)
(*    1855021: MOVNTDQ xmmword ptr [RDI + 0x3010],XMM13 *)
| 0x1c4e2d => Some (9,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x3010 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM13)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e36: MOVNTDQ xmmword ptr [RDI + 0x3020],XMM14 *)
(*    1855030: MOVNTDQ xmmword ptr [RDI + 0x3020],XMM14 *)
| 0x1c4e36 => Some (9,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x3020 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM14)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e3f: MOVNTDQ xmmword ptr [RDI + 0x3030],XMM15 *)
(*    1855039: MOVNTDQ xmmword ptr [RDI + 0x3030],XMM15 *)
| 0x1c4e3f => Some (9,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RDI) (Word 0x3030 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM15)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4880)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e48: SUB RDI,-0x40 *)
(*    1855048: SUB RDI,-0x40 *)
| 0x1c4e48 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4e4c: DEC ECX *)
(*    1855052: DEC ECX *)
| 0x1c4e4c => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4e4e: JNZ 0x001c4d45 *)
(*    1855054: JNZ 0x001c4d45 *)
| 0x1c4e4e => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1c4d45 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4e54: ADD RDI,0x3000 *)
(*    1855060: ADD RDI,0x3000 *)
| 0x1c4e54 => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x3000 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x3000 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3000 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x3000 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4e5b: ADD RSI,0x3000 *)
(*    1855067: ADD RSI,0x3000 *)
| 0x1c4e5b => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Word 0x3000 64)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Word 0x3000 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3000 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Word 0x3000 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4e62: DEC R10 *)
(*    1855074: DEC R10 *)
| 0x1c4e62 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_R10 (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4e65: JNZ 0x001c4d40 *)
(*    1855077: JNZ 0x001c4d40 *)
| 0x1c4e65 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1c4d40 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4e6b: SFENCE *)
(*    1855083: SFENCE *)
| 0x1c4e6b => Some (3,
	Nop
)

(* 0x001c4e6e: CMP EDX,0x40 *)
(*    1855086: CMP EDX,0x40 *)
| 0x1c4e6e => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x40 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4e71: JBE 0x001c4ea9 *)
(*    1855089: JBE 0x001c4ea9 *)
| 0x1c4e71 => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1c4ea9 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4e73: NOP dword ptr [RSI + 0x40] *)
(*    1855091: NOP dword ptr [RSI + 0x40] *)
| 0x1c4e73 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64))
)

(* 0x001c4e77: NOP dword ptr [RDI + 0x40] *)
(*    1855095: NOP dword ptr [RDI + 0x40] *)
| 0x1c4e77 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64))
)

(* 0x001c4e7b: MOVUPS XMM0,xmmword ptr [RSI] *)
(*    1855099: MOVUPS XMM0,xmmword ptr [RSI] *)
| 0x1c4e7b => Some (3,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x001c4e7e: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
(*    1855102: MOVUPS XMM1,xmmword ptr [RSI + 0x10] *)
| 0x1c4e7e => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4e82: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
(*    1855106: MOVUPS XMM2,xmmword ptr [RSI + 0x20] *)
| 0x1c4e82 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4e86: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
(*    1855110: MOVUPS XMM3,xmmword ptr [RSI + 0x30] *)
| 0x1c4e86 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RSI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4e8a: SUB RSI,-0x40 *)
(*    1855114: SUB RSI,-0x40 *)
| 0x1c4e8a => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4e8e: ADD EDX,-0x40 *)
(*    1855118: ADD EDX,-0x40 *)
| 0x1c4e8e => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffffc0 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffffc0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffc0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffffc0 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4e91: MOVAPS xmmword ptr [RDI],XMM0 *)
(*    1855121: MOVAPS xmmword ptr [RDI],XMM0 *)
| 0x1c4e91 => Some (3,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e94: MOVAPS xmmword ptr [RDI + 0x10],XMM1 *)
(*    1855124: MOVAPS xmmword ptr [RDI + 0x10],XMM1 *)
| 0x1c4e94 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e98: MOVAPS xmmword ptr [RDI + 0x20],XMM2 *)
(*    1855128: MOVAPS xmmword ptr [RDI + 0x20],XMM2 *)
| 0x1c4e98 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4e9c: MOVAPS xmmword ptr [RDI + 0x30],XMM3 *)
(*    1855132: MOVAPS xmmword ptr [RDI + 0x30],XMM3 *)
| 0x1c4e9c => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4ea0: SUB RDI,-0x40 *)
(*    1855136: SUB RDI,-0x40 *)
| 0x1c4ea0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffffc0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffffc0 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ea4: CMP EDX,0x40 *)
(*    1855140: CMP EDX,0x40 *)
| 0x1c4ea4 => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x40 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x40 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4ea7: JA 0x001c4e73 *)
(*    1855143: JA 0x001c4e73 *)
| 0x1c4ea7 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1c4e73 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4ea9: MOVUPS XMM0,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
(*    1855145: MOVUPS XMM0,xmmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x1c4ea9 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x001c4eae: MOVUPS XMM1,xmmword ptr [RSI + RDX*0x1 + -0x30] *)
(*    1855150: MOVUPS XMM1,xmmword ptr [RSI + RDX*0x1 + -0x30] *)
| 0x1c4eae => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffd0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001c4eb3: MOVUPS XMM2,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
(*    1855155: MOVUPS XMM2,xmmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x1c4eb3 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM2)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM2))))
)

(* 0x001c4eb8: MOVUPS XMM3,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*    1855160: MOVUPS XMM3,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x1c4eb8 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x5080)) LittleE 16) $;
	Move (V_TEMP 0x8fd00) (Var (V_TEMP 0x6c80)) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Extract 31 0 (Var (V_TEMP 0x8fd00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Extract 63 32 (Var (V_TEMP 0x8fd00))) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Extract 95 64 (Var (V_TEMP 0x8fd00))) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Extract 127 96 (Var (V_TEMP 0x8fd00))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x001c4ebd: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x40],XMM0 *)
(*    1855165: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x40],XMM0 *)
| 0x1c4ebd => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4ec2: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x30],XMM1 *)
(*    1855170: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x30],XMM1 *)
| 0x1c4ec2 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffd0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4ec7: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x20],XMM2 *)
(*    1855175: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x20],XMM2 *)
| 0x1c4ec7 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM2)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4ecc: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM3 *)
(*    1855180: MOVUPS xmmword ptr [RDI + RDX*0x1 + -0x10],XMM3 *)
| 0x1c4ecc => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM3)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x001c4ed1: RET *)
(*    1855185: RET *)
| 0x1c4ed1 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem memcpy_welltyped_lifted: welltyped_prog x64typctx memcpy_amd64.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: FUN_001b4880 at 0x1b4880
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition memchr_sse2_amd64 : program := fun _ a => match a with

(* ---- FUN_001b4880 ---- *)

(* 0x001b4880: ENDBR64 *)
(*    1788032: ENDBR64 *)
| 0x1b4880 => Some (4,
	Nop
)

(* 0x001b4884: MOVD XMM1,ESI *)
(*    1788036: MOVD XMM1,ESI *)
| 0x1b4884 => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Cast CAST_UNSIGNED 128 (Extract 31 0 (Var R_RSI))))
)

(* 0x001b4888: MOV ECX,EDI *)
(*    1788040: MOV ECX,EDI *)
| 0x1b4888 => Some (2,
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001b488a: PUNPCKLBW XMM1,XMM1 *)
(*    1788042: PUNPCKLBW XMM1,XMM1 *)
| 0x1b488a => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 63 56 (Var R_YMM1)) (Extract 119 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 120 (Var R_YMM1)) (Concat (Extract 63 56 (Var R_YMM1)) (Extract 111 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 112 (Var R_YMM1)) (Concat (Extract 55 48 (Var R_YMM1)) (Extract 103 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 104 (Var R_YMM1)) (Concat (Extract 55 48 (Var R_YMM1)) (Extract 95 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 47 40 (Var R_YMM1)) (Extract 87 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 88 (Var R_YMM1)) (Concat (Extract 47 40 (Var R_YMM1)) (Extract 79 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 80 (Var R_YMM1)) (Concat (Extract 39 32 (Var R_YMM1)) (Extract 71 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 72 (Var R_YMM1)) (Concat (Extract 39 32 (Var R_YMM1)) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 31 24 (Var R_YMM1)) (Extract 55 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 56 (Var R_YMM1)) (Concat (Extract 31 24 (Var R_YMM1)) (Extract 47 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 48 (Var R_YMM1)) (Concat (Extract 23 16 (Var R_YMM1)) (Extract 39 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 40 (Var R_YMM1)) (Concat (Extract 23 16 (Var R_YMM1)) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Concat (Extract 15 8 (Var R_YMM1)) (Extract 23 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 24 (Var R_YMM1)) (Concat (Extract 15 8 (Var R_YMM1)) (Extract 15 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 16 (Var R_YMM1)) (Concat (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var R_YMM1))))
)

(* 0x001b488e: TEST RDX,RDX *)
(*    1788046: TEST RDX,RDX *)
| 0x1b488e => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RDX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4891: JZ 0x001b4ba0 *)
(*    1788049: JZ 0x001b4ba0 *)
| 0x1b4891 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4897: PUNPCKLBW XMM1,XMM1 *)
(*    1788055: PUNPCKLBW XMM1,XMM1 *)
| 0x1b4897 => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (Extract 63 56 (Var R_YMM1)) (Extract 119 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 120 (Var R_YMM1)) (Concat (Extract 63 56 (Var R_YMM1)) (Extract 111 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 112 (Var R_YMM1)) (Concat (Extract 55 48 (Var R_YMM1)) (Extract 103 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 104 (Var R_YMM1)) (Concat (Extract 55 48 (Var R_YMM1)) (Extract 95 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (Extract 47 40 (Var R_YMM1)) (Extract 87 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 88 (Var R_YMM1)) (Concat (Extract 47 40 (Var R_YMM1)) (Extract 79 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 80 (Var R_YMM1)) (Concat (Extract 39 32 (Var R_YMM1)) (Extract 71 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 72 (Var R_YMM1)) (Concat (Extract 39 32 (Var R_YMM1)) (Extract 63 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (Extract 31 24 (Var R_YMM1)) (Extract 55 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 56 (Var R_YMM1)) (Concat (Extract 31 24 (Var R_YMM1)) (Extract 47 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 48 (Var R_YMM1)) (Concat (Extract 23 16 (Var R_YMM1)) (Extract 39 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 40 (Var R_YMM1)) (Concat (Extract 23 16 (Var R_YMM1)) (Extract 31 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Concat (Extract 15 8 (Var R_YMM1)) (Extract 23 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 24 (Var R_YMM1)) (Concat (Extract 15 8 (Var R_YMM1)) (Extract 15 0 (Var R_YMM1)))) $;
	Move R_YMM1 (Concat (Extract 255 16 (Var R_YMM1)) (Concat (Extract 7 0 (Var R_YMM1)) (Extract 7 0 (Var R_YMM1))))
)

(* 0x001b489b: AND ECX,0x3f *)
(*    1788059: AND ECX,0x3f *)
| 0x1b489b => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x3f 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b489e: PSHUFD XMM1,XMM1,0x0 *)
(*    1788062: PSHUFD XMM1,XMM1,0x0 *)
| 0x1b489e => Some (5,
	Move (V_TEMP 0xc1400) (Extract 31 0 (Var R_YMM1)) $;
	Move (V_TEMP 0xc1480) (Extract 63 32 (Var R_YMM1)) $;
	Move (V_TEMP 0xc1500) (Extract 95 64 (Var R_YMM1)) $;
	Move (V_TEMP 0xc1580) (Extract 127 96 (Var R_YMM1)) $;
	Move (V_TEMP 0xc0c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x0 8))) $;
	Move (V_TEMP 0xc0d00) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc0c80))) $;
	Move (V_TEMP 0xc0d80) (BinOp OP_TIMES (Var (V_TEMP 0xc0d00)) (Var (V_TEMP 0xc1400))) $;
	Move (V_TEMP 0xc0e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x1 8))) $;
	Move (V_TEMP 0xc0e80) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc0e00))) $;
	Move (V_TEMP 0xc0f00) (BinOp OP_TIMES (Var (V_TEMP 0xc0e80)) (Var (V_TEMP 0xc1480))) $;
	Move (V_TEMP 0xc0f80) (BinOp OP_PLUS (Var (V_TEMP 0xc0d80)) (Var (V_TEMP 0xc0f00))) $;
	Move (V_TEMP 0xc1000) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x2 8))) $;
	Move (V_TEMP 0xc1080) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc1000))) $;
	Move (V_TEMP 0xc1100) (BinOp OP_TIMES (Var (V_TEMP 0xc1080)) (Var (V_TEMP 0xc1500))) $;
	Move (V_TEMP 0xc1180) (BinOp OP_PLUS (Var (V_TEMP 0xc0f80)) (Var (V_TEMP 0xc1100))) $;
	Move (V_TEMP 0xc1200) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x3 8))) $;
	Move (V_TEMP 0xc1280) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc1200))) $;
	Move (V_TEMP 0xc1300) (BinOp OP_TIMES (Var (V_TEMP 0xc1280)) (Var (V_TEMP 0xc1580))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (BinOp OP_PLUS (Var (V_TEMP 0xc1180)) (Var (V_TEMP 0xc1300)))) $;
	Move (V_TEMP 0xc0c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x0 8))) $;
	Move (V_TEMP 0xc0d00) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc0c80))) $;
	Move (V_TEMP 0xc0d80) (BinOp OP_TIMES (Var (V_TEMP 0xc0d00)) (Var (V_TEMP 0xc1400))) $;
	Move (V_TEMP 0xc0e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x1 8))) $;
	Move (V_TEMP 0xc0e80) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc0e00))) $;
	Move (V_TEMP 0xc0f00) (BinOp OP_TIMES (Var (V_TEMP 0xc0e80)) (Var (V_TEMP 0xc1480))) $;
	Move (V_TEMP 0xc0f80) (BinOp OP_PLUS (Var (V_TEMP 0xc0d80)) (Var (V_TEMP 0xc0f00))) $;
	Move (V_TEMP 0xc1000) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x2 8))) $;
	Move (V_TEMP 0xc1080) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc1000))) $;
	Move (V_TEMP 0xc1100) (BinOp OP_TIMES (Var (V_TEMP 0xc1080)) (Var (V_TEMP 0xc1500))) $;
	Move (V_TEMP 0xc1180) (BinOp OP_PLUS (Var (V_TEMP 0xc0f80)) (Var (V_TEMP 0xc1100))) $;
	Move (V_TEMP 0xc1200) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x3 8))) $;
	Move (V_TEMP 0xc1280) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc1200))) $;
	Move (V_TEMP 0xc1300) (BinOp OP_TIMES (Var (V_TEMP 0xc1280)) (Var (V_TEMP 0xc1580))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (BinOp OP_PLUS (Var (V_TEMP 0xc1180)) (Var (V_TEMP 0xc1300))) (Extract 31 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xc0c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x0 8))) $;
	Move (V_TEMP 0xc0d00) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc0c80))) $;
	Move (V_TEMP 0xc0d80) (BinOp OP_TIMES (Var (V_TEMP 0xc0d00)) (Var (V_TEMP 0xc1400))) $;
	Move (V_TEMP 0xc0e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x1 8))) $;
	Move (V_TEMP 0xc0e80) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc0e00))) $;
	Move (V_TEMP 0xc0f00) (BinOp OP_TIMES (Var (V_TEMP 0xc0e80)) (Var (V_TEMP 0xc1480))) $;
	Move (V_TEMP 0xc0f80) (BinOp OP_PLUS (Var (V_TEMP 0xc0d80)) (Var (V_TEMP 0xc0f00))) $;
	Move (V_TEMP 0xc1000) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x2 8))) $;
	Move (V_TEMP 0xc1080) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc1000))) $;
	Move (V_TEMP 0xc1100) (BinOp OP_TIMES (Var (V_TEMP 0xc1080)) (Var (V_TEMP 0xc1500))) $;
	Move (V_TEMP 0xc1180) (BinOp OP_PLUS (Var (V_TEMP 0xc0f80)) (Var (V_TEMP 0xc1100))) $;
	Move (V_TEMP 0xc1200) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x3 8))) $;
	Move (V_TEMP 0xc1280) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc1200))) $;
	Move (V_TEMP 0xc1300) (BinOp OP_TIMES (Var (V_TEMP 0xc1280)) (Var (V_TEMP 0xc1580))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (BinOp OP_PLUS (Var (V_TEMP 0xc1180)) (Var (V_TEMP 0xc1300))) (Extract 63 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xc0c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x0 8))) $;
	Move (V_TEMP 0xc0d00) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc0c80))) $;
	Move (V_TEMP 0xc0d80) (BinOp OP_TIMES (Var (V_TEMP 0xc0d00)) (Var (V_TEMP 0xc1400))) $;
	Move (V_TEMP 0xc0e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x1 8))) $;
	Move (V_TEMP 0xc0e80) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc0e00))) $;
	Move (V_TEMP 0xc0f00) (BinOp OP_TIMES (Var (V_TEMP 0xc0e80)) (Var (V_TEMP 0xc1480))) $;
	Move (V_TEMP 0xc0f80) (BinOp OP_PLUS (Var (V_TEMP 0xc0d80)) (Var (V_TEMP 0xc0f00))) $;
	Move (V_TEMP 0xc1000) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x2 8))) $;
	Move (V_TEMP 0xc1080) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc1000))) $;
	Move (V_TEMP 0xc1100) (BinOp OP_TIMES (Var (V_TEMP 0xc1080)) (Var (V_TEMP 0xc1500))) $;
	Move (V_TEMP 0xc1180) (BinOp OP_PLUS (Var (V_TEMP 0xc0f80)) (Var (V_TEMP 0xc1100))) $;
	Move (V_TEMP 0xc1200) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Word 0x0 8) (Word 0x3 8))) $;
	Move (V_TEMP 0xc1280) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc1200))) $;
	Move (V_TEMP 0xc1300) (BinOp OP_TIMES (Var (V_TEMP 0xc1280)) (Var (V_TEMP 0xc1580))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (BinOp OP_PLUS (Var (V_TEMP 0xc1180)) (Var (V_TEMP 0xc1300))) (Extract 95 0 (Var R_YMM1))))
)

(* 0x001b48a3: CMP ECX,0x30 *)
(*    1788067: CMP ECX,0x30 *)
| 0x1b48a3 => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RCX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x30 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x30 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x30 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x30 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x30 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48a6: JA 0x001b48e0 *)
(*    1788070: JA 0x001b48e0 *)
| 0x1b48a6 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1b48e0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b48a8: MOVDQU XMM0,xmmword ptr [RDI] *)
(*    1788072: MOVDQU XMM0,xmmword ptr [RDI] *)
| 0x1b48a8 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b48ac: PCMPEQB XMM0,XMM1 *)
(*    1788076: PCMPEQB XMM0,XMM1 *)
| 0x1b48ac => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001b48b0: PMOVMSKB EAX,XMM0 *)
(*    1788080: PMOVMSKB EAX,XMM0 *)
| 0x1b48b0 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b48b4: TEST EAX,EAX *)
(*    1788084: TEST EAX,EAX *)
| 0x1b48b4 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48b6: JNZ 0x001b4b60 *)
(*    1788086: JNZ 0x001b4b60 *)
| 0x1b48b6 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b60 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b48bc: SUB RDX,0x10 *)
(*    1788092: SUB RDX,0x10 *)
| 0x1b48bc => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Word 0x10 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x10 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48c0: JBE 0x001b4ba0 *)
(*    1788096: JBE 0x001b4ba0 *)
| 0x1b48c0 => Some (6,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b48c6: ADD RDI,0x10 *)
(*    1788102: ADD RDI,0x10 *)
| 0x1b48c6 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48ca: AND ECX,0xf *)
(*    1788106: AND ECX,0xf *)
| 0x1b48ca => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xf 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48cd: AND RDI,-0x10 *)
(*    1788109: AND RDI,-0x10 *)
| 0x1b48cd => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_AND (Var R_RDI) (Word 0xfffffffffffffff0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48d1: ADD RDX,RCX *)
(*    1788113: ADD RDX,RCX *)
| 0x1b48d1 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDX) (Var R_RCX)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDX) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_PLUS (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48d4: SUB RDX,0x40 *)
(*    1788116: SUB RDX,0x40 *)
| 0x1b48d4 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48d8: JBE 0x001b4a90 *)
(*    1788120: JBE 0x001b4a90 *)
| 0x1b48d8 => Some (6,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4a90 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b48de: JMP 0x001b4930 *)
(*    1788126: JMP 0x001b4930 *)
| 0x1b48de => Some (2,
	Jmp (Word 0x1b4930 64)
)

(* 0x001b48e0: AND ECX,0xf *)
(*    1788128: AND ECX,0xf *)
| 0x1b48e0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xf 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48e3: AND RDI,-0x10 *)
(*    1788131: AND RDI,-0x10 *)
| 0x1b48e3 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_AND (Var R_RDI) (Word 0xfffffffffffffff0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48e7: MOVDQA XMM0,xmmword ptr [RDI] *)
(*    1788135: MOVDQA XMM0,xmmword ptr [RDI] *)
| 0x1b48e7 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b48eb: PCMPEQB XMM0,XMM1 *)
(*    1788139: PCMPEQB XMM0,XMM1 *)
| 0x1b48eb => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001b48ef: PMOVMSKB EAX,XMM0 *)
(*    1788143: PMOVMSKB EAX,XMM0 *)
| 0x1b48ef => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b48f3: SAR EAX,CL *)
(*    1788147: SAR EAX,CL *)
| 0x1b48f3 => Some (2,
	Move (V_TEMP 0x68380) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x1f 8)) $;
	Move (V_TEMP 0x68400) (Extract 31 0 (Var R_RAX)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_ARSHIFT (Extract 31 0 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x68380))))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x2f000) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68380)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_MINUS (Var (V_TEMP 0x68380)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2f100) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68400)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x2f080)))) $;
	Move (V_TEMP 0x2f180) (BinOp OP_AND (Var (V_TEMP 0x2f100)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2f300) (BinOp OP_XOR (Var (V_TEMP 0x2f000)) (Word 1 8)) $;
	Move (V_TEMP 0x2f380) (BinOp OP_AND (Var (V_TEMP 0x2f300)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2f400) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Var (V_TEMP 0x2f280))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2f380)) (Var (V_TEMP 0x2f400)))) $;
	Move (V_TEMP 0x2f580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x68380)) (Word 0x1 8))) $;
	Move (V_TEMP 0x2f600) (BinOp OP_XOR (Var (V_TEMP 0x2f580)) (Word 1 8)) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_AND (Var (V_TEMP 0x2f600)) (Cast CAST_UNSIGNED 8 (Var R_OF)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68380)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001b48f5: TEST EAX,EAX *)
(*    1788149: TEST EAX,EAX *)
| 0x1b48f5 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48f7: JZ 0x001b4910 *)
(*    1788151: JZ 0x001b4910 *)
| 0x1b48f7 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1b4910 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b48f9: BSF EAX,EAX *)
(*    1788153: BSF EAX,EAX *)
| 0x1b48f9 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b48fc: SUB RDX,RAX *)
(*    1788156: SUB RDX,RAX *)
| 0x1b48fc => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b48ff: JBE 0x001b4ba0 *)
(*    1788159: JBE 0x001b4ba0 *)
| 0x1b48ff => Some (6,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4905: ADD RAX,RDI *)
(*    1788165: ADD RAX,RDI *)
| 0x1b4905 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4908: ADD RAX,RCX *)
(*    1788168: ADD RAX,RCX *)
| 0x1b4908 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RCX)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b490b: RET *)
(*    1788171: RET *)
| 0x1b490b => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4910: NEG RCX *)
(*    1788176: NEG RCX *)
| 0x1b4910 => Some (3,
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

(* 0x001b4913: ADD RCX,0x10 *)
(*    1788179: ADD RCX,0x10 *)
| 0x1b4913 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RCX) (Word 0x10 64)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RCX) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_PLUS (Var R_RCX) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4917: SUB RDX,RCX *)
(*    1788183: SUB RDX,RCX *)
| 0x1b4917 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b491a: JBE 0x001b4ba0 *)
(*    1788186: JBE 0x001b4ba0 *)
| 0x1b491a => Some (6,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4920: ADD RDI,0x10 *)
(*    1788192: ADD RDI,0x10 *)
| 0x1b4920 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4924: SUB RDX,0x40 *)
(*    1788196: SUB RDX,0x40 *)
| 0x1b4924 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4928: JBE 0x001b4a90 *)
(*    1788200: JBE 0x001b4a90 *)
| 0x1b4928 => Some (6,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4a90 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b492e: NOP *)
(*    1788206: NOP *)
| 0x1b492e => Some (2,
	Nop
)

(* 0x001b4930: MOVDQA XMM0,xmmword ptr [RDI] *)
(*    1788208: MOVDQA XMM0,xmmword ptr [RDI] *)
| 0x1b4930 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4934: PCMPEQB XMM0,XMM1 *)
(*    1788212: PCMPEQB XMM0,XMM1 *)
| 0x1b4934 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001b4938: PMOVMSKB EAX,XMM0 *)
(*    1788216: PMOVMSKB EAX,XMM0 *)
| 0x1b4938 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b493c: TEST EAX,EAX *)
(*    1788220: TEST EAX,EAX *)
| 0x1b493c => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b493e: JNZ 0x001b4b30 *)
(*    1788222: JNZ 0x001b4b30 *)
| 0x1b493e => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b30 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4944: MOVDQA XMM2,xmmword ptr [RDI + 0x10] *)
(*    1788228: MOVDQA XMM2,xmmword ptr [RDI + 0x10] *)
| 0x1b4944 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4949: PCMPEQB XMM2,XMM1 *)
(*    1788233: PCMPEQB XMM2,XMM1 *)
| 0x1b4949 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001b494d: PMOVMSKB EAX,XMM2 *)
(*    1788237: PMOVMSKB EAX,XMM2 *)
| 0x1b494d => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4951: TEST EAX,EAX *)
(*    1788241: TEST EAX,EAX *)
| 0x1b4951 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4953: JNZ 0x001b4b40 *)
(*    1788243: JNZ 0x001b4b40 *)
| 0x1b4953 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b40 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4959: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
(*    1788249: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
| 0x1b4959 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b495e: PCMPEQB XMM3,XMM1 *)
(*    1788254: PCMPEQB XMM3,XMM1 *)
| 0x1b495e => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001b4962: PMOVMSKB EAX,XMM3 *)
(*    1788258: PMOVMSKB EAX,XMM3 *)
| 0x1b4962 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4966: TEST EAX,EAX *)
(*    1788262: TEST EAX,EAX *)
| 0x1b4966 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4968: JNZ 0x001b4b50 *)
(*    1788264: JNZ 0x001b4b50 *)
| 0x1b4968 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b50 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b496e: MOVDQA XMM4,xmmword ptr [RDI + 0x30] *)
(*    1788270: MOVDQA XMM4,xmmword ptr [RDI + 0x30] *)
| 0x1b496e => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4973: PCMPEQB XMM4,XMM1 *)
(*    1788275: PCMPEQB XMM4,XMM1 *)
| 0x1b4973 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 8 (Var R_YMM4)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 16 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 24 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 40 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 48 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 56 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 72 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 80 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 88 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 104 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 112 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 120 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM4))))
)

(* 0x001b4977: ADD RDI,0x40 *)
(*    1788279: ADD RDI,0x40 *)
| 0x1b4977 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b497b: PMOVMSKB EAX,XMM4 *)
(*    1788283: PMOVMSKB EAX,XMM4 *)
| 0x1b497b => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b497f: TEST EAX,EAX *)
(*    1788287: TEST EAX,EAX *)
| 0x1b497f => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4981: JNZ 0x001b4b20 *)
(*    1788289: JNZ 0x001b4b20 *)
| 0x1b4981 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b20 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4987: TEST RDI,0x3f *)
(*    1788295: TEST RDI,0x3f *)
| 0x1b4987 => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Var R_RDI) (Word 0x3f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b498e: JZ 0x001b4a00 *)
(*    1788302: JZ 0x001b4a00 *)
| 0x1b498e => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1b4a00 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4990: SUB RDX,0x40 *)
(*    1788304: SUB RDX,0x40 *)
| 0x1b4990 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4994: JBE 0x001b4a90 *)
(*    1788308: JBE 0x001b4a90 *)
| 0x1b4994 => Some (6,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4a90 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b499a: MOVDQA XMM0,xmmword ptr [RDI] *)
(*    1788314: MOVDQA XMM0,xmmword ptr [RDI] *)
| 0x1b499a => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b499e: PCMPEQB XMM0,XMM1 *)
(*    1788318: PCMPEQB XMM0,XMM1 *)
| 0x1b499e => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001b49a2: PMOVMSKB EAX,XMM0 *)
(*    1788322: PMOVMSKB EAX,XMM0 *)
| 0x1b49a2 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b49a6: TEST EAX,EAX *)
(*    1788326: TEST EAX,EAX *)
| 0x1b49a6 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b49a8: JNZ 0x001b4b30 *)
(*    1788328: JNZ 0x001b4b30 *)
| 0x1b49a8 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b30 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b49ae: MOVDQA XMM2,xmmword ptr [RDI + 0x10] *)
(*    1788334: MOVDQA XMM2,xmmword ptr [RDI + 0x10] *)
| 0x1b49ae => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b49b3: PCMPEQB XMM2,XMM1 *)
(*    1788339: PCMPEQB XMM2,XMM1 *)
| 0x1b49b3 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001b49b7: PMOVMSKB EAX,XMM2 *)
(*    1788343: PMOVMSKB EAX,XMM2 *)
| 0x1b49b7 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b49bb: TEST EAX,EAX *)
(*    1788347: TEST EAX,EAX *)
| 0x1b49bb => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b49bd: JNZ 0x001b4b40 *)
(*    1788349: JNZ 0x001b4b40 *)
| 0x1b49bd => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b40 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b49c3: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
(*    1788355: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
| 0x1b49c3 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b49c8: PCMPEQB XMM3,XMM1 *)
(*    1788360: PCMPEQB XMM3,XMM1 *)
| 0x1b49c8 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001b49cc: PMOVMSKB EAX,XMM3 *)
(*    1788364: PMOVMSKB EAX,XMM3 *)
| 0x1b49cc => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b49d0: TEST EAX,EAX *)
(*    1788368: TEST EAX,EAX *)
| 0x1b49d0 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b49d2: JNZ 0x001b4b50 *)
(*    1788370: JNZ 0x001b4b50 *)
| 0x1b49d2 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b50 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b49d8: MOVDQA XMM3,xmmword ptr [RDI + 0x30] *)
(*    1788376: MOVDQA XMM3,xmmword ptr [RDI + 0x30] *)
| 0x1b49d8 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b49dd: PCMPEQB XMM3,XMM1 *)
(*    1788381: PCMPEQB XMM3,XMM1 *)
| 0x1b49dd => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001b49e1: PMOVMSKB EAX,XMM3 *)
(*    1788385: PMOVMSKB EAX,XMM3 *)
| 0x1b49e1 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b49e5: ADD RDI,0x40 *)
(*    1788389: ADD RDI,0x40 *)
| 0x1b49e5 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b49e9: TEST EAX,EAX *)
(*    1788393: TEST EAX,EAX *)
| 0x1b49e9 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b49eb: JNZ 0x001b4b20 *)
(*    1788395: JNZ 0x001b4b20 *)
| 0x1b49eb => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b20 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b49f1: MOV RCX,RDI *)
(*    1788401: MOV RCX,RDI *)
| 0x1b49f1 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001b49f4: AND RDI,-0x40 *)
(*    1788404: AND RDI,-0x40 *)
| 0x1b49f4 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_AND (Var R_RDI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b49f8: AND ECX,0x3f *)
(*    1788408: AND ECX,0x3f *)
| 0x1b49f8 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x3f 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b49fb: ADD RDX,RCX *)
(*    1788411: ADD RDX,RCX *)
| 0x1b49fb => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDX) (Var R_RCX)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDX) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_PLUS (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b49fe: NOP *)
(*    1788414: NOP *)
| 0x1b49fe => Some (2,
	Nop
)

(* 0x001b4a00: SUB RDX,0x40 *)
(*    1788416: SUB RDX,0x40 *)
| 0x1b4a00 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4a04: JBE 0x001b4a90 *)
(*    1788420: JBE 0x001b4a90 *)
| 0x1b4a04 => Some (6,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4a90 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4a0a: MOVDQA XMM0,xmmword ptr [RDI] *)
(*    1788426: MOVDQA XMM0,xmmword ptr [RDI] *)
| 0x1b4a0a => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4a0e: MOVDQA XMM2,xmmword ptr [RDI + 0x10] *)
(*    1788430: MOVDQA XMM2,xmmword ptr [RDI + 0x10] *)
| 0x1b4a0e => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4a13: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
(*    1788435: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
| 0x1b4a13 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4a18: MOVDQA XMM4,xmmword ptr [RDI + 0x30] *)
(*    1788440: MOVDQA XMM4,xmmword ptr [RDI + 0x30] *)
| 0x1b4a18 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4a1d: PCMPEQB XMM0,XMM1 *)
(*    1788445: PCMPEQB XMM0,XMM1 *)
| 0x1b4a1d => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001b4a21: PCMPEQB XMM2,XMM1 *)
(*    1788449: PCMPEQB XMM2,XMM1 *)
| 0x1b4a21 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001b4a25: PCMPEQB XMM3,XMM1 *)
(*    1788453: PCMPEQB XMM3,XMM1 *)
| 0x1b4a25 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001b4a29: PCMPEQB XMM4,XMM1 *)
(*    1788457: PCMPEQB XMM4,XMM1 *)
| 0x1b4a29 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM4)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 8 (Var R_YMM4)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM4)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 16 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM4)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 24 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM4)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM4)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 40 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM4)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 48 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM4)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 56 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM4)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM4)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 72 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM4)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 80 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM4)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 88 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM4)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM4)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 104 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM4)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 112 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM4)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 120 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM4)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM4))))
)

(* 0x001b4a2d: PMAXUB XMM3,XMM0 *)
(*    1788461: PMAXUB XMM3,XMM0 *)
| 0x1b4a2d => Some (4,
	Move (V_TEMP 0xb4800) (Extract 127 0 (Var R_YMM0)) $;
	Move (V_TEMP 0xb4880) (Extract 7 0 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4900) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_YMM3)) (Var (V_TEMP 0xb4880)))) $;
	Move (V_TEMP 0xb4980) (Extract 7 0 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4900)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4980))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4900)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb4a00) (Extract 15 8 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4a80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 15 8 (Var R_YMM3)) (Var (V_TEMP 0xb4a00)))) $;
	Move (V_TEMP 0xb4b00) (Extract 15 8 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4a80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4b00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4a80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb4b80) (Extract 23 16 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4c00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 23 16 (Var R_YMM3)) (Var (V_TEMP 0xb4b80)))) $;
	Move (V_TEMP 0xb4c80) (Extract 23 16 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4c00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4c80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4c00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb4d00) (Extract 31 24 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4d80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 24 (Var R_YMM3)) (Var (V_TEMP 0xb4d00)))) $;
	Move (V_TEMP 0xb4e00) (Extract 31 24 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4d80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4e00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4d80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb4e80) (Extract 39 32 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4f00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 39 32 (Var R_YMM3)) (Var (V_TEMP 0xb4e80)))) $;
	Move (V_TEMP 0xb4f80) (Extract 39 32 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4f00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4f80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4f00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5000) (Extract 47 40 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5080) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 47 40 (Var R_YMM3)) (Var (V_TEMP 0xb5000)))) $;
	Move (V_TEMP 0xb5100) (Extract 47 40 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5080)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5100))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5080)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5180) (Extract 55 48 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5200) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 55 48 (Var R_YMM3)) (Var (V_TEMP 0xb5180)))) $;
	Move (V_TEMP 0xb5280) (Extract 55 48 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5200)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5280))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5200)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5300) (Extract 63 56 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5380) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 63 56 (Var R_YMM3)) (Var (V_TEMP 0xb5300)))) $;
	Move (V_TEMP 0xb5400) (Extract 63 56 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5380)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5400))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5380)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5480) (Extract 71 64 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 71 64 (Var R_YMM3)) (Var (V_TEMP 0xb5480)))) $;
	Move (V_TEMP 0xb5580) (Extract 71 64 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5500)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5580))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5500)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5600) (Extract 79 72 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5680) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 79 72 (Var R_YMM3)) (Var (V_TEMP 0xb5600)))) $;
	Move (V_TEMP 0xb5700) (Extract 79 72 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5680)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5700))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5680)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5780) (Extract 87 80 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5800) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 87 80 (Var R_YMM3)) (Var (V_TEMP 0xb5780)))) $;
	Move (V_TEMP 0xb5880) (Extract 87 80 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5800)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5880))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5800)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5900) (Extract 95 88 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5980) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 95 88 (Var R_YMM3)) (Var (V_TEMP 0xb5900)))) $;
	Move (V_TEMP 0xb5a00) (Extract 95 88 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5980)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5a00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5980)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5a80) (Extract 103 96 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5b00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 103 96 (Var R_YMM3)) (Var (V_TEMP 0xb5a80)))) $;
	Move (V_TEMP 0xb5b80) (Extract 103 96 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5b00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5b80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5b00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5c00) (Extract 111 104 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5c80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 111 104 (Var R_YMM3)) (Var (V_TEMP 0xb5c00)))) $;
	Move (V_TEMP 0xb5d00) (Extract 111 104 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5c80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5d00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5c80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5d80) (Extract 119 112 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5e00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 119 112 (Var R_YMM3)) (Var (V_TEMP 0xb5d80)))) $;
	Move (V_TEMP 0xb5e80) (Extract 119 112 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5e00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5e80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5e00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xb5f00) (Extract 127 120 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5f80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 127 120 (Var R_YMM3)) (Var (V_TEMP 0xb5f00)))) $;
	Move (V_TEMP 0xb6000) (Extract 127 120 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5f80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb6000))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5f80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001b4a31: PMAXUB XMM4,XMM2 *)
(*    1788465: PMAXUB XMM4,XMM2 *)
| 0x1b4a31 => Some (4,
	Move (V_TEMP 0xb4800) (Extract 127 0 (Var R_YMM2)) $;
	Move (V_TEMP 0xb4880) (Extract 7 0 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4900) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_YMM4)) (Var (V_TEMP 0xb4880)))) $;
	Move (V_TEMP 0xb4980) (Extract 7 0 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4900)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4980))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4900)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 8 (Var R_YMM4)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb4a00) (Extract 15 8 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4a80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 15 8 (Var R_YMM4)) (Var (V_TEMP 0xb4a00)))) $;
	Move (V_TEMP 0xb4b00) (Extract 15 8 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4a80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4b00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4a80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 16 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb4b80) (Extract 23 16 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4c00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 23 16 (Var R_YMM4)) (Var (V_TEMP 0xb4b80)))) $;
	Move (V_TEMP 0xb4c80) (Extract 23 16 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4c00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4c80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4c00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 24 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb4d00) (Extract 31 24 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4d80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 24 (Var R_YMM4)) (Var (V_TEMP 0xb4d00)))) $;
	Move (V_TEMP 0xb4e00) (Extract 31 24 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4d80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4e00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4d80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb4e80) (Extract 39 32 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4f00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 39 32 (Var R_YMM4)) (Var (V_TEMP 0xb4e80)))) $;
	Move (V_TEMP 0xb4f80) (Extract 39 32 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4f00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4f80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4f00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 40 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5000) (Extract 47 40 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5080) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 47 40 (Var R_YMM4)) (Var (V_TEMP 0xb5000)))) $;
	Move (V_TEMP 0xb5100) (Extract 47 40 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5080)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5100))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5080)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 48 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5180) (Extract 55 48 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5200) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 55 48 (Var R_YMM4)) (Var (V_TEMP 0xb5180)))) $;
	Move (V_TEMP 0xb5280) (Extract 55 48 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5200)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5280))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5200)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 56 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5300) (Extract 63 56 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5380) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 63 56 (Var R_YMM4)) (Var (V_TEMP 0xb5300)))) $;
	Move (V_TEMP 0xb5400) (Extract 63 56 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5380)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5400))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5380)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5480) (Extract 71 64 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 71 64 (Var R_YMM4)) (Var (V_TEMP 0xb5480)))) $;
	Move (V_TEMP 0xb5580) (Extract 71 64 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5500)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5580))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5500)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 72 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5600) (Extract 79 72 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5680) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 79 72 (Var R_YMM4)) (Var (V_TEMP 0xb5600)))) $;
	Move (V_TEMP 0xb5700) (Extract 79 72 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5680)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5700))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5680)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 80 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5780) (Extract 87 80 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5800) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 87 80 (Var R_YMM4)) (Var (V_TEMP 0xb5780)))) $;
	Move (V_TEMP 0xb5880) (Extract 87 80 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5800)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5880))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5800)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 88 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5900) (Extract 95 88 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5980) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 95 88 (Var R_YMM4)) (Var (V_TEMP 0xb5900)))) $;
	Move (V_TEMP 0xb5a00) (Extract 95 88 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5980)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5a00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5980)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5a80) (Extract 103 96 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5b00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 103 96 (Var R_YMM4)) (Var (V_TEMP 0xb5a80)))) $;
	Move (V_TEMP 0xb5b80) (Extract 103 96 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5b00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5b80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5b00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 104 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5c00) (Extract 111 104 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5c80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 111 104 (Var R_YMM4)) (Var (V_TEMP 0xb5c00)))) $;
	Move (V_TEMP 0xb5d00) (Extract 111 104 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5c80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5d00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5c80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 112 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5d80) (Extract 119 112 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5e00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 119 112 (Var R_YMM4)) (Var (V_TEMP 0xb5d80)))) $;
	Move (V_TEMP 0xb5e80) (Extract 119 112 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5e00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5e80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5e00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 120 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5f00) (Extract 127 120 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5f80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 127 120 (Var R_YMM4)) (Var (V_TEMP 0xb5f00)))) $;
	Move (V_TEMP 0xb6000) (Extract 127 120 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5f80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb6000))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5f80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM4))))
)

(* 0x001b4a35: PMAXUB XMM4,XMM3 *)
(*    1788469: PMAXUB XMM4,XMM3 *)
| 0x1b4a35 => Some (4,
	Move (V_TEMP 0xb4800) (Extract 127 0 (Var R_YMM3)) $;
	Move (V_TEMP 0xb4880) (Extract 7 0 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4900) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 7 0 (Var R_YMM4)) (Var (V_TEMP 0xb4880)))) $;
	Move (V_TEMP 0xb4980) (Extract 7 0 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4900)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4980))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4900)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 8 (Var R_YMM4)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb4a00) (Extract 15 8 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4a80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 15 8 (Var R_YMM4)) (Var (V_TEMP 0xb4a00)))) $;
	Move (V_TEMP 0xb4b00) (Extract 15 8 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4a80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4b00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4a80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 16 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb4b80) (Extract 23 16 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4c00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 23 16 (Var R_YMM4)) (Var (V_TEMP 0xb4b80)))) $;
	Move (V_TEMP 0xb4c80) (Extract 23 16 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4c00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4c80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4c00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 24 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb4d00) (Extract 31 24 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4d80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 24 (Var R_YMM4)) (Var (V_TEMP 0xb4d00)))) $;
	Move (V_TEMP 0xb4e00) (Extract 31 24 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4d80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4e00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4d80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 32 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb4e80) (Extract 39 32 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb4f00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 39 32 (Var R_YMM4)) (Var (V_TEMP 0xb4e80)))) $;
	Move (V_TEMP 0xb4f80) (Extract 39 32 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb4f00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb4f80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb4f00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 40 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5000) (Extract 47 40 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5080) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 47 40 (Var R_YMM4)) (Var (V_TEMP 0xb5000)))) $;
	Move (V_TEMP 0xb5100) (Extract 47 40 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5080)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5100))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5080)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 48 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5180) (Extract 55 48 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5200) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 55 48 (Var R_YMM4)) (Var (V_TEMP 0xb5180)))) $;
	Move (V_TEMP 0xb5280) (Extract 55 48 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5200)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5280))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5200)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 56 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5300) (Extract 63 56 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5380) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 63 56 (Var R_YMM4)) (Var (V_TEMP 0xb5300)))) $;
	Move (V_TEMP 0xb5400) (Extract 63 56 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5380)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5400))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5380)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 64 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5480) (Extract 71 64 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 71 64 (Var R_YMM4)) (Var (V_TEMP 0xb5480)))) $;
	Move (V_TEMP 0xb5580) (Extract 71 64 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5500)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5580))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5500)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 72 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5600) (Extract 79 72 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5680) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 79 72 (Var R_YMM4)) (Var (V_TEMP 0xb5600)))) $;
	Move (V_TEMP 0xb5700) (Extract 79 72 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5680)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5700))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5680)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 80 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5780) (Extract 87 80 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5800) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 87 80 (Var R_YMM4)) (Var (V_TEMP 0xb5780)))) $;
	Move (V_TEMP 0xb5880) (Extract 87 80 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5800)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5880))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5800)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 88 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5900) (Extract 95 88 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5980) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 95 88 (Var R_YMM4)) (Var (V_TEMP 0xb5900)))) $;
	Move (V_TEMP 0xb5a00) (Extract 95 88 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5980)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5a00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5980)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 96 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5a80) (Extract 103 96 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5b00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 103 96 (Var R_YMM4)) (Var (V_TEMP 0xb5a80)))) $;
	Move (V_TEMP 0xb5b80) (Extract 103 96 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5b00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5b80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5b00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 104 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5c00) (Extract 111 104 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5c80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 111 104 (Var R_YMM4)) (Var (V_TEMP 0xb5c00)))) $;
	Move (V_TEMP 0xb5d00) (Extract 111 104 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5c80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5d00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5c80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 112 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5d80) (Extract 119 112 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5e00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 119 112 (Var R_YMM4)) (Var (V_TEMP 0xb5d80)))) $;
	Move (V_TEMP 0xb5e80) (Extract 119 112 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5e00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb5e80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5e00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 120 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM4)))) $;
	Move (V_TEMP 0xb5f00) (Extract 127 120 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0xb5f80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 127 120 (Var R_YMM4)) (Var (V_TEMP 0xb5f00)))) $;
	Move (V_TEMP 0xb6000) (Extract 127 120 (Var (V_TEMP 0xb4800))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb5f80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb6000))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb5f80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM4))) $;
	Move R_YMM4 (Concat (Extract 255 128 (Var R_YMM4)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM4))))
)

(* 0x001b4a39: PMOVMSKB EAX,XMM4 *)
(*    1788473: PMOVMSKB EAX,XMM4 *)
| 0x1b4a39 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM4)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4a3d: ADD RDI,0x40 *)
(*    1788477: ADD RDI,0x40 *)
| 0x1b4a3d => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4a41: TEST EAX,EAX *)
(*    1788481: TEST EAX,EAX *)
| 0x1b4a41 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4a43: JZ 0x001b4a00 *)
(*    1788483: JZ 0x001b4a00 *)
| 0x1b4a43 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1b4a00 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4a45: SUB RDI,0x40 *)
(*    1788485: SUB RDI,0x40 *)
| 0x1b4a45 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4a49: PMOVMSKB EAX,XMM0 *)
(*    1788489: PMOVMSKB EAX,XMM0 *)
| 0x1b4a49 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4a4d: TEST EAX,EAX *)
(*    1788493: TEST EAX,EAX *)
| 0x1b4a4d => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4a4f: JNZ 0x001b4b30 *)
(*    1788495: JNZ 0x001b4b30 *)
| 0x1b4a4f => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b30 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4a55: PMOVMSKB EAX,XMM2 *)
(*    1788501: PMOVMSKB EAX,XMM2 *)
| 0x1b4a55 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4a59: TEST EAX,EAX *)
(*    1788505: TEST EAX,EAX *)
| 0x1b4a59 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4a5b: JNZ 0x001b4b40 *)
(*    1788507: JNZ 0x001b4b40 *)
| 0x1b4a5b => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b40 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4a61: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
(*    1788513: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
| 0x1b4a61 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4a66: PCMPEQB XMM3,XMM1 *)
(*    1788518: PCMPEQB XMM3,XMM1 *)
| 0x1b4a66 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001b4a6a: PCMPEQB XMM1,xmmword ptr [RDI + 0x30] *)
(*    1788522: PCMPEQB XMM1,xmmword ptr [RDI + 0x30] *)
| 0x1b4a6a => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM1 (Concat (Extract 255 8 (Var R_YMM1)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM1 (Concat (Extract 255 16 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM1 (Concat (Extract 255 24 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM1 (Concat (Extract 255 40 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM1 (Concat (Extract 255 48 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM1 (Concat (Extract 255 56 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM1 (Concat (Extract 255 72 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM1 (Concat (Extract 255 80 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM1 (Concat (Extract 255 88 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM1 (Concat (Extract 255 104 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM1 (Concat (Extract 255 112 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM1 (Concat (Extract 255 120 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM1))))
)

(* 0x001b4a6f: PMOVMSKB EAX,XMM3 *)
(*    1788527: PMOVMSKB EAX,XMM3 *)
| 0x1b4a6f => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4a73: TEST EAX,EAX *)
(*    1788531: TEST EAX,EAX *)
| 0x1b4a73 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4a75: JNZ 0x001b4b50 *)
(*    1788533: JNZ 0x001b4b50 *)
| 0x1b4a75 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b50 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4a7b: PMOVMSKB EAX,XMM1 *)
(*    1788539: PMOVMSKB EAX,XMM1 *)
| 0x1b4a7b => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4a7f: BSF EAX,EAX *)
(*    1788543: BSF EAX,EAX *)
| 0x1b4a7f => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4a82: LEA RAX,[RDI + RAX*0x1 + 0x30] *)
(*    1788546: LEA RAX,[RDI + RAX*0x1 + 0x30] *)
| 0x1b4a82 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0x30 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RAX (Var (V_TEMP 0x5080))
)

(* 0x001b4a87: RET *)
(*    1788551: RET *)
| 0x1b4a87 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4a90: ADD EDX,0x20 *)
(*    1788560: ADD EDX,0x20 *)
| 0x1b4a90 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4a93: JLE 0x001b4af0 *)
(*    1788563: JLE 0x001b4af0 *)
| 0x1b4a93 => Some (2,
	Move (V_TEMP 0x12f80) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 0x13080) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Var (V_TEMP 0x12f80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13080))) (
		Jmp (Word 0x1b4af0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4a95: MOVDQA XMM0,xmmword ptr [RDI] *)
(*    1788565: MOVDQA XMM0,xmmword ptr [RDI] *)
| 0x1b4a95 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4a99: PCMPEQB XMM0,XMM1 *)
(*    1788569: PCMPEQB XMM0,XMM1 *)
| 0x1b4a99 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001b4a9d: PMOVMSKB EAX,XMM0 *)
(*    1788573: PMOVMSKB EAX,XMM0 *)
| 0x1b4a9d => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4aa1: TEST EAX,EAX *)
(*    1788577: TEST EAX,EAX *)
| 0x1b4aa1 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4aa3: JNZ 0x001b4b30 *)
(*    1788579: JNZ 0x001b4b30 *)
| 0x1b4aa3 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b30 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4aa9: MOVDQA XMM2,xmmword ptr [RDI + 0x10] *)
(*    1788585: MOVDQA XMM2,xmmword ptr [RDI + 0x10] *)
| 0x1b4aa9 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4aae: PCMPEQB XMM2,XMM1 *)
(*    1788590: PCMPEQB XMM2,XMM1 *)
| 0x1b4aae => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001b4ab2: PMOVMSKB EAX,XMM2 *)
(*    1788594: PMOVMSKB EAX,XMM2 *)
| 0x1b4ab2 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM2)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4ab6: TEST EAX,EAX *)
(*    1788598: TEST EAX,EAX *)
| 0x1b4ab6 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4ab8: JNZ 0x001b4b40 *)
(*    1788600: JNZ 0x001b4b40 *)
| 0x1b4ab8 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b40 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4abe: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
(*    1788606: MOVDQA XMM3,xmmword ptr [RDI + 0x20] *)
| 0x1b4abe => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4ac3: PCMPEQB XMM3,XMM1 *)
(*    1788611: PCMPEQB XMM3,XMM1 *)
| 0x1b4ac3 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001b4ac7: PMOVMSKB EAX,XMM3 *)
(*    1788615: PMOVMSKB EAX,XMM3 *)
| 0x1b4ac7 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM3)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4acb: TEST EAX,EAX *)
(*    1788619: TEST EAX,EAX *)
| 0x1b4acb => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4acd: JNZ 0x001b4b80 *)
(*    1788621: JNZ 0x001b4b80 *)
| 0x1b4acd => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b80 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4ad3: SUB EDX,0x10 *)
(*    1788627: SUB EDX,0x10 *)
| 0x1b4ad3 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RDX)) (Word 0x10 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4ad6: JLE 0x001b4ba0 *)
(*    1788630: JLE 0x001b4ba0 *)
| 0x1b4ad6 => Some (6,
	Move (V_TEMP 0x12f80) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 0x13080) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Var (V_TEMP 0x12f80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13080))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4adc: PCMPEQB XMM1,xmmword ptr [RDI + 0x30] *)
(*    1788636: PCMPEQB XMM1,xmmword ptr [RDI + 0x30] *)
| 0x1b4adc => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM1 (Concat (Extract 255 8 (Var R_YMM1)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM1 (Concat (Extract 255 16 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM1 (Concat (Extract 255 24 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM1 (Concat (Extract 255 40 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM1 (Concat (Extract 255 48 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM1 (Concat (Extract 255 56 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM1 (Concat (Extract 255 72 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM1 (Concat (Extract 255 80 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM1 (Concat (Extract 255 88 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM1 (Concat (Extract 255 104 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM1 (Concat (Extract 255 112 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM1 (Concat (Extract 255 120 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM1))))
)

(* 0x001b4ae1: PMOVMSKB EAX,XMM1 *)
(*    1788641: PMOVMSKB EAX,XMM1 *)
| 0x1b4ae1 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4ae5: TEST EAX,EAX *)
(*    1788645: TEST EAX,EAX *)
| 0x1b4ae5 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4ae7: JNZ 0x001b4b90 *)
(*    1788647: JNZ 0x001b4b90 *)
| 0x1b4ae7 => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b90 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4aed: XOR EAX,EAX *)
(*    1788653: XOR EAX,EAX *)
| 0x1b4aed => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4aef: RET *)
(*    1788655: RET *)
| 0x1b4aef => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4af0: ADD EDX,0x20 *)
(*    1788656: ADD EDX,0x20 *)
| 0x1b4af0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0x20 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4af3: MOVDQA XMM0,xmmword ptr [RDI] *)
(*    1788659: MOVDQA XMM0,xmmword ptr [RDI] *)
| 0x1b4af3 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RDI) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001b4af7: PCMPEQB XMM0,XMM1 *)
(*    1788663: PCMPEQB XMM0,XMM1 *)
| 0x1b4af7 => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM1)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001b4afb: PMOVMSKB EAX,XMM0 *)
(*    1788667: PMOVMSKB EAX,XMM0 *)
| 0x1b4afb => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM0)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4aff: TEST EAX,EAX *)
(*    1788671: TEST EAX,EAX *)
| 0x1b4aff => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b01: JNZ 0x001b4b60 *)
(*    1788673: JNZ 0x001b4b60 *)
| 0x1b4b01 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b60 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4b03: SUB EDX,0x10 *)
(*    1788675: SUB EDX,0x10 *)
| 0x1b4b03 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 31 0 (Var R_RDX)) (Word 0x10 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RDX)) (Word 0x10 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b06: JBE 0x001b4ba0 *)
(*    1788678: JBE 0x001b4ba0 *)
| 0x1b4b06 => Some (6,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4b0c: PCMPEQB XMM1,xmmword ptr [RDI + 0x10] *)
(*    1788684: PCMPEQB XMM1,xmmword ptr [RDI + 0x10] *)
| 0x1b4b0c => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM1)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM1 (Concat (Extract 255 8 (Var R_YMM1)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM1)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM1 (Concat (Extract 255 16 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM1)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM1 (Concat (Extract 255 24 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM1)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM1 (Concat (Extract 255 32 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM1)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM1 (Concat (Extract 255 40 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM1)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM1 (Concat (Extract 255 48 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM1)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM1 (Concat (Extract 255 56 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM1)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM1)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM1 (Concat (Extract 255 72 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM1)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM1 (Concat (Extract 255 80 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM1)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM1 (Concat (Extract 255 88 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM1)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM1 (Concat (Extract 255 96 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM1)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM1 (Concat (Extract 255 104 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM1)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM1 (Concat (Extract 255 112 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM1)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM1 (Concat (Extract 255 120 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM1)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM1))))
)

(* 0x001b4b11: PMOVMSKB EAX,XMM1 *)
(*    1788689: PMOVMSKB EAX,XMM1 *)
| 0x1b4b11 => Some (4,
	Move (V_TEMP 0xbad00) (Word 0x0 16) $;
	Move (V_TEMP 0xbaf00) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffe 16)) $;
	Move (V_TEMP 0xbad80) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 7 128)) $;
	Move (V_TEMP 0xbae00) (Extract 7 0 (Var (V_TEMP 0xbad80))) $;
	Move (V_TEMP 0xbae80) (BinOp OP_AND (Var (V_TEMP 0xbae00)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbaf80) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbae80))) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbaf00)) (Var (V_TEMP 0xbaf80))) $;
	Move (V_TEMP 0xbb180) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffd 16)) $;
	Move (V_TEMP 0xbb000) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 15 128)) $;
	Move (V_TEMP 0xbb080) (Extract 7 0 (Var (V_TEMP 0xbb000))) $;
	Move (V_TEMP 0xbb100) (BinOp OP_AND (Var (V_TEMP 0xbb080)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb200) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb100))) $;
	Move (V_TEMP 0xbb280) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb200)) (Word 1 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb180)) (Var (V_TEMP 0xbb280))) $;
	Move (V_TEMP 0xbb480) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfffb 16)) $;
	Move (V_TEMP 0xbb300) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 23 128)) $;
	Move (V_TEMP 0xbb380) (Extract 7 0 (Var (V_TEMP 0xbb300))) $;
	Move (V_TEMP 0xbb400) (BinOp OP_AND (Var (V_TEMP 0xbb380)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb500) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb400))) $;
	Move (V_TEMP 0xbb580) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb500)) (Word 2 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb480)) (Var (V_TEMP 0xbb580))) $;
	Move (V_TEMP 0xbb780) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfff7 16)) $;
	Move (V_TEMP 0xbb600) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 31 128)) $;
	Move (V_TEMP 0xbb680) (Extract 7 0 (Var (V_TEMP 0xbb600))) $;
	Move (V_TEMP 0xbb700) (BinOp OP_AND (Var (V_TEMP 0xbb680)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbb800) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbb700))) $;
	Move (V_TEMP 0xbb880) (BinOp OP_LSHIFT (Var (V_TEMP 0xbb800)) (Word 3 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbb780)) (Var (V_TEMP 0xbb880))) $;
	Move (V_TEMP 0xbba80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffef 16)) $;
	Move (V_TEMP 0xbb900) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 39 128)) $;
	Move (V_TEMP 0xbb980) (Extract 7 0 (Var (V_TEMP 0xbb900))) $;
	Move (V_TEMP 0xbba00) (BinOp OP_AND (Var (V_TEMP 0xbb980)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbb00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbba00))) $;
	Move (V_TEMP 0xbbb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbb00)) (Word 4 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbba80)) (Var (V_TEMP 0xbbb80))) $;
	Move (V_TEMP 0xbbd80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffdf 16)) $;
	Move (V_TEMP 0xbbc00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 47 128)) $;
	Move (V_TEMP 0xbbc80) (Extract 7 0 (Var (V_TEMP 0xbbc00))) $;
	Move (V_TEMP 0xbbd00) (BinOp OP_AND (Var (V_TEMP 0xbbc80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbbe00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbbd00))) $;
	Move (V_TEMP 0xbbe80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbbe00)) (Word 5 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbbd80)) (Var (V_TEMP 0xbbe80))) $;
	Move (V_TEMP 0xbc080) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xffbf 16)) $;
	Move (V_TEMP 0xbbf00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 55 128)) $;
	Move (V_TEMP 0xbbf80) (Extract 7 0 (Var (V_TEMP 0xbbf00))) $;
	Move (V_TEMP 0xbc000) (BinOp OP_AND (Var (V_TEMP 0xbbf80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc100) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc000))) $;
	Move (V_TEMP 0xbc180) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc100)) (Word 6 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc080)) (Var (V_TEMP 0xbc180))) $;
	Move (V_TEMP 0xbc380) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xff7f 16)) $;
	Move (V_TEMP 0xbc200) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 63 128)) $;
	Move (V_TEMP 0xbc280) (Extract 7 0 (Var (V_TEMP 0xbc200))) $;
	Move (V_TEMP 0xbc300) (BinOp OP_AND (Var (V_TEMP 0xbc280)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc400) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc300))) $;
	Move (V_TEMP 0xbc480) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc400)) (Word 7 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc380)) (Var (V_TEMP 0xbc480))) $;
	Move (V_TEMP 0xbc680) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfeff 16)) $;
	Move (V_TEMP 0xbc500) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 71 128)) $;
	Move (V_TEMP 0xbc580) (Extract 7 0 (Var (V_TEMP 0xbc500))) $;
	Move (V_TEMP 0xbc600) (BinOp OP_AND (Var (V_TEMP 0xbc580)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbc700) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc600))) $;
	Move (V_TEMP 0xbc780) (BinOp OP_LSHIFT (Var (V_TEMP 0xbc700)) (Word 8 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc680)) (Var (V_TEMP 0xbc780))) $;
	Move (V_TEMP 0xbc980) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfdff 16)) $;
	Move (V_TEMP 0xbc800) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 79 128)) $;
	Move (V_TEMP 0xbc880) (Extract 7 0 (Var (V_TEMP 0xbc800))) $;
	Move (V_TEMP 0xbc900) (BinOp OP_AND (Var (V_TEMP 0xbc880)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbca00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbc900))) $;
	Move (V_TEMP 0xbca80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbca00)) (Word 9 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbc980)) (Var (V_TEMP 0xbca80))) $;
	Move (V_TEMP 0xbcc80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xfbff 16)) $;
	Move (V_TEMP 0xbcb00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 87 128)) $;
	Move (V_TEMP 0xbcb80) (Extract 7 0 (Var (V_TEMP 0xbcb00))) $;
	Move (V_TEMP 0xbcc00) (BinOp OP_AND (Var (V_TEMP 0xbcb80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbcd00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcc00))) $;
	Move (V_TEMP 0xbcd80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbcd00)) (Word 10 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcc80)) (Var (V_TEMP 0xbcd80))) $;
	Move (V_TEMP 0xbcf80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xf7ff 16)) $;
	Move (V_TEMP 0xbce00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 95 128)) $;
	Move (V_TEMP 0xbce80) (Extract 7 0 (Var (V_TEMP 0xbce00))) $;
	Move (V_TEMP 0xbcf00) (BinOp OP_AND (Var (V_TEMP 0xbce80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd000) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbcf00))) $;
	Move (V_TEMP 0xbd080) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd000)) (Word 11 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbcf80)) (Var (V_TEMP 0xbd080))) $;
	Move (V_TEMP 0xbd280) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xefff 16)) $;
	Move (V_TEMP 0xbd100) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 103 128)) $;
	Move (V_TEMP 0xbd180) (Extract 7 0 (Var (V_TEMP 0xbd100))) $;
	Move (V_TEMP 0xbd200) (BinOp OP_AND (Var (V_TEMP 0xbd180)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd300) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd200))) $;
	Move (V_TEMP 0xbd380) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd300)) (Word 12 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd280)) (Var (V_TEMP 0xbd380))) $;
	Move (V_TEMP 0xbd580) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xdfff 16)) $;
	Move (V_TEMP 0xbd400) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 111 128)) $;
	Move (V_TEMP 0xbd480) (Extract 7 0 (Var (V_TEMP 0xbd400))) $;
	Move (V_TEMP 0xbd500) (BinOp OP_AND (Var (V_TEMP 0xbd480)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd600) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd500))) $;
	Move (V_TEMP 0xbd680) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd600)) (Word 13 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd580)) (Var (V_TEMP 0xbd680))) $;
	Move (V_TEMP 0xbd880) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0xbfff 16)) $;
	Move (V_TEMP 0xbd700) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 119 128)) $;
	Move (V_TEMP 0xbd780) (Extract 7 0 (Var (V_TEMP 0xbd700))) $;
	Move (V_TEMP 0xbd800) (BinOp OP_AND (Var (V_TEMP 0xbd780)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbd900) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbd800))) $;
	Move (V_TEMP 0xbd980) (BinOp OP_LSHIFT (Var (V_TEMP 0xbd900)) (Word 14 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbd880)) (Var (V_TEMP 0xbd980))) $;
	Move (V_TEMP 0xbdb80) (BinOp OP_AND (Var (V_TEMP 0xbad00)) (Word 0x7fff 16)) $;
	Move (V_TEMP 0xbda00) (BinOp OP_RSHIFT (Extract 127 0 (Var R_YMM1)) (Word 127 128)) $;
	Move (V_TEMP 0xbda80) (Extract 7 0 (Var (V_TEMP 0xbda00))) $;
	Move (V_TEMP 0xbdb00) (BinOp OP_AND (Var (V_TEMP 0xbda80)) (Word 0x1 8)) $;
	Move (V_TEMP 0xbdc00) (Cast CAST_UNSIGNED 16 (Var (V_TEMP 0xbdb00))) $;
	Move (V_TEMP 0xbdc80) (BinOp OP_LSHIFT (Var (V_TEMP 0xbdc00)) (Word 15 16)) $;
	Move (V_TEMP 0xbad00) (BinOp OP_OR (Var (V_TEMP 0xbdb80)) (Var (V_TEMP 0xbdc80))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x001b4b15: TEST EAX,EAX *)
(*    1788693: TEST EAX,EAX *)
| 0x1b4b15 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b17: JNZ 0x001b4b70 *)
(*    1788695: JNZ 0x001b4b70 *)
| 0x1b4b17 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1b4b70 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4b19: XOR EAX,EAX *)
(*    1788697: XOR EAX,EAX *)
| 0x1b4b19 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b1b: RET *)
(*    1788699: RET *)
| 0x1b4b1b => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4b20: BSF EAX,EAX *)
(*    1788704: BSF EAX,EAX *)
| 0x1b4b20 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4b23: LEA RAX,[RAX + RDI*0x1 + -0x10] *)
(*    1788707: LEA RAX,[RAX + RDI*0x1 + -0x10] *)
| 0x1b4b23 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RAX (Var (V_TEMP 0x5080))
)

(* 0x001b4b28: RET *)
(*    1788712: RET *)
| 0x1b4b28 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4b30: BSF EAX,EAX *)
(*    1788720: BSF EAX,EAX *)
| 0x1b4b30 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4b33: ADD RAX,RDI *)
(*    1788723: ADD RAX,RDI *)
| 0x1b4b33 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b36: RET *)
(*    1788726: RET *)
| 0x1b4b36 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4b40: BSF EAX,EAX *)
(*    1788736: BSF EAX,EAX *)
| 0x1b4b40 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4b43: LEA RAX,[RAX + RDI*0x1 + 0x10] *)
(*    1788739: LEA RAX,[RAX + RDI*0x1 + 0x10] *)
| 0x1b4b43 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0x10 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RAX (Var (V_TEMP 0x5080))
)

(* 0x001b4b48: RET *)
(*    1788744: RET *)
| 0x1b4b48 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4b50: BSF EAX,EAX *)
(*    1788752: BSF EAX,EAX *)
| 0x1b4b50 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4b53: LEA RAX,[RAX + RDI*0x1 + 0x20] *)
(*    1788755: LEA RAX,[RAX + RDI*0x1 + 0x20] *)
| 0x1b4b53 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0x20 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RAX (Var (V_TEMP 0x5080))
)

(* 0x001b4b58: RET *)
(*    1788760: RET *)
| 0x1b4b58 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4b60: BSF EAX,EAX *)
(*    1788768: BSF EAX,EAX *)
| 0x1b4b60 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4b63: SUB RDX,RAX *)
(*    1788771: SUB RDX,RAX *)
| 0x1b4b63 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b66: JBE 0x001b4ba0 *)
(*    1788774: JBE 0x001b4ba0 *)
| 0x1b4b66 => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4b68: ADD RAX,RDI *)
(*    1788776: ADD RAX,RDI *)
| 0x1b4b68 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b6b: RET *)
(*    1788779: RET *)
| 0x1b4b6b => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4b70: BSF EAX,EAX *)
(*    1788784: BSF EAX,EAX *)
| 0x1b4b70 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4b73: SUB RDX,RAX *)
(*    1788787: SUB RDX,RAX *)
| 0x1b4b73 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b76: JBE 0x001b4ba0 *)
(*    1788790: JBE 0x001b4ba0 *)
| 0x1b4b76 => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4b78: LEA RAX,[RDI + RAX*0x1 + 0x10] *)
(*    1788792: LEA RAX,[RDI + RAX*0x1 + 0x10] *)
| 0x1b4b78 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0x10 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RAX (Var (V_TEMP 0x5080))
)

(* 0x001b4b7d: RET *)
(*    1788797: RET *)
| 0x1b4b7d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4b80: BSF EAX,EAX *)
(*    1788800: BSF EAX,EAX *)
| 0x1b4b80 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4b83: SUB RDX,RAX *)
(*    1788803: SUB RDX,RAX *)
| 0x1b4b83 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b86: JBE 0x001b4ba0 *)
(*    1788806: JBE 0x001b4ba0 *)
| 0x1b4b86 => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4b88: LEA RAX,[RDI + RAX*0x1 + 0x20] *)
(*    1788808: LEA RAX,[RDI + RAX*0x1 + 0x20] *)
| 0x1b4b88 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0x20 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RAX (Var (V_TEMP 0x5080))
)

(* 0x001b4b8d: RET *)
(*    1788813: RET *)
| 0x1b4b8d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4b90: BSF EAX,EAX *)
(*    1788816: BSF EAX,EAX *)
| 0x1b4b90 => Some (3,
	Move (V_TEMP 0x34200) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x34300) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34300))) (
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	) (* else *) (
		Rep (Word 33 32) (
			Move (V_TEMP 0x34200) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Var (V_TEMP 0x34200)))) (Word 0x1 32))) (Word 0x0 32))))) (Var (V_TEMP 0x34200)) (BinOp OP_PLUS (Var (V_TEMP 0x34200)) (Word 0x1 32)))
		) $;
		Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x34200))) $;
		Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
	)
)

(* 0x001b4b93: SUB RDX,RAX *)
(*    1788819: SUB RDX,RAX *)
| 0x1b4b93 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4b96: JBE 0x001b4ba0 *)
(*    1788822: JBE 0x001b4ba0 *)
| 0x1b4b96 => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1b4ba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001b4b98: LEA RAX,[RDI + RAX*0x1 + 0x30] *)
(*    1788824: LEA RAX,[RDI + RAX*0x1 + 0x30] *)
| 0x1b4b98 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0x30 64) (Var R_RDI)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move R_RAX (Var (V_TEMP 0x5080))
)

(* 0x001b4b9d: RET *)
(*    1788829: RET *)
| 0x1b4b9d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001b4ba0: XOR EAX,EAX *)
(*    1788832: XOR EAX,EAX *)
| 0x1b4ba0 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001b4ba2: RET *)
(*    1788834: RET *)
| 0x1b4ba2 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx memchr_sse2_amd64.
Proof. Picinae_typecheck. Qed.

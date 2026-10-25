(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: FUN_001baaf0 at 0x1baaf0
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition strnlen_sse2_amd64 : program := fun _ a => match a with

(* ---- FUN_001baaf0 ---- *)

(* 0x001baaf0: ENDBR64 *)
(*    1813232: ENDBR64 *)
| 0x1baaf0 => Some (4,
	Nop
)

(* 0x001baaf4: TEST RSI,RSI *)
(*    1813236: TEST RSI,RSI *)
| 0x1baaf4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RSI) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baaf7: JNZ 0x001baafd *)
(*    1813239: JNZ 0x001baafd *)
| 0x1baaf7 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1baafd 64)
	) (* else *) (
		Nop
	)
)

(* 0x001baaf9: XOR RAX,RAX *)
(*    1813241: XOR RAX,RAX *)
| 0x1baaf9 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_XOR (Var R_RAX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baafc: RET *)
(*    1813244: RET *)
| 0x1baafc => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001baafd: ADD RSI,RDI *)
(*    1813245: ADD RSI,RDI *)
| 0x1baafd => Some (3,
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

(* 0x001bab00: MOV R10,RSI *)
(*    1813248: MOV R10,RSI *)
| 0x1bab00 => Some (3,
	Move R_R10 (Var R_RSI)
)

(* 0x001bab03: AND R10,-0x40 *)
(*    1813251: AND R10,-0x40 *)
| 0x1bab03 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R10 (BinOp OP_AND (Var R_R10) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab07: MOV R11,RSI *)
(*    1813255: MOV R11,RSI *)
| 0x1bab07 => Some (3,
	Move R_R11 (Var R_RSI)
)

(* 0x001bab0a: PXOR XMM0,XMM0 *)
(*    1813258: PXOR XMM0,XMM0 *)
| 0x1bab0a => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM0)) (Extract 127 0 (Var R_YMM0))))
)

(* 0x001bab0e: PXOR XMM1,XMM1 *)
(*    1813262: PXOR XMM1,XMM1 *)
| 0x1bab0e => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM1))))
)

(* 0x001bab12: PXOR XMM2,XMM2 *)
(*    1813266: PXOR XMM2,XMM2 *)
| 0x1bab12 => Some (4,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM2))))
)

(* 0x001bab16: PXOR XMM3,XMM3 *)
(*    1813270: PXOR XMM3,XMM3 *)
| 0x1bab16 => Some (4,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))))
)

(* 0x001bab1a: MOV RAX,RDI *)
(*    1813274: MOV RAX,RDI *)
| 0x1bab1a => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x001bab1d: MOV RCX,RDI *)
(*    1813277: MOV RCX,RDI *)
| 0x1bab1d => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001bab20: AND RCX,0xfff *)
(*    1813280: AND RCX,0xfff *)
| 0x1bab20 => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_AND (Var R_RCX) (Word 0xfff 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab27: CMP RCX,0xfcf *)
(*    1813287: CMP RCX,0xfcf *)
| 0x1bab27 => Some (7,
	Move (V_TEMP 0x3e680) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e680)) (Word 0xfcf 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e680)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0xfcf 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0xfcf 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xfcf 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3e780) (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0xfcf 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e780)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e780)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e780)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab2e: JA 0x001baba0 *)
(*    1813294: JA 0x001baba0 *)
| 0x1bab2e => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1baba0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001bab30: AND RAX,-0x10 *)
(*    1813296: AND RAX,-0x10 *)
| 0x1bab30 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_AND (Var R_RAX) (Word 0xfffffffffffffff0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab34: PCMPEQB XMM0,xmmword ptr [RAX] *)
(*    1813300: PCMPEQB XMM0,xmmword ptr [RAX] *)
| 0x1bab34 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001bab38: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
(*    1813304: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
| 0x1bab38 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
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

(* 0x001bab3d: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
(*    1813309: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
| 0x1bab3d => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001bab42: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
(*    1813314: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
| 0x1bab42 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001bab47: PMOVMSKB ESI,XMM0 *)
(*    1813319: PMOVMSKB ESI,XMM0 *)
| 0x1bab47 => Some (4,
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
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001bab4b: PMOVMSKB EDX,XMM1 *)
(*    1813323: PMOVMSKB EDX,XMM1 *)
| 0x1bab4b => Some (4,
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
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001bab4f: PMOVMSKB R8D,XMM2 *)
(*    1813327: PMOVMSKB R8D,XMM2 *)
| 0x1bab4f => Some (5,
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
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x001bab54: PMOVMSKB ECX,XMM3 *)
(*    1813332: PMOVMSKB ECX,XMM3 *)
| 0x1bab54 => Some (4,
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
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001bab58: SHL RDX,0x10 *)
(*    1813336: SHL RDX,0x10 *)
| 0x1bab58 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bab5c: SHL RCX,0x10 *)
(*    1813340: SHL RCX,0x10 *)
| 0x1bab5c => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bab60: OR RDX,RSI *)
(*    1813344: OR RDX,RSI *)
| 0x1bab60 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab63: OR RCX,R8 *)
(*    1813347: OR RCX,R8 *)
| 0x1bab63 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (Var R_RCX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab66: SHL RCX,0x20 *)
(*    1813350: SHL RCX,0x20 *)
| 0x1bab66 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bab6a: OR RDX,RCX *)
(*    1813354: OR RDX,RCX *)
| 0x1bab6a => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab6d: MOV RCX,RDI *)
(*    1813357: MOV RCX,RDI *)
| 0x1bab6d => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001bab70: XOR RCX,RAX *)
(*    1813360: XOR RCX,RAX *)
| 0x1bab70 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_XOR (Var R_RCX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab73: MOV RSI,R11 *)
(*    1813363: MOV RSI,R11 *)
| 0x1bab73 => Some (3,
	Move R_RSI (Var R_R11)
)

(* 0x001bab76: SUB RSI,RAX *)
(*    1813366: SUB RSI,RAX *)
| 0x1bab76 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab79: AND RAX,-0x40 *)
(*    1813369: AND RAX,-0x40 *)
| 0x1bab79 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab7d: TEST RSI,-0x40 *)
(*    1813373: TEST RSI,-0x40 *)
| 0x1bab7d => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Var R_RSI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bab84: JZ 0x001bac03 *)
(*    1813380: JZ 0x001bac03 *)
| 0x1bab84 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1bac03 64)
	) (* else *) (
		Nop
	)
)

(* 0x001bab86: SAR RDX,CL *)
(*    1813382: SAR RDX,CL *)
| 0x1bab86 => Some (3,
	Move (V_TEMP 0x68900) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x3f 8)) $;
	Move (V_TEMP 0x68980) (Var R_RDX) $;
	Move R_RDX (BinOp OP_ARSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x68900)))) $;
	Move (V_TEMP 0x2f000) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_MINUS (Var (V_TEMP 0x68900)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2f100) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68980)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f080)))) $;
	Move (V_TEMP 0x2f180) (BinOp OP_AND (Var (V_TEMP 0x2f100)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f180)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2f300) (BinOp OP_XOR (Var (V_TEMP 0x2f000)) (Word 1 8)) $;
	Move (V_TEMP 0x2f380) (BinOp OP_AND (Var (V_TEMP 0x2f300)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2f400) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Var (V_TEMP 0x2f280))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2f380)) (Var (V_TEMP 0x2f400)))) $;
	Move (V_TEMP 0x2f580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x68900)) (Word 0x1 8))) $;
	Move (V_TEMP 0x2f600) (BinOp OP_XOR (Var (V_TEMP 0x2f580)) (Word 1 8)) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_AND (Var (V_TEMP 0x2f600)) (Cast CAST_UNSIGNED 8 (Var R_OF)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bab89: TEST RDX,RDX *)
(*    1813385: TEST RDX,RDX *)
| 0x1bab89 => Some (3,
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

(* 0x001bab8c: JZ 0x001bac30 *)
(*    1813388: JZ 0x001bac30 *)
| 0x1bab8c => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x1bac30 64)
	) (* else *) (
		Nop
	)
)

(* 0x001bab92: BSF RAX,RDX *)
(*    1813394: BSF RAX,RDX *)
| 0x1bab92 => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RAX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RAX (Var (V_TEMP 0x34580))
	)
)

(* 0x001bab96: RET *)
(*    1813398: RET *)
| 0x1bab96 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001baba0: AND RAX,-0x40 *)
(*    1813408: AND RAX,-0x40 *)
| 0x1baba0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baba4: PCMPEQB XMM0,xmmword ptr [RAX] *)
(*    1813412: PCMPEQB XMM0,xmmword ptr [RAX] *)
| 0x1baba4 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001baba8: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
(*    1813416: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
| 0x1baba8 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
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

(* 0x001babad: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
(*    1813421: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
| 0x1babad => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001babb2: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
(*    1813426: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
| 0x1babb2 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001babb7: PMOVMSKB ESI,XMM0 *)
(*    1813431: PMOVMSKB ESI,XMM0 *)
| 0x1babb7 => Some (4,
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
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001babbb: PMOVMSKB EDX,XMM1 *)
(*    1813435: PMOVMSKB EDX,XMM1 *)
| 0x1babbb => Some (4,
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
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001babbf: PMOVMSKB R8D,XMM2 *)
(*    1813439: PMOVMSKB R8D,XMM2 *)
| 0x1babbf => Some (5,
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
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x001babc4: PMOVMSKB ECX,XMM3 *)
(*    1813444: PMOVMSKB ECX,XMM3 *)
| 0x1babc4 => Some (4,
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
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001babc8: SHL RDX,0x10 *)
(*    1813448: SHL RDX,0x10 *)
| 0x1babc8 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001babcc: SHL RCX,0x10 *)
(*    1813452: SHL RCX,0x10 *)
| 0x1babcc => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001babd0: OR RDX,RSI *)
(*    1813456: OR RDX,RSI *)
| 0x1babd0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001babd3: OR RCX,R8 *)
(*    1813459: OR RCX,R8 *)
| 0x1babd3 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (Var R_RCX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001babd6: SHL RCX,0x20 *)
(*    1813462: SHL RCX,0x20 *)
| 0x1babd6 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001babda: OR RDX,RCX *)
(*    1813466: OR RDX,RCX *)
| 0x1babda => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001babdd: MOV RCX,RDI *)
(*    1813469: MOV RCX,RDI *)
| 0x1babdd => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x001babe0: XOR RCX,RAX *)
(*    1813472: XOR RCX,RAX *)
| 0x1babe0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_XOR (Var R_RCX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001babe3: MOV RSI,R11 *)
(*    1813475: MOV RSI,R11 *)
| 0x1babe3 => Some (3,
	Move R_RSI (Var R_R11)
)

(* 0x001babe6: SUB RSI,RAX *)
(*    1813478: SUB RSI,RAX *)
| 0x1babe6 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001babe9: AND RAX,-0x40 *)
(*    1813481: AND RAX,-0x40 *)
| 0x1babe9 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001babed: TEST RSI,-0x40 *)
(*    1813485: TEST RSI,-0x40 *)
| 0x1babed => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70180) (BinOp OP_AND (Var R_RSI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70180)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70180)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70180)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001babf4: JZ 0x001bac03 *)
(*    1813492: JZ 0x001bac03 *)
| 0x1babf4 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1bac03 64)
	) (* else *) (
		Nop
	)
)

(* 0x001babf6: SAR RDX,CL *)
(*    1813494: SAR RDX,CL *)
| 0x1babf6 => Some (3,
	Move (V_TEMP 0x68900) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x3f 8)) $;
	Move (V_TEMP 0x68980) (Var R_RDX) $;
	Move R_RDX (BinOp OP_ARSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x68900)))) $;
	Move (V_TEMP 0x2f000) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_MINUS (Var (V_TEMP 0x68900)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2f100) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68980)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f080)))) $;
	Move (V_TEMP 0x2f180) (BinOp OP_AND (Var (V_TEMP 0x2f100)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f180)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2f300) (BinOp OP_XOR (Var (V_TEMP 0x2f000)) (Word 1 8)) $;
	Move (V_TEMP 0x2f380) (BinOp OP_AND (Var (V_TEMP 0x2f300)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2f400) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Var (V_TEMP 0x2f280))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2f380)) (Var (V_TEMP 0x2f400)))) $;
	Move (V_TEMP 0x2f580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x68900)) (Word 0x1 8))) $;
	Move (V_TEMP 0x2f600) (BinOp OP_XOR (Var (V_TEMP 0x2f580)) (Word 1 8)) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_AND (Var (V_TEMP 0x2f600)) (Cast CAST_UNSIGNED 8 (Var R_OF)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001babf9: TEST RDX,RDX *)
(*    1813497: TEST RDX,RDX *)
| 0x1babf9 => Some (3,
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

(* 0x001babfc: JZ 0x001bac20 *)
(*    1813500: JZ 0x001bac20 *)
| 0x1babfc => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1bac20 64)
	) (* else *) (
		Nop
	)
)

(* 0x001babfe: BSF RAX,RDX *)
(*    1813502: BSF RAX,RDX *)
| 0x1babfe => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RAX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RAX (Var (V_TEMP 0x34580))
	)
)

(* 0x001bac02: RET *)
(*    1813506: RET *)
| 0x1bac02 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001bac03: BTS RDX,RSI *)
(*    1813507: BTS RDX,RSI *)
| 0x1bac03 => Some (4,
	Move (V_TEMP 0x3b880) (BinOp OP_AND (Var R_RSI) (Word 0x3f 64)) $;
	Move (V_TEMP 0x3b900) (BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x3b880))) $;
	Move (V_TEMP 0x3ba00) (BinOp OP_AND (Var (V_TEMP 0x3b900)) (Word 0x1 64)) $;
	Move (V_TEMP 0x3ba80) (BinOp OP_LSHIFT (Word 0x1 64) (Var (V_TEMP 0x3b880))) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var (V_TEMP 0x3ba80))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x3ba00)) (Word 0x0 64))))
)

(* 0x001bac07: SAR RDX,CL *)
(*    1813511: SAR RDX,CL *)
| 0x1bac07 => Some (3,
	Move (V_TEMP 0x68900) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0x3f 8)) $;
	Move (V_TEMP 0x68980) (Var R_RDX) $;
	Move R_RDX (BinOp OP_ARSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x68900)))) $;
	Move (V_TEMP 0x2f000) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2f080) (BinOp OP_MINUS (Var (V_TEMP 0x68900)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2f100) (BinOp OP_ARSHIFT (Var (V_TEMP 0x68980)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2f080)))) $;
	Move (V_TEMP 0x2f180) (BinOp OP_AND (Var (V_TEMP 0x2f100)) (Word 0x1 64)) $;
	Move (V_TEMP 0x2f280) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2f180)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2f300) (BinOp OP_XOR (Var (V_TEMP 0x2f000)) (Word 1 8)) $;
	Move (V_TEMP 0x2f380) (BinOp OP_AND (Var (V_TEMP 0x2f300)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2f400) (BinOp OP_AND (Var (V_TEMP 0x2f000)) (Var (V_TEMP 0x2f280))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2f380)) (Var (V_TEMP 0x2f400)))) $;
	Move (V_TEMP 0x2f580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x68900)) (Word 0x1 8))) $;
	Move (V_TEMP 0x2f600) (BinOp OP_XOR (Var (V_TEMP 0x2f580)) (Word 1 8)) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_AND (Var (V_TEMP 0x2f600)) (Cast CAST_UNSIGNED 8 (Var R_OF)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x68900)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bac0a: TEST RDX,RDX *)
(*    1813514: TEST RDX,RDX *)
| 0x1bac0a => Some (3,
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

(* 0x001bac0d: JZ 0x001bac20 *)
(*    1813517: JZ 0x001bac20 *)
| 0x1bac0d => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1bac20 64)
	) (* else *) (
		Nop
	)
)

(* 0x001bac0f: BSF RAX,RDX *)
(*    1813519: BSF RAX,RDX *)
| 0x1bac0f => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RAX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RAX (Var (V_TEMP 0x34580))
	)
)

(* 0x001bac13: RET *)
(*    1813523: RET *)
| 0x1bac13 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001bac20: PXOR XMM1,XMM1 *)
(*    1813536: PXOR XMM1,XMM1 *)
| 0x1bac20 => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM1)) (Extract 127 0 (Var R_YMM1))))
)

(* 0x001bac24: PXOR XMM2,XMM2 *)
(*    1813540: PXOR XMM2,XMM2 *)
| 0x1bac24 => Some (4,
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM2)) (Extract 127 0 (Var R_YMM2))))
)

(* 0x001bac28: PXOR XMM3,XMM3 *)
(*    1813544: PXOR XMM3,XMM3 *)
| 0x1bac28 => Some (4,
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM3)) (Extract 127 0 (Var R_YMM3))))
)

(* 0x001bac2c: NOP dword ptr [RAX] *)
(*    1813548: NOP dword ptr [RAX] *)
| 0x1bac2c => Some (4,
	Nop
)

(* 0x001bac30: ADD RAX,0x40 *)
(*    1813552: ADD RAX,0x40 *)
| 0x1bac30 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bac34: CMP R10,RAX *)
(*    1813556: CMP R10,RAX *)
| 0x1bac34 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_R10) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bac37: JZ 0x001bac60 *)
(*    1813559: JZ 0x001bac60 *)
| 0x1bac37 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1bac60 64)
	) (* else *) (
		Nop
	)
)

(* 0x001bac39: MOVDQA XMM0,xmmword ptr [RAX] *)
(*    1813561: MOVDQA XMM0,xmmword ptr [RAX] *)
| 0x1bac39 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Var (V_TEMP 0x6c80)))
)

(* 0x001bac3d: PMINUB XMM0,xmmword ptr [RAX + 0x10] *)
(*    1813565: PMINUB XMM0,xmmword ptr [RAX + 0x10] *)
| 0x1bac3d => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001bac42: PMINUB XMM0,xmmword ptr [RAX + 0x20] *)
(*    1813570: PMINUB XMM0,xmmword ptr [RAX + 0x20] *)
| 0x1bac42 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001bac47: PMINUB XMM0,xmmword ptr [RAX + 0x30] *)
(*    1813575: PMINUB XMM0,xmmword ptr [RAX + 0x30] *)
| 0x1bac47 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xb8000) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xb8080) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8100) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8080)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8180) (Extract 7 0 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8100)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8180))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8100)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 7 0 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200)))) $;
	Move (V_TEMP 0xb8200) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8280) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8200)) (Extract 15 8 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8300) (Extract 15 8 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8280)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8300))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8280)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 15 8 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8380) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8400) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8380)) (Extract 23 16 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8480) (Extract 23 16 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8400)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8480))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8400)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 23 16 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8500) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8580) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8500)) (Extract 31 24 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8600) (Extract 31 24 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8580)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8600))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8580)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 31 24 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8680) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8700) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8680)) (Extract 39 32 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8780) (Extract 39 32 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8700)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8780))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8700)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 39 32 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8800) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8880) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8800)) (Extract 47 40 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8900) (Extract 47 40 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8880)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8900))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8880)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 47 40 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8980) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8a00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8980)) (Extract 55 48 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8a80) (Extract 55 48 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8a00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8a80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8a00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 55 48 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8b00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8b80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8b00)) (Extract 63 56 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c00) (Extract 63 56 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8b80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8c00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8b80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 63 56 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8c80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8d00) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8c80)) (Extract 71 64 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8d80) (Extract 71 64 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8d00)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8d80))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8d00)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 71 64 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8e00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb8e80) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8e00)) (Extract 79 72 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f00) (Extract 79 72 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb8e80)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb8f00))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb8e80)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 79 72 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb8f80) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9000) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb8f80)) (Extract 87 80 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9080) (Extract 87 80 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9000)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9080))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9000)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 87 80 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9100) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9180) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9100)) (Extract 95 88 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9200) (Extract 95 88 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9180)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9200))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9180)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 95 88 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9280) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9300) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9280)) (Extract 103 96 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9380) (Extract 103 96 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9300)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9380))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9300)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 103 96 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9400) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9400)) (Extract 111 104 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9500) (Extract 111 104 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9480)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9500))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9480)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 111 104 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9580) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9600) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9580)) (Extract 119 112 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9680) (Extract 119 112 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9600)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9680))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9600)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 119 112 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9700) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0xb9780) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0xb9700)) (Extract 127 120 (Var R_YMM0)))) $;
	Move (V_TEMP 0xb9800) (Extract 127 120 (Var (V_TEMP 0xb8000))) $;
	Move (V_TEMP 0x0) (Var (V_TEMP 0xb9780)) $;
	Move (V_TEMP 0x80) (BinOp OP_TIMES (Var (V_TEMP 0x0)) (Var (V_TEMP 0xb9800))) $;
	Move (V_TEMP 0x100) (BinOp OP_XOR (Var (V_TEMP 0xb9780)) (Word 1 8)) $;
	Move (V_TEMP 0x180) (Var (V_TEMP 0x100)) $;
	Move (V_TEMP 0x200) (BinOp OP_TIMES (Var (V_TEMP 0x180)) (Extract 127 120 (Var R_YMM0))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_OR (Var (V_TEMP 0x80)) (Var (V_TEMP 0x200))) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001bac4c: PCMPEQB XMM0,XMM3 *)
(*    1813580: PCMPEQB XMM0,XMM3 *)
| 0x1bac4c => Some (4,
	Move (V_TEMP 0xa2c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Extract 7 0 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa2c80)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa2d80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Extract 15 8 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2d80)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2e80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Extract 23 16 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2e80)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Extract 31 24 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2f80)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3080) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Extract 39 32 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3080)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Extract 47 40 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3180)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Extract 55 48 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3280)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3380) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Extract 63 56 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3380)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3480) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Extract 71 64 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3480)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Extract 79 72 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3580)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Extract 87 80 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3680)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3780) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Extract 95 88 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3780)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Extract 103 96 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3880)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Extract 111 104 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3980)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3a80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Extract 119 112 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3a80)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa3b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Extract 127 120 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa3b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001bac50: PMOVMSKB EDX,XMM0 *)
(*    1813584: PMOVMSKB EDX,XMM0 *)
| 0x1bac50 => Some (4,
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
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001bac54: TEST EDX,EDX *)
(*    1813588: TEST EDX,EDX *)
| 0x1bac54 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bac56: JNZ 0x001bacc0 *)
(*    1813590: JNZ 0x001bacc0 *)
| 0x1bac56 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1bacc0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001bac58: JMP 0x001bac30 *)
(*    1813592: JMP 0x001bac30 *)
| 0x1bac58 => Some (2,
	Jmp (Word 0x1bac30 64)
)

(* 0x001bac60: CMP R11,RAX *)
(*    1813600: CMP R11,RAX *)
| 0x1bac60 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_R11) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bac63: JZ 0x001baca2 *)
(*    1813603: JZ 0x001baca2 *)
| 0x1bac63 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1baca2 64)
	) (* else *) (
		Nop
	)
)

(* 0x001bac65: PXOR XMM0,XMM0 *)
(*    1813605: PXOR XMM0,XMM0 *)
| 0x1bac65 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM0)) (Extract 127 0 (Var R_YMM0))))
)

(* 0x001bac69: PCMPEQB XMM0,xmmword ptr [RAX] *)
(*    1813609: PCMPEQB XMM0,xmmword ptr [RAX] *)
| 0x1bac69 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001bac6d: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
(*    1813613: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
| 0x1bac6d => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
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

(* 0x001bac72: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
(*    1813618: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
| 0x1bac72 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001bac77: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
(*    1813623: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
| 0x1bac77 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001bac7c: PMOVMSKB ESI,XMM0 *)
(*    1813628: PMOVMSKB ESI,XMM0 *)
| 0x1bac7c => Some (4,
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
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001bac80: PMOVMSKB EDX,XMM1 *)
(*    1813632: PMOVMSKB EDX,XMM1 *)
| 0x1bac80 => Some (4,
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
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001bac84: PMOVMSKB R8D,XMM2 *)
(*    1813636: PMOVMSKB R8D,XMM2 *)
| 0x1bac84 => Some (5,
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
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x001bac89: PMOVMSKB ECX,XMM3 *)
(*    1813641: PMOVMSKB ECX,XMM3 *)
| 0x1bac89 => Some (4,
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
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001bac8d: SHL RDX,0x10 *)
(*    1813645: SHL RDX,0x10 *)
| 0x1bac8d => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bac91: SHL RCX,0x10 *)
(*    1813649: SHL RCX,0x10 *)
| 0x1bac91 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bac95: OR RDX,RSI *)
(*    1813653: OR RDX,RSI *)
| 0x1bac95 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bac98: OR RCX,R8 *)
(*    1813656: OR RCX,R8 *)
| 0x1bac98 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (Var R_RCX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bac9b: SHL RCX,0x20 *)
(*    1813659: SHL RCX,0x20 *)
| 0x1bac9b => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bac9f: OR RDX,RCX *)
(*    1813663: OR RDX,RCX *)
| 0x1bac9f => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001baca2: BTS RDX,R11 *)
(*    1813666: BTS RDX,R11 *)
| 0x1baca2 => Some (4,
	Move (V_TEMP 0x3b880) (BinOp OP_AND (Var R_R11) (Word 0x3f 64)) $;
	Move (V_TEMP 0x3b900) (BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x3b880))) $;
	Move (V_TEMP 0x3ba00) (BinOp OP_AND (Var (V_TEMP 0x3b900)) (Word 0x1 64)) $;
	Move (V_TEMP 0x3ba80) (BinOp OP_LSHIFT (Word 0x1 64) (Var (V_TEMP 0x3b880))) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var (V_TEMP 0x3ba80))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x3ba00)) (Word 0x0 64))))
)

(* 0x001baca6: BSF RDX,RDX *)
(*    1813670: BSF RDX,RDX *)
| 0x1baca6 => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RDX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RDX (Var (V_TEMP 0x34580))
	)
)

(* 0x001bacaa: ADD RAX,RDX *)
(*    1813674: ADD RAX,RDX *)
| 0x1bacaa => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bacad: SUB RAX,RDI *)
(*    1813677: SUB RAX,RDI *)
| 0x1bacad => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RAX) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bacb0: RET *)
(*    1813680: RET *)
| 0x1bacb0 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001bacc0: PXOR XMM0,XMM0 *)
(*    1813696: PXOR XMM0,XMM0 *)
| 0x1bacc0 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (BinOp OP_XOR (Extract 127 0 (Var R_YMM0)) (Extract 127 0 (Var R_YMM0))))
)

(* 0x001bacc4: PCMPEQB XMM0,xmmword ptr [RAX] *)
(*    1813700: PCMPEQB XMM0,xmmword ptr [RAX] *)
| 0x1bacc4 => Some (4,
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var R_RAX) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM0)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM0 (Concat (Extract 255 8 (Var R_YMM0)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM0)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM0 (Concat (Extract 255 16 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM0)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM0 (Concat (Extract 255 24 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM0)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM0)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM0 (Concat (Extract 255 40 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM0)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM0 (Concat (Extract 255 48 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM0)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM0 (Concat (Extract 255 56 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM0)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM0)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM0 (Concat (Extract 255 72 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM0)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM0 (Concat (Extract 255 80 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM0)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM0 (Concat (Extract 255 88 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM0)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM0)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM0 (Concat (Extract 255 104 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM0)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM0 (Concat (Extract 255 112 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM0)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM0 (Concat (Extract 255 120 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM0)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM0)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM0))))
)

(* 0x001bacc8: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
(*    1813704: PCMPEQB XMM1,xmmword ptr [RAX + 0x10] *)
| 0x1bacc8 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x10 64)) $;
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

(* 0x001baccd: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
(*    1813709: PCMPEQB XMM2,xmmword ptr [RAX + 0x20] *)
| 0x1baccd => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM2)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM2 (Concat (Extract 255 8 (Var R_YMM2)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM2)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM2 (Concat (Extract 255 16 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM2)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM2 (Concat (Extract 255 24 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM2)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM2 (Concat (Extract 255 32 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM2)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM2 (Concat (Extract 255 40 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM2)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM2 (Concat (Extract 255 48 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM2)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM2 (Concat (Extract 255 56 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM2)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM2 (Concat (Extract 255 64 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM2)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM2 (Concat (Extract 255 72 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM2)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM2 (Concat (Extract 255 80 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM2)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM2 (Concat (Extract 255 88 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM2)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM2 (Concat (Extract 255 96 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM2)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM2 (Concat (Extract 255 104 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM2)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM2 (Concat (Extract 255 112 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM2)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM2 (Concat (Extract 255 120 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM2)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM2)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM2 (Concat (Extract 255 128 (Var R_YMM2)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM2))))
)

(* 0x001bacd2: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
(*    1813714: PCMPEQB XMM3,xmmword ptr [RAX + 0x30] *)
| 0x1bacd2 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x30 64)) $;
	Move (V_TEMP 0x6c80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 16) $;
	Move (V_TEMP 0xa1400) (Var (V_TEMP 0x6c80)) $;
	Move (V_TEMP 0xa1480) (Extract 7 0 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_YMM3)) (Var (V_TEMP 0xa1480)))) $;
	Move R_YMM3 (Concat (Extract 255 8 (Var R_YMM3)) (BinOp OP_TIMES (Var (V_TEMP 0xa1500)) (Word 0xff 8))) $;
	Move (V_TEMP 0xa1600) (Extract 15 8 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 8 (Var R_YMM3)) (Var (V_TEMP 0xa1600)))) $;
	Move R_YMM3 (Concat (Extract 255 16 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1680)) (Word 0xff 8)) (Extract 7 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1780) (Extract 23 16 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1800) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 23 16 (Var R_YMM3)) (Var (V_TEMP 0xa1780)))) $;
	Move R_YMM3 (Concat (Extract 255 24 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1800)) (Word 0xff 8)) (Extract 15 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1900) (Extract 31 24 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1980) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 24 (Var R_YMM3)) (Var (V_TEMP 0xa1900)))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1980)) (Word 0xff 8)) (Extract 23 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1a80) (Extract 39 32 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1b00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 39 32 (Var R_YMM3)) (Var (V_TEMP 0xa1a80)))) $;
	Move R_YMM3 (Concat (Extract 255 40 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1b00)) (Word 0xff 8)) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1c00) (Extract 47 40 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1c80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 47 40 (Var R_YMM3)) (Var (V_TEMP 0xa1c00)))) $;
	Move R_YMM3 (Concat (Extract 255 48 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1c80)) (Word 0xff 8)) (Extract 39 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1d80) (Extract 55 48 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1e00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 55 48 (Var R_YMM3)) (Var (V_TEMP 0xa1d80)))) $;
	Move R_YMM3 (Concat (Extract 255 56 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1e00)) (Word 0xff 8)) (Extract 47 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa1f00) (Extract 63 56 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa1f80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 63 56 (Var R_YMM3)) (Var (V_TEMP 0xa1f00)))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa1f80)) (Word 0xff 8)) (Extract 55 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2080) (Extract 71 64 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2100) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 71 64 (Var R_YMM3)) (Var (V_TEMP 0xa2080)))) $;
	Move R_YMM3 (Concat (Extract 255 72 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2100)) (Word 0xff 8)) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2200) (Extract 79 72 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2280) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 79 72 (Var R_YMM3)) (Var (V_TEMP 0xa2200)))) $;
	Move R_YMM3 (Concat (Extract 255 80 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2280)) (Word 0xff 8)) (Extract 71 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2380) (Extract 87 80 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2400) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 87 80 (Var R_YMM3)) (Var (V_TEMP 0xa2380)))) $;
	Move R_YMM3 (Concat (Extract 255 88 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2400)) (Word 0xff 8)) (Extract 79 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2500) (Extract 95 88 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2580) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 95 88 (Var R_YMM3)) (Var (V_TEMP 0xa2500)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2580)) (Word 0xff 8)) (Extract 87 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2680) (Extract 103 96 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2700) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 103 96 (Var R_YMM3)) (Var (V_TEMP 0xa2680)))) $;
	Move R_YMM3 (Concat (Extract 255 104 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2700)) (Word 0xff 8)) (Extract 95 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2800) (Extract 111 104 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 111 104 (Var R_YMM3)) (Var (V_TEMP 0xa2800)))) $;
	Move R_YMM3 (Concat (Extract 255 112 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2880)) (Word 0xff 8)) (Extract 103 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2980) (Extract 119 112 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2a00) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 119 112 (Var R_YMM3)) (Var (V_TEMP 0xa2980)))) $;
	Move R_YMM3 (Concat (Extract 255 120 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2a00)) (Word 0xff 8)) (Extract 111 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0xa2b00) (Extract 127 120 (Var (V_TEMP 0xa1400))) $;
	Move (V_TEMP 0xa2b80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 127 120 (Var R_YMM3)) (Var (V_TEMP 0xa2b00)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_TIMES (Var (V_TEMP 0xa2b80)) (Word 0xff 8)) (Extract 119 0 (Var R_YMM3))))
)

(* 0x001bacd7: PMOVMSKB ESI,XMM0 *)
(*    1813719: PMOVMSKB ESI,XMM0 *)
| 0x1bacd7 => Some (4,
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
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001bacdb: PMOVMSKB EDX,XMM1 *)
(*    1813723: PMOVMSKB EDX,XMM1 *)
| 0x1bacdb => Some (4,
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
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x001bacdf: PMOVMSKB R8D,XMM2 *)
(*    1813727: PMOVMSKB R8D,XMM2 *)
| 0x1bacdf => Some (5,
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
	Move R_R8 (Concat (Extract 63 32 (Var R_R8)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_R8 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R8)))
)

(* 0x001bace4: PMOVMSKB ECX,XMM3 *)
(*    1813732: PMOVMSKB ECX,XMM3 *)
| 0x1bace4 => Some (4,
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
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbad00)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x001bace8: SHL RDX,0x10 *)
(*    1813736: SHL RDX,0x10 *)
| 0x1bace8 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RDX) $;
	Move R_RDX (BinOp OP_LSHIFT (Var R_RDX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bacec: SHL RCX,0x10 *)
(*    1813740: SHL RCX,0x10 *)
| 0x1bacec => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x10 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bacf0: OR RDX,RSI *)
(*    1813744: OR RDX,RSI *)
| 0x1bacf0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bacf3: OR RCX,R8 *)
(*    1813747: OR RCX,R8 *)
| 0x1bacf3 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_OR (Var R_RCX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bacf6: SHL RCX,0x20 *)
(*    1813750: SHL RCX,0x20 *)
| 0x1bacf6 => Some (4,
	Move (V_TEMP 0x6a880) (BinOp OP_AND (Word 0x20 32) (Word 0x3f 32)) $;
	Move (V_TEMP 0x6a900) (Var R_RCX) $;
	Move R_RCX (BinOp OP_LSHIFT (Var R_RCX) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x6a880)))) $;
	Move (V_TEMP 0x2e680) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2e700) (BinOp OP_MINUS (Var (V_TEMP 0x6a880)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2e780) (BinOp OP_LSHIFT (Var (V_TEMP 0x6a900)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2e700)))) $;
	Move (V_TEMP 0x2e880) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x2e780)) (Word 0x0 64))) $;
	Move (V_TEMP 0x2e900) (BinOp OP_XOR (Var (V_TEMP 0x2e680)) (Word 1 8)) $;
	Move (V_TEMP 0x2e980) (BinOp OP_AND (Var (V_TEMP 0x2e900)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2ea00) (BinOp OP_AND (Var (V_TEMP 0x2e680)) (Var (V_TEMP 0x2e880))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2e980)) (Var (V_TEMP 0x2ea00)))) $;
	Move (V_TEMP 0x2eb80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6a880)) (Word 0x1 32))) $;
	Move (V_TEMP 0x2ec00) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2ed00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2ec00))) $;
	Move (V_TEMP 0x2ed80) (BinOp OP_XOR (Var (V_TEMP 0x2eb80)) (Word 1 8)) $;
	Move (V_TEMP 0x2ee00) (BinOp OP_AND (Var (V_TEMP 0x2ed80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2ee80) (BinOp OP_AND (Var (V_TEMP 0x2eb80)) (Var (V_TEMP 0x2ed00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ee00)) (Var (V_TEMP 0x2ee80)))) $;
	Move (V_TEMP 0x2c500) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6a880)) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c600) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c680) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2c700) (BinOp OP_AND (Var (V_TEMP 0x2c680)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2c700)) (Var (V_TEMP 0x2c780)))) $;
	Move (V_TEMP 0x2c900) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	Move (V_TEMP 0x2c980) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ca00) (BinOp OP_AND (Var (V_TEMP 0x2c980)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x2ca80) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2c900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ca00)) (Var (V_TEMP 0x2ca80)))) $;
	Move (V_TEMP 0x2cb80) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2cc00) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2cb80)))) $;
	Move (V_TEMP 0x2cc80) (BinOp OP_AND (Var (V_TEMP 0x2cc00)) (Word 0x1 8)) $;
	Move (V_TEMP 0x2cd80) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2cc80)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2ce00) (BinOp OP_XOR (Var (V_TEMP 0x2c500)) (Word 1 8)) $;
	Move (V_TEMP 0x2ce80) (BinOp OP_AND (Var (V_TEMP 0x2ce00)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 0x2cf00) (BinOp OP_AND (Var (V_TEMP 0x2c500)) (Var (V_TEMP 0x2cd80))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2ce80)) (Var (V_TEMP 0x2cf00))))
)

(* 0x001bacfa: OR RDX,RCX *)
(*    1813754: OR RDX,RCX *)
| 0x1bacfa => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_OR (Var R_RDX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bacfd: BSF RDX,RDX *)
(*    1813757: BSF RDX,RDX *)
| 0x1bacfd => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RDX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDX) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RDX (Var (V_TEMP 0x34580))
	)
)

(* 0x001bad01: ADD RAX,RDX *)
(*    1813761: ADD RAX,RDX *)
| 0x1bad01 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bad04: SUB RAX,RDI *)
(*    1813764: SUB RAX,RDI *)
| 0x1bad04 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RAX) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001bad07: RET *)
(*    1813767: RET *)
| 0x1bad07 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx strnlen_sse2_amd64.
Proof. Picinae_typecheck. Qed.

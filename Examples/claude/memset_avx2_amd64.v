(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: FUN_002a1000
entry: 0x2a1000 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition memset_avx2_amd64 : program := fun _ a => match a with

(* 0x002a1000: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x002a1004: VMOVD XMM0,ESI *)
(*          4: VMOVD XMM0,ESI *)
| 0x4 => Some (4,
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Extract 31 0 (Var R_RSI))))
)

(* 0x002a1008: MOV RAX,RDI *)
(*          8: MOV RAX,RDI *)
| 0x8 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x002a100b: VPBROADCASTB YMM0,XMM0 *)
(*         11: VPBROADCASTB YMM0,XMM0 *)
| 0xb => Some (5,
	Move (V_TEMP 0x11e380) (Extract 7 0 (Var R_YMM0)) $;
	Move R_YMM0 (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Concat (Var (V_TEMP 0x11e380)) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) (Var (V_TEMP 0x11e380))) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var R_YMM0)))
)

(* 0x002a1010: CMP RDX,0x20 *)
(*         16: CMP RDX,0x20 *)
| 0x10 => Some (4,
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

(* 0x002a1014: JC 0x002a10e0 *)
(*         20: JC 0x002a10e0 *)
| 0x14 => Some (6,
	If (Var R_CF) (
		Jmp (Word 0xe0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a101a: CMP RDX,0x40 *)
(*         26: CMP RDX,0x40 *)
| 0x1a => Some (4,
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

(* 0x002a101e: JA 0x002a1040 *)
(*         30: JA 0x002a1040 *)
| 0x1e => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x40 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a1020: VMOVDQU ymmword ptr [RAX],YMM0 *)
(*         32: VMOVDQU ymmword ptr [RAX],YMM0 *)
| 0x20 => Some (4,
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a1024: VMOVDQU ymmword ptr [RAX + RDX*0x1 + -0x20],YMM0 *)
(*         36: VMOVDQU ymmword ptr [RAX + RDX*0x1 + -0x20],YMM0 *)
| 0x24 => Some (6,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a102a: VZEROUPPER *)
(*         42: VZEROUPPER *)
| 0x2a => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a102d: RET *)
(*         45: RET *)
| 0x2d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a1030: VMOVDQU ymmword ptr [RDI + -0x40],YMM0 *)
(*         48: VMOVDQU ymmword ptr [RDI + -0x40],YMM0 *)
| 0x30 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffffc0 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a1035: VMOVDQU ymmword ptr [RDI + -0x20],YMM0 *)
(*         53: VMOVDQU ymmword ptr [RDI + -0x20],YMM0 *)
| 0x35 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffffe0 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a103a: VZEROUPPER *)
(*         58: VZEROUPPER *)
| 0x3a => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a103d: RET *)
(*         61: RET *)
| 0x3d => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a1040: CMP RDX,qword ptr [0x0031a3f0] *)
(*         64: CMP RDX,qword ptr [0x0031a3f0] *)
| 0x40 => Some (7,
	Move (V_TEMP 0x3f880) (Load (Var V_MEM64) (Word 0x31a3f0 64) LittleE 8) $;
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

(* 0x002a1047: JA 0x002a10c0 *)
(*         71: JA 0x002a10c0 *)
| 0x47 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0xc0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a1049: VMOVDQU ymmword ptr [RAX],YMM0 *)
(*         73: VMOVDQU ymmword ptr [RAX],YMM0 *)
| 0x49 => Some (4,
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a104d: VMOVDQU ymmword ptr [RAX + 0x20],YMM0 *)
(*         77: VMOVDQU ymmword ptr [RAX + 0x20],YMM0 *)
| 0x4d => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a1052: ADD RDI,RDX *)
(*         82: ADD RDI,RDX *)
| 0x52 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Var R_RDX)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002a1055: CMP RDX,0x80 *)
(*         85: CMP RDX,0x80 *)
| 0x55 => Some (7,
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

(* 0x002a105c: JBE 0x002a1030 *)
(*         92: JBE 0x002a1030 *)
| 0x5c => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x30 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a105e: VMOVDQU ymmword ptr [RAX + 0x40],YMM0 *)
(*         94: VMOVDQU ymmword ptr [RAX + 0x40],YMM0 *)
| 0x5e => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x40 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a1063: VMOVDQU ymmword ptr [RAX + 0x60],YMM0 *)
(*         99: VMOVDQU ymmword ptr [RAX + 0x60],YMM0 *)
| 0x63 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x60 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a1068: ADD RDI,-0x80 *)
(*        104: ADD RDI,-0x80 *)
| 0x68 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002a106c: CMP RDX,0x100 *)
(*        108: CMP RDX,0x100 *)
| 0x6c => Some (7,
	Move (V_TEMP 0x3e680) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e680)) (Word 0x100 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e680)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0x100 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0x100 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x100 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3e780) (BinOp OP_MINUS (Var (V_TEMP 0x3e680)) (Word 0x100 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e780)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e780)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e780)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002a1073: JBE 0x002a10a0 *)
(*        115: JBE 0x002a10a0 *)
| 0x73 => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0xa0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a1075: LEA RDX,[RAX + 0x80] *)
(*        117: LEA RDX,[RAX + 0x80] *)
| 0x75 => Some (7,
	Move (V_TEMP 0x4880) (BinOp OP_PLUS (Var R_RAX) (Word 0x80 64)) $;
	Move R_RDX (Var (V_TEMP 0x4880))
)

(* 0x002a107c: AND RDX,-0x40 *)
(*        124: AND RDX,-0x40 *)
| 0x7c => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (BinOp OP_AND (Var R_RDX) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002a1080: VMOVDQA ymmword ptr [RDX],YMM0 *)
(*        128: VMOVDQA ymmword ptr [RDX],YMM0 *)
| 0x80 => Some (4,
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDX) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a1084: VMOVDQA ymmword ptr [RDX + 0x20],YMM0 *)
(*        132: VMOVDQA ymmword ptr [RDX + 0x20],YMM0 *)
| 0x84 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a1089: VMOVDQA ymmword ptr [RDX + 0x40],YMM0 *)
(*        137: VMOVDQA ymmword ptr [RDX + 0x40],YMM0 *)
| 0x89 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x40 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a108e: VMOVDQA ymmword ptr [RDX + 0x60],YMM0 *)
(*        142: VMOVDQA ymmword ptr [RDX + 0x60],YMM0 *)
| 0x8e => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x60 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a1093: SUB RDX,-0x80 *)
(*        147: SUB RDX,-0x80 *)
| 0x93 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_MINUS (Var R_RDX) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002a1097: CMP RDX,RDI *)
(*        151: CMP RDX,RDI *)
| 0x97 => Some (3,
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

(* 0x002a109a: JC 0x002a1080 *)
(*        154: JC 0x002a1080 *)
| 0x9a => Some (2,
	If (Var R_CF) (
		Jmp (Word 0x80 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a109c: NOP dword ptr [RAX] *)
(*        156: NOP dword ptr [RAX] *)
| 0x9c => Some (4,
	Nop
)

(* 0x002a10a0: VMOVDQU ymmword ptr [RDI],YMM0 *)
(*        160: VMOVDQU ymmword ptr [RDI],YMM0 *)
| 0xa0 => Some (4,
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a10a4: VMOVDQU ymmword ptr [RDI + 0x20],YMM0 *)
(*        164: VMOVDQU ymmword ptr [RDI + 0x20],YMM0 *)
| 0xa4 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a10a9: VMOVDQU ymmword ptr [RDI + 0x40],YMM0 *)
(*        169: VMOVDQU ymmword ptr [RDI + 0x40],YMM0 *)
| 0xa9 => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a10ae: VMOVDQU ymmword ptr [RDI + 0x60],YMM0 *)
(*        174: VMOVDQU ymmword ptr [RDI + 0x60],YMM0 *)
| 0xae => Some (5,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 0x6d00) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6d00)) LittleE 32)
)

(* 0x002a10b3: VZEROUPPER *)
(*        179: VZEROUPPER *)
| 0xb3 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a10b6: RET *)
(*        182: RET *)
| 0xb6 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a10c0: MOVZX EAX,SIL *)
(*        192: MOVZX EAX,SIL *)
| 0xc0 => Some (4,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Cast CAST_UNSIGNED 32 (Extract 7 0 (Var R_RSI)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x002a10c4: MOV RCX,RDX *)
(*        196: MOV RCX,RDX *)
| 0xc4 => Some (3,
	Move R_RCX (Var R_RDX)
)

(* 0x002a10c7: MOV RDX,RDI *)
(*        199: MOV RDX,RDI *)
| 0xc7 => Some (3,
	Move R_RDX (Var R_RDI)
)

(* 0x002a10ca: STOSB.REP RDI *)
(*        202: STOSB.REP RDI *)
| 0xca => Some (2,
	Move (V_TEMP 0x13500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13500))) (
		Jmp (Word 0xcc 64)
	) (* else *) (
		Nop
	) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x11280) (Var R_RDI) $;
	Move (V_TEMP 0x11300) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x11380) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 0x11400) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 0x11380))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 0x11300)) (Var (V_TEMP 0x11400))) $;
	Move (V_TEMP 0x11500) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x11280)) (Var (V_TEMP 0x11500)) LittleE 1) $;
	Jmp (Word 0xca 64)
)

(* 0x002a10cc: MOV RAX,RDX *)
(*        204: MOV RAX,RDX *)
| 0xcc => Some (3,
	Move R_RAX (Var R_RDX)
)

(* 0x002a10cf: VZEROUPPER *)
(*        207: VZEROUPPER *)
| 0xcf => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a10d2: RET *)
(*        210: RET *)
| 0xd2 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a10e0: CMP EDX,0x10 *)
(*        224: CMP EDX,0x10 *)
| 0xe0 => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x10 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x10 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x10 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x10 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x002a10e3: JNC 0x002a1102 *)
(*        227: JNC 0x002a1102 *)
| 0xe3 => Some (2,
	Move (V_TEMP 0x12780) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x102 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a10e5: VMOVQ RDI,XMM0 *)
(*        229: VMOVQ RDI,XMM0 *)
| 0xe5 => Some (5,
	Move R_RDI (Extract 63 0 (Var R_YMM0))
)

(* 0x002a10ea: CMP EDX,0x8 *)
(*        234: CMP EDX,0x8 *)
| 0xea => Some (3,
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

(* 0x002a10ed: JNC 0x002a1110 *)
(*        237: JNC 0x002a1110 *)
| 0xed => Some (2,
	Move (V_TEMP 0x12780) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x110 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a10ef: CMP EDX,0x4 *)
(*        239: CMP EDX,0x4 *)
| 0xef => Some (3,
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

(* 0x002a10f2: JNC 0x002a1120 *)
(*        242: JNC 0x002a1120 *)
| 0xf2 => Some (2,
	Move (V_TEMP 0x12780) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x120 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a10f4: CMP EDX,0x1 *)
(*        244: CMP EDX,0x1 *)
| 0xf4 => Some (3,
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

(* 0x002a10f7: JA 0x002a1130 *)
(*        247: JA 0x002a1130 *)
| 0xf7 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x130 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a10f9: JC 0x002a10b3 *)
(*        249: JC 0x002a10b3 *)
| 0xf9 => Some (2,
	If (Var R_CF) (
		Jmp (Word 0xb3 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a10fb: MOV byte ptr [RAX],SIL *)
(*        251: MOV byte ptr [RAX],SIL *)
| 0xfb => Some (3,
	Move (V_TEMP 0x6a00) (Extract 7 0 (Var R_RSI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Var (V_TEMP 0x6a00)) LittleE 1)
)

(* 0x002a10fe: VZEROUPPER *)
(*        254: VZEROUPPER *)
| 0xfe => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a1101: RET *)
(*        257: RET *)
| 0x101 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a1102: VMOVDQU xmmword ptr [RAX],XMM0 *)
(*        258: VMOVDQU xmmword ptr [RAX],XMM0 *)
| 0x102 => Some (4,
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x002a1106: VMOVDQU xmmword ptr [RAX + RDX*0x1 + -0x10],XMM0 *)
(*        262: VMOVDQU xmmword ptr [RAX + RDX*0x1 + -0x10],XMM0 *)
| 0x106 => Some (6,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6c80) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6c80)) LittleE 16)
)

(* 0x002a110c: VZEROUPPER *)
(*        268: VZEROUPPER *)
| 0x10c => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a110f: RET *)
(*        271: RET *)
| 0x10f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a1110: MOV qword ptr [RAX],RDI *)
(*        272: MOV qword ptr [RAX],RDI *)
| 0x110 => Some (3,
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x002a1113: MOV qword ptr [RAX + RDX*0x1 + -0x8],RDI *)
(*        275: MOV qword ptr [RAX + RDX*0x1 + -0x8],RDI *)
| 0x113 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffff8 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x002a1118: VZEROUPPER *)
(*        280: VZEROUPPER *)
| 0x118 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a111b: RET *)
(*        283: RET *)
| 0x11b => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a1120: MOV dword ptr [RAX],EDI *)
(*        288: MOV dword ptr [RAX],EDI *)
| 0x120 => Some (2,
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RDI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x002a1122: MOV dword ptr [RAX + RDX*0x1 + -0x4],EDI *)
(*        290: MOV dword ptr [RAX + RDX*0x1 + -0x4],EDI *)
| 0x122 => Some (4,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xfffffffffffffffc 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RDI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x002a1126: VZEROUPPER *)
(*        294: VZEROUPPER *)
| 0x126 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a1129: RET *)
(*        297: RET *)
| 0x129 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a1130: MOV word ptr [RAX],DI *)
(*        304: MOV word ptr [RAX],DI *)
| 0x130 => Some (3,
	Move (V_TEMP 0x6a80) (Extract 15 0 (Var R_RDI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Var (V_TEMP 0x6a80)) LittleE 2)
)

(* 0x002a1133: MOV byte ptr [RAX + RDX*0x1 + -0x1],DIL *)
(*        307: MOV byte ptr [RAX + RDX*0x1 + -0x1],DIL *)
| 0x133 => Some (5,
	Move (V_TEMP 0x4f00) (BinOp OP_PLUS (Word 0xffffffffffffffff 64) (Var R_RAX)) $;
	Move (V_TEMP 0x4f80) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5080) (BinOp OP_PLUS (Var (V_TEMP 0x4f00)) (Var (V_TEMP 0x4f80))) $;
	Move (V_TEMP 0x6a00) (Extract 7 0 (Var R_RDI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x5080)) (Var (V_TEMP 0x6a00)) LittleE 1)
)

(* 0x002a1138: VZEROUPPER *)
(*        312: VZEROUPPER *)
| 0x138 => Some (3,
	Move R_YMM0 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM0))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM1 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM1))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM2 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM2))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM3 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM3))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM4 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM4))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM5 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM5))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM6 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM6))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM7 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM7))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM8 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM8))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM9 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM9))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM10 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM10))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM11 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM11))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM12 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM12))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM13 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM13))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM14 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM14))) $;
	Nop $;
	Nop $;
	Nop $;
	Nop $;
	Move R_YMM15 (Concat (Concat (Word 0x0 64) (Word 0x0 64)) (Extract 127 0 (Var R_YMM15)))
)

(* 0x002a113b: RET *)
(*        315: RET *)
| 0x13b => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx memset_avx2_amd64.
Proof. Picinae_typecheck. Qed.


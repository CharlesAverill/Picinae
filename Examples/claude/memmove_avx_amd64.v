(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: FUN_002a0840
entry: 0x2a0840 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition memmove_avx_amd64 : program := fun _ a => match a with

(* 0x002a0840: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x002a0844: MOV RAX,RDI *)
(*          4: MOV RAX,RDI *)
| 0x4 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x002a0847: CMP RDX,0x20 *)
(*          7: CMP RDX,0x20 *)
| 0x7 => Some (4,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x20 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x20 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x20 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x20 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a084b: JC 0x002a0870 *)
(*         11: JC 0x002a0870 *)
| 0xb => Some (2,
	If (Var R_CF) (
		Jmp (Word 0x30 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a084d: VMOVDQU YMM0,ymmword ptr [RSI] *)
(*         13: VMOVDQU YMM0,ymmword ptr [RSI] *)
| 0xd => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002a0851: CMP RDX,0x40 *)
(*         17: CMP RDX,0x40 *)
| 0x11 => Some (4,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0855: JA 0x002a0900 *)
(*         21: JA 0x002a0900 *)
| 0x15 => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0xc0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a085b: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
(*         27: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x1b => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0861: VMOVDQU ymmword ptr [RDI],YMM0 *)
(*         33: VMOVDQU ymmword ptr [RDI],YMM0 *)
| 0x21 => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0865: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM1 *)
(*         37: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM1 *)
| 0x25 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a086b: VZEROUPPER *)
(*         43: VZEROUPPER *)
| 0x2b => Some (3,
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

(* 0x002a086e: RET *)
(*         46: RET *)
| 0x2e => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0870: CMP EDX,0x10 *)
(*         48: CMP EDX,0x10 *)
| 0x30 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x10 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x10 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x10 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x10 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0873: JNC 0x002a08a2 *)
(*         51: JNC 0x002a08a2 *)
| 0x33 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x62 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0875: CMP EDX,0x8 *)
(*         53: CMP EDX,0x8 *)
| 0x35 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x8 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x8 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x8 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x8 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0878: JNC 0x002a08c0 *)
(*         56: JNC 0x002a08c0 *)
| 0x38 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x80 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a087a: CMP EDX,0x4 *)
(*         58: CMP EDX,0x4 *)
| 0x3a => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x4 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x4 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x4 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a087d: JNC 0x002a0895 *)
(*         61: JNC 0x002a0895 *)
| 0x3d => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x55 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a087f: CMP EDX,0x1 *)
(*         63: CMP EDX,0x1 *)
| 0x3f => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0882: JL 0x002a0894 *)
(*         66: JL 0x002a0894 *)
| 0x42 => Some (2,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x54 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0884: MOV CL,byte ptr [RSI] *)
(*         68: MOV CL,byte ptr [RSI] *)
| 0x44 => Some (2,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0)))
)

(* 0x002a0886: JZ 0x002a0892 *)
(*         70: JZ 0x002a0892 *)
| 0x46 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x52 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0888: MOVZX ESI,word ptr [RSI + RDX*0x1 + -0x2] *)
(*         72: MOVZX ESI,word ptr [RSI + RDX*0x1 + -0x2] *)
| 0x48 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffffe 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 2) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 3)))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x002a088d: MOV word ptr [RDI + RDX*0x1 + -0x2],SI *)
(*         77: MOV word ptr [RDI + RDX*0x1 + -0x2],SI *)
| 0x4d => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffffe 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Extract 15 0 (Var R_RSI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 2)
)

(* 0x002a0892: MOV byte ptr [RDI],CL *)
(*         82: MOV byte ptr [RDI],CL *)
| 0x52 => Some (2,
	Move (V_TEMP 0) (Extract 7 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 1)
)

(* 0x002a0894: RET *)
(*         84: RET *)
| 0x54 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0895: MOV ECX,dword ptr [RSI + RDX*0x1 + -0x4] *)
(*         85: MOV ECX,dword ptr [RSI + RDX*0x1 + -0x4] *)
| 0x55 => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffffc 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 4) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 3))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x002a0899: MOV ESI,dword ptr [RSI] *)
(*         89: MOV ESI,dword ptr [RSI] *)
| 0x59 => Some (2,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 4) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x002a089b: MOV dword ptr [RDI + RDX*0x1 + -0x4],ECX *)
(*         91: MOV dword ptr [RDI + RDX*0x1 + -0x4],ECX *)
| 0x5b => Some (4,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffffc 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Extract 31 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 4)
)

(* 0x002a089f: MOV dword ptr [RDI],ESI *)
(*         95: MOV dword ptr [RDI],ESI *)
| 0x5f => Some (2,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RSI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 4)
)

(* 0x002a08a1: RET *)
(*         97: RET *)
| 0x61 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a08a2: VMOVDQU XMM0,xmmword ptr [RSI] *)
(*         98: VMOVDQU XMM0,xmmword ptr [RSI] *)
| 0x62 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 16) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002a08a6: VMOVDQU XMM1,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
(*        102: VMOVDQU XMM1,xmmword ptr [RSI + RDX*0x1 + -0x10] *)
| 0x66 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 16) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a08ac: VMOVDQU xmmword ptr [RDI],XMM0 *)
(*        108: VMOVDQU xmmword ptr [RDI],XMM0 *)
| 0x6c => Some (4,
	Move (V_TEMP 0) (Extract 127 0 (Var R_YMM0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 16)
)

(* 0x002a08b0: VMOVDQU xmmword ptr [RDI + RDX*0x1 + -0x10],XMM1 *)
(*        112: VMOVDQU xmmword ptr [RDI + RDX*0x1 + -0x10],XMM1 *)
| 0x70 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Extract 127 0 (Var R_YMM1)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 16)
)

(* 0x002a08b6: RET *)
(*        118: RET *)
| 0x76 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a08c0: MOV RCX,qword ptr [RSI + RDX*0x1 + -0x8] *)
(*        128: MOV RCX,qword ptr [RSI + RDX*0x1 + -0x8] *)
| 0x80 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff8 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 8) $;
	Move R_RCX (Var (V_TEMP 3))
)

(* 0x002a08c5: MOV RSI,qword ptr [RSI] *)
(*        133: MOV RSI,qword ptr [RSI] *)
| 0x85 => Some (3,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	Move R_RSI (Var (V_TEMP 0))
)

(* 0x002a08c8: MOV qword ptr [RDI],RSI *)
(*        136: MOV qword ptr [RDI],RSI *)
| 0x88 => Some (3,
	Move (V_TEMP 0) (Var R_RSI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 8)
)

(* 0x002a08cb: MOV qword ptr [RDI + RDX*0x1 + -0x8],RCX *)
(*        139: MOV qword ptr [RDI + RDX*0x1 + -0x8],RCX *)
| 0x8b => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xfffffffffffffff8 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_RCX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 8)
)

(* 0x002a08d0: RET *)
(*        144: RET *)
| 0x90 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a08d1: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
(*        145: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x91 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a08d7: VMOVDQU YMM3,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
(*        151: VMOVDQU YMM3,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x97 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a08dd: VMOVDQU ymmword ptr [RDI],YMM0 *)
(*        157: VMOVDQU ymmword ptr [RDI],YMM0 *)
| 0x9d => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a08e1: VMOVDQU ymmword ptr [RDI + 0x20],YMM1 *)
(*        161: VMOVDQU ymmword ptr [RDI + 0x20],YMM1 *)
| 0xa1 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a08e6: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM2 *)
(*        166: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM2 *)
| 0xa6 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a08ec: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x40],YMM3 *)
(*        172: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x40],YMM3 *)
| 0xac => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a08f2: VZEROUPPER *)
(*        178: VZEROUPPER *)
| 0xb2 => Some (3,
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

(* 0x002a08f5: RET *)
(*        181: RET *)
| 0xb5 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0900: CMP RDX,qword ptr [0x0031a3f8] *)
(*        192: CMP RDX,qword ptr [0x0031a3f8] *)
| 0xc0 => Some (7,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Word 0x31a3f8 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var (V_TEMP 0))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0907: JA 0x002a0b00 *)
(*        199: JA 0x002a0b00 *)
| 0xc7 => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x2c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a090d: CMP RDX,0x100 *)
(*        205: CMP RDX,0x100 *)
| 0xcd => Some (7,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x100 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x100 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x100 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x100 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x100 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0914: JA 0x002a0975 *)
(*        212: JA 0x002a0975 *)
| 0xd4 => Some (2,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x135 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0916: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
(*        214: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
| 0xd6 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a091b: CMP RDX,0x80 *)
(*        219: CMP RDX,0x80 *)
| 0xdb => Some (7,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0922: JBE 0x002a08d1 *)
(*        226: JBE 0x002a08d1 *)
| 0xe2 => Some (2,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x91 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0924: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
(*        228: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
| 0xe4 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0929: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
(*        233: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
| 0xe9 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a092e: VMOVDQU YMM4,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
(*        238: VMOVDQU YMM4,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0xee => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0934: VMOVDQU YMM5,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
(*        244: VMOVDQU YMM5,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0xf4 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a093a: VMOVDQU YMM6,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
(*        250: VMOVDQU YMM6,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
| 0xfa => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffa0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0940: VMOVDQU YMM7,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
(*        256: VMOVDQU YMM7,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
| 0x100 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0946: VMOVDQU ymmword ptr [RDI],YMM0 *)
(*        262: VMOVDQU ymmword ptr [RDI],YMM0 *)
| 0x106 => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a094a: VMOVDQU ymmword ptr [RDI + 0x20],YMM1 *)
(*        266: VMOVDQU ymmword ptr [RDI + 0x20],YMM1 *)
| 0x10a => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a094f: VMOVDQU ymmword ptr [RDI + 0x40],YMM2 *)
(*        271: VMOVDQU ymmword ptr [RDI + 0x40],YMM2 *)
| 0x10f => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0954: VMOVDQU ymmword ptr [RDI + 0x60],YMM3 *)
(*        276: VMOVDQU ymmword ptr [RDI + 0x60],YMM3 *)
| 0x114 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0959: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM4 *)
(*        281: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM4 *)
| 0x119 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM4) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a095f: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x40],YMM5 *)
(*        287: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x40],YMM5 *)
| 0x11f => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM5) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0965: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x60],YMM6 *)
(*        293: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x60],YMM6 *)
| 0x125 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffa0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM6) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a096b: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x80],YMM7 *)
(*        299: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x80],YMM7 *)
| 0x12b => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM7) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0971: VZEROUPPER *)
(*        305: VZEROUPPER *)
| 0x131 => Some (3,
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

(* 0x002a0974: RET *)
(*        308: RET *)
| 0x134 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0975: MOV RCX,RDI *)
(*        309: MOV RCX,RDI *)
| 0x135 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x002a0978: SUB RCX,RSI *)
(*        312: SUB RCX,RSI *)
| 0x138 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RCX) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a097b: CMP RCX,RDX *)
(*        315: CMP RCX,RDX *)
| 0x13b => Some (3,
	Move (V_TEMP 0) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a097e: JC 0x002a0a30 *)
(*        318: JC 0x002a0a30 *)
| 0x13e => Some (6,
	If (Var R_CF) (
		Jmp (Word 0x1f0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0984: CMP RDX,qword ptr [0x003215a8] *)
(*        324: CMP RDX,qword ptr [0x003215a8] *)
| 0x144 => Some (7,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Word 0x3215a8 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var (V_TEMP 0))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a098b: JA 0x002a0b6d *)
(*        331: JA 0x002a0b6d *)
| 0x14b => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x32d 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0991: LEA R8,[RCX + RDX*0x1] *)
(*        337: LEA R8,[RCX + RDX*0x1] *)
| 0x151 => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RCX) (Var (V_TEMP 0))) $;
	Move R_R8 (Var (V_TEMP 1))
)

(* 0x002a0995: XOR R8,RCX *)
(*        341: XOR R8,RCX *)
| 0x155 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R8 (BinOp OP_XOR (Var R_R8) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R8) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R8) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0998: SHR R8,0x3f *)
(*        344: SHR R8,0x3f *)
| 0x158 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x3f 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_R8) $;
	Move R_R8 (BinOp OP_RSHIFT (Var R_R8) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0x1 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 5)) (Word 0x0 64))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 6))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 8)) (Var (V_TEMP 9)))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 11) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 10)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 10)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R8) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R8) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x002a099c: AND ECX,0xf00 *)
(*        348: AND ECX,0xf00 *)
| 0x15c => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xf00 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a09a2: ADD ECX,R8D *)
(*        354: ADD ECX,R8D *)
| 0x162 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_R8))) (Extract 31 0 (Var R_RCX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_R8))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_R8)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RCX)) (Extract 31 0 (Var R_R8)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a09a5: JZ 0x002a0a35 *)
(*        357: JZ 0x002a0a35 *)
| 0x165 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x1f5 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a09ab: VMOVDQU YMM5,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
(*        363: VMOVDQU YMM5,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x16b => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a09b1: VMOVDQU YMM6,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
(*        369: VMOVDQU YMM6,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x171 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a09b7: MOV RCX,RDI *)
(*        375: MOV RCX,RDI *)
| 0x177 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x002a09ba: OR RDI,0x1f *)
(*        378: OR RDI,0x1f *)
| 0x17a => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_OR (Var R_RDI) (Word 0x1f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a09be: VMOVDQU YMM7,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
(*        382: VMOVDQU YMM7,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
| 0x17e => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffa0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a09c4: VMOVDQU YMM8,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
(*        388: VMOVDQU YMM8,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
| 0x184 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a09ca: SUB RSI,RCX *)
(*        394: SUB RSI,RCX *)
| 0x18a => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a09cd: INC RDI *)
(*        397: INC RDI *)
| 0x18d => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a09d0: ADD RSI,RDI *)
(*        400: ADD RSI,RDI *)
| 0x190 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a09d3: LEA RDX,[RCX + RDX*0x1 + -0x80] *)
(*        403: LEA RDX,[RCX + RDX*0x1 + -0x80] *)
| 0x193 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RCX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RDX (Var (V_TEMP 2))
)

(* 0x002a09d8: NOP dword ptr [RAX + RAX*0x1] *)
(*        408: NOP dword ptr [RAX + RAX*0x1] *)
| 0x198 => Some (8,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0)))
)

(* 0x002a09e0: VMOVDQU YMM1,ymmword ptr [RSI] *)
(*        416: VMOVDQU YMM1,ymmword ptr [RSI] *)
| 0x1a0 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002a09e4: VMOVDQU YMM2,ymmword ptr [RSI + 0x20] *)
(*        420: VMOVDQU YMM2,ymmword ptr [RSI + 0x20] *)
| 0x1a4 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a09e9: VMOVDQU YMM3,ymmword ptr [RSI + 0x40] *)
(*        425: VMOVDQU YMM3,ymmword ptr [RSI + 0x40] *)
| 0x1a9 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a09ee: VMOVDQU YMM4,ymmword ptr [RSI + 0x60] *)
(*        430: VMOVDQU YMM4,ymmword ptr [RSI + 0x60] *)
| 0x1ae => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a09f3: SUB RSI,-0x80 *)
(*        435: SUB RSI,-0x80 *)
| 0x1b3 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a09f7: VMOVDQA ymmword ptr [RDI],YMM1 *)
(*        439: VMOVDQA ymmword ptr [RDI],YMM1 *)
| 0x1b7 => Some (4,
	Move (V_TEMP 0) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a09fb: VMOVDQA ymmword ptr [RDI + 0x20],YMM2 *)
(*        443: VMOVDQA ymmword ptr [RDI + 0x20],YMM2 *)
| 0x1bb => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a00: VMOVDQA ymmword ptr [RDI + 0x40],YMM3 *)
(*        448: VMOVDQA ymmword ptr [RDI + 0x40],YMM3 *)
| 0x1c0 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a05: VMOVDQA ymmword ptr [RDI + 0x60],YMM4 *)
(*        453: VMOVDQA ymmword ptr [RDI + 0x60],YMM4 *)
| 0x1c5 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM4) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a0a: SUB RDI,-0x80 *)
(*        458: SUB RDI,-0x80 *)
| 0x1ca => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0a0e: CMP RDX,RDI *)
(*        462: CMP RDX,RDI *)
| 0x1ce => Some (3,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0a11: JA 0x002a09e0 *)
(*        465: JA 0x002a09e0 *)
| 0x1d1 => Some (2,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x1a0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0a13: VMOVDQU ymmword ptr [RDX + 0x60],YMM5 *)
(*        467: VMOVDQU ymmword ptr [RDX + 0x60],YMM5 *)
| 0x1d3 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM5) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a18: VMOVDQU ymmword ptr [RDX + 0x40],YMM6 *)
(*        472: VMOVDQU ymmword ptr [RDX + 0x40],YMM6 *)
| 0x1d8 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM6) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a1d: VMOVDQU ymmword ptr [RDX + 0x20],YMM7 *)
(*        477: VMOVDQU ymmword ptr [RDX + 0x20],YMM7 *)
| 0x1dd => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDX) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM7) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a22: VMOVDQU ymmword ptr [RDX],YMM8 *)
(*        482: VMOVDQU ymmword ptr [RDX],YMM8 *)
| 0x1e2 => Some (4,
	Move (V_TEMP 0) (Var R_YMM8) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDX) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0a26: VMOVDQU ymmword ptr [RCX],YMM0 *)
(*        486: VMOVDQU ymmword ptr [RCX],YMM0 *)
| 0x1e6 => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RCX) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0a2a: VZEROUPPER *)
(*        490: VZEROUPPER *)
| 0x1ea => Some (3,
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

(* 0x002a0a2d: RET *)
(*        493: RET *)
| 0x1ed => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0a30: TEST RCX,RCX *)
(*        496: TEST RCX,RCX *)
| 0x1f0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 64)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x002a0a33: JZ 0x002a0a2a *)
(*        499: JZ 0x002a0a2a *)
| 0x1f3 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1ea 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0a35: VMOVDQU YMM5,ymmword ptr [RSI + 0x20] *)
(*        501: VMOVDQU YMM5,ymmword ptr [RSI + 0x20] *)
| 0x1f5 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0a3a: VMOVDQU YMM6,ymmword ptr [RSI + 0x40] *)
(*        506: VMOVDQU YMM6,ymmword ptr [RSI + 0x40] *)
| 0x1fa => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0a3f: LEA RCX,[RDI + RDX*0x1 + -0x81] *)
(*        511: LEA RCX,[RDI + RDX*0x1 + -0x81] *)
| 0x1ff => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff7f 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RCX (Var (V_TEMP 2))
)

(* 0x002a0a47: VMOVDQU YMM7,ymmword ptr [RSI + 0x60] *)
(*        519: VMOVDQU YMM7,ymmword ptr [RSI + 0x60] *)
| 0x207 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0a4c: VMOVDQU YMM8,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
(*        524: VMOVDQU YMM8,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x20c => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0a52: SUB RSI,RDI *)
(*        530: SUB RSI,RDI *)
| 0x212 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0a55: AND RCX,-0x20 *)
(*        533: AND RCX,-0x20 *)
| 0x215 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (BinOp OP_AND (Var R_RCX) (Word 0xffffffffffffffe0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0a59: ADD RSI,RCX *)
(*        537: ADD RSI,RCX *)
| 0x219 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0a5c: NOP dword ptr [RAX] *)
(*        540: NOP dword ptr [RAX] *)
| 0x21c => Some (4,
	Nop
)

(* 0x002a0a60: VMOVDQU YMM1,ymmword ptr [RSI + 0x60] *)
(*        544: VMOVDQU YMM1,ymmword ptr [RSI + 0x60] *)
| 0x220 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0a65: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
(*        549: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
| 0x225 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0a6a: VMOVDQU YMM3,ymmword ptr [RSI + 0x20] *)
(*        554: VMOVDQU YMM3,ymmword ptr [RSI + 0x20] *)
| 0x22a => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0a6f: VMOVDQU YMM4,ymmword ptr [RSI] *)
(*        559: VMOVDQU YMM4,ymmword ptr [RSI] *)
| 0x22f => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002a0a73: ADD RSI,-0x80 *)
(*        563: ADD RSI,-0x80 *)
| 0x233 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0a77: VMOVDQA ymmword ptr [RCX + 0x60],YMM1 *)
(*        567: VMOVDQA ymmword ptr [RCX + 0x60],YMM1 *)
| 0x237 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RCX) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a7c: VMOVDQA ymmword ptr [RCX + 0x40],YMM2 *)
(*        572: VMOVDQA ymmword ptr [RCX + 0x40],YMM2 *)
| 0x23c => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RCX) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a81: VMOVDQA ymmword ptr [RCX + 0x20],YMM3 *)
(*        577: VMOVDQA ymmword ptr [RCX + 0x20],YMM3 *)
| 0x241 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RCX) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a86: VMOVDQA ymmword ptr [RCX],YMM4 *)
(*        582: VMOVDQA ymmword ptr [RCX],YMM4 *)
| 0x246 => Some (4,
	Move (V_TEMP 0) (Var R_YMM4) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RCX) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0a8a: ADD RCX,-0x80 *)
(*        586: ADD RCX,-0x80 *)
| 0x24a => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RCX) (Word 0xffffffffffffff80 64)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RCX) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_PLUS (Var R_RCX) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0a8e: CMP RDI,RCX *)
(*        590: CMP RDI,RCX *)
| 0x24e => Some (3,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0a91: JC 0x002a0a60 *)
(*        593: JC 0x002a0a60 *)
| 0x251 => Some (2,
	If (Var R_CF) (
		Jmp (Word 0x220 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0a93: VMOVDQU ymmword ptr [RDI],YMM0 *)
(*        595: VMOVDQU ymmword ptr [RDI],YMM0 *)
| 0x253 => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0a97: VMOVDQU ymmword ptr [RDI + 0x20],YMM5 *)
(*        599: VMOVDQU ymmword ptr [RDI + 0x20],YMM5 *)
| 0x257 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM5) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0a9c: VMOVDQU ymmword ptr [RDI + 0x40],YMM6 *)
(*        604: VMOVDQU ymmword ptr [RDI + 0x40],YMM6 *)
| 0x25c => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM6) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0aa1: VMOVDQU ymmword ptr [RDI + 0x60],YMM7 *)
(*        609: VMOVDQU ymmword ptr [RDI + 0x60],YMM7 *)
| 0x261 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM7) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0aa6: VMOVDQU ymmword ptr [RDX + RDI*0x1 + -0x20],YMM8 *)
(*        614: VMOVDQU ymmword ptr [RDX + RDI*0x1 + -0x20],YMM8 *)
| 0x266 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDX)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM8) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0aac: VZEROUPPER *)
(*        620: VZEROUPPER *)
| 0x26c => Some (3,
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

(* 0x002a0aaf: RET *)
(*        623: RET *)
| 0x26f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0ac0: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
(*        640: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
| 0x280 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0ac5: TEST ECX,0xe00 *)
(*        645: TEST ECX,0xe00 *)
| 0x285 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xe00 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x002a0acb: JNZ 0x002a0b35 *)
(*        651: JNZ 0x002a0b35 *)
| 0x28b => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x2f5 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0acd: MOV R9,RCX *)
(*        653: MOV R9,RCX *)
| 0x28d => Some (3,
	Move R_R9 (Var R_RCX)
)

(* 0x002a0ad0: LEA RCX,[RSI + RDX*0x1 + -0x1] *)
(*        656: LEA RCX,[RSI + RDX*0x1 + -0x1] *)
| 0x290 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffff 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RCX (Var (V_TEMP 2))
)

(* 0x002a0ad5: OR RSI,0x3f *)
(*        661: OR RSI,0x3f *)
| 0x295 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RSI (BinOp OP_OR (Var R_RSI) (Word 0x3f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0ad9: LEA RDI,[RSI + R9*0x1 + 0x1] *)
(*        665: LEA RDI,[RSI + R9*0x1 + 0x1] *)
| 0x299 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0x1 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_R9) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move R_RDI (Var (V_TEMP 2))
)

(* 0x002a0ade: SUB RCX,RSI *)
(*        670: SUB RCX,RSI *)
| 0x29e => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RCX) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0ae1: INC RSI *)
(*        673: INC RSI *)
| 0x2a1 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0ae4: MOVSB.REP RDI,RSI *)
(*        676: MOVSB.REP RDI,RSI *)
| 0x2a4 => Some (2,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x2a6 64)
	) (* else *) (
		Nop
	) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (Var R_RDI) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 4) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 3))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (Var R_RSI) $;
	Move (V_TEMP 6) (BinOp OP_PLUS (Var R_RSI) (Word 0x1 64)) $;
	Move (V_TEMP 7) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 8) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 7))) $;
	Move R_RSI (BinOp OP_MINUS (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (Load (Var V_MEM64) (Var (V_TEMP 5)) LittleE 1) $;
	Move (V_TEMP 10) (Var (V_TEMP 9)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 10)) LittleE 1) $;
	Jmp (Word 0x2a4 64)
)

(* 0x002a0ae6: VMOVDQU ymmword ptr [R8],YMM0 *)
(*        678: VMOVDQU ymmword ptr [R8],YMM0 *)
| 0x2a6 => Some (5,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_R8) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0aeb: VMOVDQU ymmword ptr [R8 + 0x20],YMM1 *)
(*        683: VMOVDQU ymmword ptr [R8 + 0x20],YMM1 *)
| 0x2ab => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_R8) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0af1: VZEROUPPER *)
(*        689: VZEROUPPER *)
| 0x2b1 => Some (3,
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

(* 0x002a0af4: RET *)
(*        692: RET *)
| 0x2b4 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0b00: MOV RCX,RDI *)
(*        704: MOV RCX,RDI *)
| 0x2c0 => Some (3,
	Move R_RCX (Var R_RDI)
)

(* 0x002a0b03: SUB RCX,RSI *)
(*        707: SUB RCX,RSI *)
| 0x2c3 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RCX) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b06: CMP RCX,RDX *)
(*        710: CMP RCX,RDX *)
| 0x2c6 => Some (3,
	Move (V_TEMP 0) (Var R_RCX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0b09: JC 0x002a0a30 *)
(*        713: JC 0x002a0a30 *)
| 0x2c9 => Some (6,
	If (Var R_CF) (
		Jmp (Word 0x1f0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0b0f: MOV R8,RDI *)
(*        719: MOV R8,RDI *)
| 0x2cf => Some (3,
	Move R_R8 (Var R_RDI)
)

(* 0x002a0b12: CMP RDX,qword ptr [0x003215a0] *)
(*        722: CMP RDX,qword ptr [0x003215a0] *)
| 0x2d2 => Some (7,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Word 0x3215a0 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var (V_TEMP 0))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0b19: JNC 0x002a0b60 *)
(*        729: JNC 0x002a0b60 *)
| 0x2d9 => Some (2,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x320 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0b1b: TEST dword ptr [0x00321598],0x1 *)
(*        731: TEST dword ptr [0x00321598],0x1 *)
| 0x2db => Some (10,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Load (Var V_MEM64) (Word 0x321598 64) LittleE 4) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x002a0b25: JZ 0x002a0ac0 *)
(*        741: JZ 0x002a0ac0 *)
| 0x2e5 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x280 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0b27: CMP ECX,-0x40 *)
(*        743: CMP ECX,-0x40 *)
| 0x2e7 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RCX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0xffffffc0 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0xffffffc0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0xffffffc0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffc0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0xffffffc0 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0b2a: JA 0x002a09ab *)
(*        746: JA 0x002a09ab *)
| 0x2ea => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x16b 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0b30: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
(*        752: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
| 0x2f0 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0b35: SUB RSI,RDI *)
(*        757: SUB RSI,RDI *)
| 0x2f5 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b38: ADD RDI,0x3f *)
(*        760: ADD RDI,0x3f *)
| 0x2f8 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x3f 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x3f 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3f 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x3f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b3c: LEA RCX,[R8 + RDX*0x1] *)
(*        764: LEA RCX,[R8 + RDX*0x1] *)
| 0x2fc => Some (4,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_R8) (Var (V_TEMP 0))) $;
	Move R_RCX (Var (V_TEMP 1))
)

(* 0x002a0b40: AND RDI,-0x40 *)
(*        768: AND RDI,-0x40 *)
| 0x300 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (BinOp OP_AND (Var R_RDI) (Word 0xffffffffffffffc0 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b44: ADD RSI,RDI *)
(*        772: ADD RSI,RDI *)
| 0x304 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b47: SUB RCX,RDI *)
(*        775: SUB RCX,RDI *)
| 0x307 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RCX) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RDI)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RCX) (Var R_RDI)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b4a: MOVSB.REP RDI,RSI *)
(*        778: MOVSB.REP RDI,RSI *)
| 0x30a => Some (2,
	Move (V_TEMP 0) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x30c 64)
	) (* else *) (
		Nop
	) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (Var R_RDI) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 3) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 4) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 3))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 2)) (Var (V_TEMP 4))) $;
	Move (V_TEMP 5) (Var R_RSI) $;
	Move (V_TEMP 6) (BinOp OP_PLUS (Var R_RSI) (Word 0x1 64)) $;
	Move (V_TEMP 7) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 8) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 7))) $;
	Move R_RSI (BinOp OP_MINUS (Var (V_TEMP 6)) (Var (V_TEMP 8))) $;
	Move (V_TEMP 9) (Load (Var V_MEM64) (Var (V_TEMP 5)) LittleE 1) $;
	Move (V_TEMP 10) (Var (V_TEMP 9)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 1)) (Var (V_TEMP 10)) LittleE 1) $;
	Jmp (Word 0x30a 64)
)

(* 0x002a0b4c: VMOVDQU ymmword ptr [R8],YMM0 *)
(*        780: VMOVDQU ymmword ptr [R8],YMM0 *)
| 0x30c => Some (5,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_R8) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0b51: VMOVDQU ymmword ptr [R8 + 0x20],YMM1 *)
(*        785: VMOVDQU ymmword ptr [R8 + 0x20],YMM1 *)
| 0x311 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_R8) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0b57: VZEROUPPER *)
(*        791: VZEROUPPER *)
| 0x317 => Some (3,
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

(* 0x002a0b5a: RET *)
(*        794: RET *)
| 0x31a => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0b60: CMP RDX,qword ptr [0x0031a3f8] *)
(*        800: CMP RDX,qword ptr [0x0031a3f8] *)
| 0x320 => Some (7,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Word 0x31a3f8 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDX) (Var (V_TEMP 0))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_RDX) (Var (V_TEMP 0))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0b67: JC 0x002a0991 *)
(*        807: JC 0x002a0991 *)
| 0x327 => Some (6,
	If (Var R_CF) (
		Jmp (Word 0x151 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0b6d: NEG RCX *)
(*        813: NEG RCX *)
| 0x32d => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_RCX) (Word 0x0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 64) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 64) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 64) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RCX (UnOp OP_NEG (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RCX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RCX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b70: CMP RDX,RCX *)
(*        816: CMP RDX,RCX *)
| 0x330 => Some (3,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RCX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0b73: JA 0x002a09ab *)
(*        819: JA 0x002a09ab *)
| 0x333 => Some (6,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x16b 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0b79: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
(*        825: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
| 0x339 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0b7e: VMOVDQU ymmword ptr [RDI],YMM0 *)
(*        830: VMOVDQU ymmword ptr [RDI],YMM0 *)
| 0x33e => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0b82: VMOVDQU ymmword ptr [RDI + 0x20],YMM1 *)
(*        834: VMOVDQU ymmword ptr [RDI + 0x20],YMM1 *)
| 0x342 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0b87: MOV R8,RDI *)
(*        839: MOV R8,RDI *)
| 0x347 => Some (3,
	Move R_R8 (Var R_RDI)
)

(* 0x002a0b8a: AND R8,0x3f *)
(*        842: AND R8,0x3f *)
| 0x34a => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R8 (BinOp OP_AND (Var R_R8) (Word 0x3f 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R8) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R8) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b8e: SUB R8,0x40 *)
(*        846: SUB R8,0x40 *)
| 0x34e => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_R8) (Word 0x40 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Word 0x40 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R8) (Word 0x40 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x40 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_R8 (BinOp OP_MINUS (Var R_R8) (Word 0x40 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R8) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R8) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_R8) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b92: SUB RSI,R8 *)
(*        850: SUB RSI,R8 *)
| 0x352 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Var R_R8)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_R8)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Var R_R8)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b95: SUB RDI,R8 *)
(*        853: SUB RDI,R8 *)
| 0x355 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Var R_R8)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Var R_R8)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Var R_R8)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b98: ADD RDX,R8 *)
(*        856: ADD RDX,R8 *)
| 0x358 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDX) (Var R_R8)) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDX) (Var R_R8)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R8) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDX (BinOp OP_PLUS (Var R_RDX) (Var R_R8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0b9b: NOT ECX *)
(*        859: NOT ECX *)
| 0x35b => Some (2,
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (UnOp OP_NOT (Extract 31 0 (Var R_RCX)))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x002a0b9d: TEST ECX,0xf00 *)
(*        861: TEST ECX,0xf00 *)
| 0x35d => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xf00 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)))) $;
	Move (V_TEMP 1) (BinOp OP_AND (Var (V_TEMP 0)) (Word 0xff 32)) $;
	Move (V_TEMP 2) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 1)))) $;
	Move (V_TEMP 3) (BinOp OP_AND (Var (V_TEMP 2)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 3)) (Word 0x0 8))))
)

(* 0x002a0ba3: JZ 0x002a0d30 *)
(*        867: JZ 0x002a0d30 *)
| 0x363 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x4f0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0ba9: MOV R10,RDX *)
(*        873: MOV R10,RDX *)
| 0x369 => Some (3,
	Move R_R10 (Var R_RDX)
)

(* 0x002a0bac: SHR R10,0x4 *)
(*        876: SHR R10,0x4 *)
| 0x36c => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x4 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_R10) $;
	Move R_R10 (BinOp OP_RSHIFT (Var R_R10) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0x1 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 5)) (Word 0x0 64))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 6))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 8)) (Var (V_TEMP 9)))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 11) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 10)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 10)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x002a0bb0: CMP R10,qword ptr [0x003215a8] *)
(*        880: CMP R10,qword ptr [0x003215a8] *)
| 0x370 => Some (7,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Word 0x3215a8 64) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_R10) (Var (V_TEMP 0))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var R_R10) (Var (V_TEMP 0))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0bb7: JNC 0x002a0d30 *)
(*        887: JNC 0x002a0d30 *)
| 0x377 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x4f0 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0bbd: AND EDX,0x1fff *)
(*        893: AND EDX,0x1fff *)
| 0x37d => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x1fff 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0bc3: SHR R10,0x9 *)
(*        899: SHR R10,0x9 *)
| 0x383 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0x9 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_R10) $;
	Move R_R10 (BinOp OP_RSHIFT (Var R_R10) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0x1 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 5)) (Word 0x0 64))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 6))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 8)) (Var (V_TEMP 9)))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 11) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 10)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 10)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x002a0bc7: NOP word ptr [RAX + RAX*0x1] *)
(*        903: NOP word ptr [RAX + RAX*0x1] *)
| 0x387 => Some (9,
	Move (V_TEMP 0) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0)))
)

(* 0x002a0bd0: MOV ECX,0x20 *)
(*        912: MOV ECX,0x20 *)
| 0x390 => Some (5,
	Move R_RCX (Word 0x20 64)
)

(* 0x002a0bd5: NOP dword ptr [RSI + 0x80] *)
(*        917: NOP dword ptr [RSI + 0x80] *)
| 0x395 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x80 64))
)

(* 0x002a0bdc: NOP dword ptr [RSI + 0xc0] *)
(*        924: NOP dword ptr [RSI + 0xc0] *)
| 0x39c => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0xc0 64))
)

(* 0x002a0be3: NOP dword ptr [RSI + 0x100] *)
(*        931: NOP dword ptr [RSI + 0x100] *)
| 0x3a3 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x100 64))
)

(* 0x002a0bea: NOP dword ptr [RSI + 0x140] *)
(*        938: NOP dword ptr [RSI + 0x140] *)
| 0x3aa => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x140 64))
)

(* 0x002a0bf1: NOP dword ptr [RSI + 0x1080] *)
(*        945: NOP dword ptr [RSI + 0x1080] *)
| 0x3b1 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1080 64))
)

(* 0x002a0bf8: NOP dword ptr [RSI + 0x10c0] *)
(*        952: NOP dword ptr [RSI + 0x10c0] *)
| 0x3b8 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x10c0 64))
)

(* 0x002a0bff: NOP dword ptr [RSI + 0x1100] *)
(*        959: NOP dword ptr [RSI + 0x1100] *)
| 0x3bf => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1100 64))
)

(* 0x002a0c06: NOP dword ptr [RSI + 0x1140] *)
(*        966: NOP dword ptr [RSI + 0x1140] *)
| 0x3c6 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1140 64))
)

(* 0x002a0c0d: VMOVDQU YMM0,ymmword ptr [RSI] *)
(*        973: VMOVDQU YMM0,ymmword ptr [RSI] *)
| 0x3cd => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002a0c11: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
(*        977: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
| 0x3d1 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0c16: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
(*        982: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
| 0x3d6 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0c1b: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
(*        987: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
| 0x3db => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0c20: VMOVDQU YMM4,ymmword ptr [RSI + 0x1000] *)
(*        992: VMOVDQU YMM4,ymmword ptr [RSI + 0x1000] *)
| 0x3e0 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0c28: VMOVDQU YMM5,ymmword ptr [RSI + 0x1020] *)
(*       1000: VMOVDQU YMM5,ymmword ptr [RSI + 0x1020] *)
| 0x3e8 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1020 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0c30: VMOVDQU YMM6,ymmword ptr [RSI + 0x1040] *)
(*       1008: VMOVDQU YMM6,ymmword ptr [RSI + 0x1040] *)
| 0x3f0 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1040 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0c38: VMOVDQU YMM7,ymmword ptr [RSI + 0x1060] *)
(*       1016: VMOVDQU YMM7,ymmword ptr [RSI + 0x1060] *)
| 0x3f8 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1060 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0c40: SUB RSI,-0x80 *)
(*       1024: SUB RSI,-0x80 *)
| 0x400 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0c44: VMOVNTDQ ymmword ptr [RDI],YMM0 *)
(*       1028: VMOVNTDQ ymmword ptr [RDI],YMM0 *)
| 0x404 => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0c48: VMOVNTDQ ymmword ptr [RDI + 0x20],YMM1 *)
(*       1032: VMOVNTDQ ymmword ptr [RDI + 0x20],YMM1 *)
| 0x408 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0c4d: VMOVNTDQ ymmword ptr [RDI + 0x40],YMM2 *)
(*       1037: VMOVNTDQ ymmword ptr [RDI + 0x40],YMM2 *)
| 0x40d => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0c52: VMOVNTDQ ymmword ptr [RDI + 0x60],YMM3 *)
(*       1042: VMOVNTDQ ymmword ptr [RDI + 0x60],YMM3 *)
| 0x412 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0c57: VMOVNTDQ ymmword ptr [RDI + 0x1000],YMM4 *)
(*       1047: VMOVNTDQ ymmword ptr [RDI + 0x1000],YMM4 *)
| 0x417 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) $;
	Move (V_TEMP 1) (Var R_YMM4) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0c5f: VMOVNTDQ ymmword ptr [RDI + 0x1020],YMM5 *)
(*       1055: VMOVNTDQ ymmword ptr [RDI + 0x1020],YMM5 *)
| 0x41f => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1020 64)) $;
	Move (V_TEMP 1) (Var R_YMM5) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0c67: VMOVNTDQ ymmword ptr [RDI + 0x1040],YMM6 *)
(*       1063: VMOVNTDQ ymmword ptr [RDI + 0x1040],YMM6 *)
| 0x427 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1040 64)) $;
	Move (V_TEMP 1) (Var R_YMM6) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0c6f: VMOVNTDQ ymmword ptr [RDI + 0x1060],YMM7 *)
(*       1071: VMOVNTDQ ymmword ptr [RDI + 0x1060],YMM7 *)
| 0x42f => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1060 64)) $;
	Move (V_TEMP 1) (Var R_YMM7) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0c77: SUB RDI,-0x80 *)
(*       1079: SUB RDI,-0x80 *)
| 0x437 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0c7b: DEC ECX *)
(*       1083: DEC ECX *)
| 0x43b => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0c7d: JNZ 0x002a0bd5 *)
(*       1085: JNZ 0x002a0bd5 *)
| 0x43d => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x395 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0c83: ADD RDI,0x1000 *)
(*       1091: ADD RDI,0x1000 *)
| 0x443 => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1000 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0c8a: ADD RSI,0x1000 *)
(*       1098: ADD RSI,0x1000 *)
| 0x44a => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1000 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0c91: DEC R10 *)
(*       1105: DEC R10 *)
| 0x451 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_R10 (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0c94: JNZ 0x002a0bd0 *)
(*       1108: JNZ 0x002a0bd0 *)
| 0x454 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x390 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0c9a: SFENCE *)
(*       1114: SFENCE *)
| 0x45a => Some (3,
	Nop
)

(* 0x002a0c9d: CMP EDX,0x80 *)
(*       1117: CMP EDX,0x80 *)
| 0x45d => Some (6,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x80 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0ca3: JBE 0x002a0cfa *)
(*       1123: JBE 0x002a0cfa *)
| 0x463 => Some (2,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x4ba 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0ca5: NOP dword ptr [RSI + 0x80] *)
(*       1125: NOP dword ptr [RSI + 0x80] *)
| 0x465 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x80 64))
)

(* 0x002a0cac: NOP dword ptr [RSI + 0xc0] *)
(*       1132: NOP dword ptr [RSI + 0xc0] *)
| 0x46c => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0xc0 64))
)

(* 0x002a0cb3: NOP dword ptr [RDI + 0x80] *)
(*       1139: NOP dword ptr [RDI + 0x80] *)
| 0x473 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x80 64))
)

(* 0x002a0cba: NOP dword ptr [RDI + 0xc0] *)
(*       1146: NOP dword ptr [RDI + 0xc0] *)
| 0x47a => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0xc0 64))
)

(* 0x002a0cc1: VMOVDQU YMM0,ymmword ptr [RSI] *)
(*       1153: VMOVDQU YMM0,ymmword ptr [RSI] *)
| 0x481 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002a0cc5: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
(*       1157: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
| 0x485 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0cca: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
(*       1162: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
| 0x48a => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0ccf: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
(*       1167: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
| 0x48f => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0cd4: SUB RSI,-0x80 *)
(*       1172: SUB RSI,-0x80 *)
| 0x494 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0cd8: ADD EDX,-0x80 *)
(*       1176: ADD EDX,-0x80 *)
| 0x498 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffff80 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffff80 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffff80 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffff80 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0cdb: VMOVDQA ymmword ptr [RDI],YMM0 *)
(*       1179: VMOVDQA ymmword ptr [RDI],YMM0 *)
| 0x49b => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0cdf: VMOVDQA ymmword ptr [RDI + 0x20],YMM1 *)
(*       1183: VMOVDQA ymmword ptr [RDI + 0x20],YMM1 *)
| 0x49f => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0ce4: VMOVDQA ymmword ptr [RDI + 0x40],YMM2 *)
(*       1188: VMOVDQA ymmword ptr [RDI + 0x40],YMM2 *)
| 0x4a4 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0ce9: VMOVDQA ymmword ptr [RDI + 0x60],YMM3 *)
(*       1193: VMOVDQA ymmword ptr [RDI + 0x60],YMM3 *)
| 0x4a9 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0cee: SUB RDI,-0x80 *)
(*       1198: SUB RDI,-0x80 *)
| 0x4ae => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0cf2: CMP EDX,0x80 *)
(*       1202: CMP EDX,0x80 *)
| 0x4b2 => Some (6,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x80 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0cf8: JA 0x002a0ca5 *)
(*       1208: JA 0x002a0ca5 *)
| 0x4b8 => Some (2,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x465 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0cfa: VMOVDQU YMM0,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
(*       1210: VMOVDQU YMM0,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
| 0x4ba => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0d00: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
(*       1216: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
| 0x4c0 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffa0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0d06: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
(*       1222: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x4c6 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0d0c: VMOVDQU YMM3,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
(*       1228: VMOVDQU YMM3,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x4cc => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0d12: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x80],YMM0 *)
(*       1234: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x80],YMM0 *)
| 0x4d2 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0d18: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x60],YMM1 *)
(*       1240: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x60],YMM1 *)
| 0x4d8 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffa0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0d1e: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x40],YMM2 *)
(*       1246: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x40],YMM2 *)
| 0x4de => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0d24: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM3 *)
(*       1252: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM3 *)
| 0x4e4 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0d2a: VZEROUPPER *)
(*       1258: VZEROUPPER *)
| 0x4ea => Some (3,
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

(* 0x002a0d2d: RET *)
(*       1261: RET *)
| 0x4ed => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x002a0d30: MOV R10,RDX *)
(*       1264: MOV R10,RDX *)
| 0x4f0 => Some (3,
	Move R_R10 (Var R_RDX)
)

(* 0x002a0d33: AND EDX,0x3fff *)
(*       1267: AND EDX,0x3fff *)
| 0x4f3 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x3fff 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0d39: SHR R10,0xe *)
(*       1273: SHR R10,0xe *)
| 0x4f9 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Word 0xe 32) (Word 0x3f 32)) $;
	Move (V_TEMP 1) (Var R_R10) $;
	Move R_R10 (BinOp OP_RSHIFT (Var R_R10) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 3) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x1 32)) $;
	Move (V_TEMP 4) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 3)))) $;
	Move (V_TEMP 5) (BinOp OP_AND (Var (V_TEMP 4)) (Word 0x1 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 5)) (Word 0x0 64))) $;
	Move (V_TEMP 7) (BinOp OP_XOR (Var (V_TEMP 2)) (Word 1 8)) $;
	Move (V_TEMP 8) (BinOp OP_AND (Var (V_TEMP 7)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 9) (BinOp OP_AND (Var (V_TEMP 2)) (Var (V_TEMP 6))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 8)) (Var (V_TEMP 9)))) $;
	Move (V_TEMP 10) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x1 32))) $;
	Move (V_TEMP 11) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64))) $;
	Move (V_TEMP 12) (BinOp OP_XOR (Var (V_TEMP 10)) (Word 1 8)) $;
	Move (V_TEMP 13) (BinOp OP_AND (Var (V_TEMP 12)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 14) (BinOp OP_AND (Var (V_TEMP 10)) (Var (V_TEMP 11))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 13)) (Var (V_TEMP 14)))) $;
	Move (V_TEMP 15) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0)) (Word 0x0 32))) $;
	Move (V_TEMP 16) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 17) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 18) (BinOp OP_AND (Var (V_TEMP 17)) (Cast CAST_UNSIGNED 8 (Var R_SF))) $;
	Move (V_TEMP 19) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 16))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 18)) (Var (V_TEMP 19)))) $;
	Move (V_TEMP 20) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64))) $;
	Move (V_TEMP 21) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 22) (BinOp OP_AND (Var (V_TEMP 21)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 23) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 20))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 22)) (Var (V_TEMP 23)))) $;
	Move (V_TEMP 24) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 25) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 24)))) $;
	Move (V_TEMP 26) (BinOp OP_AND (Var (V_TEMP 25)) (Word 0x1 8)) $;
	Move (V_TEMP 27) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 26)) (Word 0x0 8))) $;
	Move (V_TEMP 28) (BinOp OP_XOR (Var (V_TEMP 15)) (Word 1 8)) $;
	Move (V_TEMP 29) (BinOp OP_AND (Var (V_TEMP 28)) (Cast CAST_UNSIGNED 8 (Var R_PF))) $;
	Move (V_TEMP 30) (BinOp OP_AND (Var (V_TEMP 15)) (Var (V_TEMP 27))) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 29)) (Var (V_TEMP 30))))
)

(* 0x002a0d3d: NOP dword ptr [RAX] *)
(*       1277: NOP dword ptr [RAX] *)
| 0x4fd => Some (3,
	Nop
)

(* 0x002a0d40: MOV ECX,0x20 *)
(*       1280: MOV ECX,0x20 *)
| 0x500 => Some (5,
	Move R_RCX (Word 0x20 64)
)

(* 0x002a0d45: NOP dword ptr [RSI + 0x80] *)
(*       1285: NOP dword ptr [RSI + 0x80] *)
| 0x505 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x80 64))
)

(* 0x002a0d4c: NOP dword ptr [RSI + 0xc0] *)
(*       1292: NOP dword ptr [RSI + 0xc0] *)
| 0x50c => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0xc0 64))
)

(* 0x002a0d53: NOP dword ptr [RSI + 0x1080] *)
(*       1299: NOP dword ptr [RSI + 0x1080] *)
| 0x513 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1080 64))
)

(* 0x002a0d5a: NOP dword ptr [RSI + 0x10c0] *)
(*       1306: NOP dword ptr [RSI + 0x10c0] *)
| 0x51a => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x10c0 64))
)

(* 0x002a0d61: NOP dword ptr [RSI + 0x2080] *)
(*       1313: NOP dword ptr [RSI + 0x2080] *)
| 0x521 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x2080 64))
)

(* 0x002a0d68: NOP dword ptr [RSI + 0x20c0] *)
(*       1320: NOP dword ptr [RSI + 0x20c0] *)
| 0x528 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20c0 64))
)

(* 0x002a0d6f: NOP dword ptr [RSI + 0x3080] *)
(*       1327: NOP dword ptr [RSI + 0x3080] *)
| 0x52f => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x3080 64))
)

(* 0x002a0d76: NOP dword ptr [RSI + 0x30c0] *)
(*       1334: NOP dword ptr [RSI + 0x30c0] *)
| 0x536 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x30c0 64))
)

(* 0x002a0d7d: VMOVDQU YMM0,ymmword ptr [RSI] *)
(*       1341: VMOVDQU YMM0,ymmword ptr [RSI] *)
| 0x53d => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002a0d81: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
(*       1345: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
| 0x541 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0d86: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
(*       1350: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
| 0x546 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0d8b: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
(*       1355: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
| 0x54b => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0d90: VMOVDQU YMM4,ymmword ptr [RSI + 0x1000] *)
(*       1360: VMOVDQU YMM4,ymmword ptr [RSI + 0x1000] *)
| 0x550 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1000 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM4 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0d98: VMOVDQU YMM5,ymmword ptr [RSI + 0x1020] *)
(*       1368: VMOVDQU YMM5,ymmword ptr [RSI + 0x1020] *)
| 0x558 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1020 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM5 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0da0: VMOVDQU YMM6,ymmword ptr [RSI + 0x1040] *)
(*       1376: VMOVDQU YMM6,ymmword ptr [RSI + 0x1040] *)
| 0x560 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1040 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM6 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0da8: VMOVDQU YMM7,ymmword ptr [RSI + 0x1060] *)
(*       1384: VMOVDQU YMM7,ymmword ptr [RSI + 0x1060] *)
| 0x568 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x1060 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM7 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0db0: VMOVDQU YMM8,ymmword ptr [RSI + 0x2000] *)
(*       1392: VMOVDQU YMM8,ymmword ptr [RSI + 0x2000] *)
| 0x570 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x2000 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM8 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0db8: VMOVDQU YMM9,ymmword ptr [RSI + 0x2020] *)
(*       1400: VMOVDQU YMM9,ymmword ptr [RSI + 0x2020] *)
| 0x578 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x2020 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM9 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0dc0: VMOVDQU YMM10,ymmword ptr [RSI + 0x2040] *)
(*       1408: VMOVDQU YMM10,ymmword ptr [RSI + 0x2040] *)
| 0x580 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x2040 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM10 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0dc8: VMOVDQU YMM11,ymmword ptr [RSI + 0x2060] *)
(*       1416: VMOVDQU YMM11,ymmword ptr [RSI + 0x2060] *)
| 0x588 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x2060 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM11 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0dd0: VMOVDQU YMM12,ymmword ptr [RSI + 0x3000] *)
(*       1424: VMOVDQU YMM12,ymmword ptr [RSI + 0x3000] *)
| 0x590 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x3000 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM12 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0dd8: VMOVDQU YMM13,ymmword ptr [RSI + 0x3020] *)
(*       1432: VMOVDQU YMM13,ymmword ptr [RSI + 0x3020] *)
| 0x598 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x3020 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM13 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0de0: VMOVDQU YMM14,ymmword ptr [RSI + 0x3040] *)
(*       1440: VMOVDQU YMM14,ymmword ptr [RSI + 0x3040] *)
| 0x5a0 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x3040 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM14 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0de8: VMOVDQU YMM15,ymmword ptr [RSI + 0x3060] *)
(*       1448: VMOVDQU YMM15,ymmword ptr [RSI + 0x3060] *)
| 0x5a8 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x3060 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM15 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0df0: SUB RSI,-0x80 *)
(*       1456: SUB RSI,-0x80 *)
| 0x5b0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0df4: VMOVNTDQ ymmword ptr [RDI],YMM0 *)
(*       1460: VMOVNTDQ ymmword ptr [RDI],YMM0 *)
| 0x5b4 => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0df8: VMOVNTDQ ymmword ptr [RDI + 0x20],YMM1 *)
(*       1464: VMOVNTDQ ymmword ptr [RDI + 0x20],YMM1 *)
| 0x5b8 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0dfd: VMOVNTDQ ymmword ptr [RDI + 0x40],YMM2 *)
(*       1469: VMOVNTDQ ymmword ptr [RDI + 0x40],YMM2 *)
| 0x5bd => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e02: VMOVNTDQ ymmword ptr [RDI + 0x60],YMM3 *)
(*       1474: VMOVNTDQ ymmword ptr [RDI + 0x60],YMM3 *)
| 0x5c2 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e07: VMOVNTDQ ymmword ptr [RDI + 0x1000],YMM4 *)
(*       1479: VMOVNTDQ ymmword ptr [RDI + 0x1000],YMM4 *)
| 0x5c7 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1000 64)) $;
	Move (V_TEMP 1) (Var R_YMM4) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e0f: VMOVNTDQ ymmword ptr [RDI + 0x1020],YMM5 *)
(*       1487: VMOVNTDQ ymmword ptr [RDI + 0x1020],YMM5 *)
| 0x5cf => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1020 64)) $;
	Move (V_TEMP 1) (Var R_YMM5) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e17: VMOVNTDQ ymmword ptr [RDI + 0x1040],YMM6 *)
(*       1495: VMOVNTDQ ymmword ptr [RDI + 0x1040],YMM6 *)
| 0x5d7 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1040 64)) $;
	Move (V_TEMP 1) (Var R_YMM6) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e1f: VMOVNTDQ ymmword ptr [RDI + 0x1060],YMM7 *)
(*       1503: VMOVNTDQ ymmword ptr [RDI + 0x1060],YMM7 *)
| 0x5df => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x1060 64)) $;
	Move (V_TEMP 1) (Var R_YMM7) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e27: VMOVNTDQ ymmword ptr [RDI + 0x2000],YMM8 *)
(*       1511: VMOVNTDQ ymmword ptr [RDI + 0x2000],YMM8 *)
| 0x5e7 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x2000 64)) $;
	Move (V_TEMP 1) (Var R_YMM8) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e2f: VMOVNTDQ ymmword ptr [RDI + 0x2020],YMM9 *)
(*       1519: VMOVNTDQ ymmword ptr [RDI + 0x2020],YMM9 *)
| 0x5ef => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x2020 64)) $;
	Move (V_TEMP 1) (Var R_YMM9) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e37: VMOVNTDQ ymmword ptr [RDI + 0x2040],YMM10 *)
(*       1527: VMOVNTDQ ymmword ptr [RDI + 0x2040],YMM10 *)
| 0x5f7 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x2040 64)) $;
	Move (V_TEMP 1) (Var R_YMM10) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e3f: VMOVNTDQ ymmword ptr [RDI + 0x2060],YMM11 *)
(*       1535: VMOVNTDQ ymmword ptr [RDI + 0x2060],YMM11 *)
| 0x5ff => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x2060 64)) $;
	Move (V_TEMP 1) (Var R_YMM11) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e47: VMOVNTDQ ymmword ptr [RDI + 0x3000],YMM12 *)
(*       1543: VMOVNTDQ ymmword ptr [RDI + 0x3000],YMM12 *)
| 0x607 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x3000 64)) $;
	Move (V_TEMP 1) (Var R_YMM12) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e4f: VMOVNTDQ ymmword ptr [RDI + 0x3020],YMM13 *)
(*       1551: VMOVNTDQ ymmword ptr [RDI + 0x3020],YMM13 *)
| 0x60f => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x3020 64)) $;
	Move (V_TEMP 1) (Var R_YMM13) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e57: VMOVNTDQ ymmword ptr [RDI + 0x3040],YMM14 *)
(*       1559: VMOVNTDQ ymmword ptr [RDI + 0x3040],YMM14 *)
| 0x617 => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x3040 64)) $;
	Move (V_TEMP 1) (Var R_YMM14) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e5f: VMOVNTDQ ymmword ptr [RDI + 0x3060],YMM15 *)
(*       1567: VMOVNTDQ ymmword ptr [RDI + 0x3060],YMM15 *)
| 0x61f => Some (8,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x3060 64)) $;
	Move (V_TEMP 1) (Var R_YMM15) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0e67: SUB RDI,-0x80 *)
(*       1575: SUB RDI,-0x80 *)
| 0x627 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0e6b: DEC ECX *)
(*       1579: DEC ECX *)
| 0x62b => Some (2,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RCX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_MINUS (Extract 31 0 (Var R_RCX)) (Word 0x1 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0e6d: JNZ 0x002a0d45 *)
(*       1581: JNZ 0x002a0d45 *)
| 0x62d => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x505 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0e73: ADD RDI,0x3000 *)
(*       1587: ADD RDI,0x3000 *)
| 0x633 => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Word 0x3000 64)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Word 0x3000 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3000 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Word 0x3000 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0e7a: ADD RSI,0x3000 *)
(*       1594: ADD RSI,0x3000 *)
| 0x63a => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSI) (Word 0x3000 64)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSI) (Word 0x3000 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3000 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_PLUS (Var R_RSI) (Word 0x3000 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0e81: DEC R10 *)
(*       1601: DEC R10 *)
| 0x641 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R10) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_R10 (BinOp OP_MINUS (Var R_R10) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R10) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R10) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_R10) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0e84: JNZ 0x002a0d40 *)
(*       1604: JNZ 0x002a0d40 *)
| 0x644 => Some (6,
	Move (V_TEMP 0) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x500 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0e8a: SFENCE *)
(*       1610: SFENCE *)
| 0x64a => Some (3,
	Nop
)

(* 0x002a0e8d: CMP EDX,0x80 *)
(*       1613: CMP EDX,0x80 *)
| 0x64d => Some (6,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x80 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0e93: JBE 0x002a0eea *)
(*       1619: JBE 0x002a0eea *)
| 0x653 => Some (2,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0))) (
		Jmp (Word 0x6aa 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0e95: NOP dword ptr [RSI + 0x80] *)
(*       1621: NOP dword ptr [RSI + 0x80] *)
| 0x655 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x80 64))
)

(* 0x002a0e9c: NOP dword ptr [RSI + 0xc0] *)
(*       1628: NOP dword ptr [RSI + 0xc0] *)
| 0x65c => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0xc0 64))
)

(* 0x002a0ea3: NOP dword ptr [RDI + 0x80] *)
(*       1635: NOP dword ptr [RDI + 0x80] *)
| 0x663 => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x80 64))
)

(* 0x002a0eaa: NOP dword ptr [RDI + 0xc0] *)
(*       1642: NOP dword ptr [RDI + 0xc0] *)
| 0x66a => Some (7,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0xc0 64))
)

(* 0x002a0eb1: VMOVDQU YMM0,ymmword ptr [RSI] *)
(*       1649: VMOVDQU YMM0,ymmword ptr [RSI] *)
| 0x671 => Some (4,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 32) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 0))))
)

(* 0x002a0eb5: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
(*       1653: VMOVDQU YMM1,ymmword ptr [RSI + 0x20] *)
| 0x675 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0eba: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
(*       1658: VMOVDQU YMM2,ymmword ptr [RSI + 0x40] *)
| 0x67a => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0ebf: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
(*       1663: VMOVDQU YMM3,ymmword ptr [RSI + 0x60] *)
| 0x67f => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RSI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Load (Var V_MEM64) (Var (V_TEMP 0)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 1))))
)

(* 0x002a0ec4: SUB RSI,-0x80 *)
(*       1668: SUB RSI,-0x80 *)
| 0x684 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSI (BinOp OP_MINUS (Var R_RSI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RSI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0ec8: ADD EDX,-0x80 *)
(*       1672: ADD EDX,-0x80 *)
| 0x688 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffff80 32)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffff80 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffff80 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RDX)) (Word 0xffffff80 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0ecb: VMOVDQA ymmword ptr [RDI],YMM0 *)
(*       1675: VMOVDQA ymmword ptr [RDI],YMM0 *)
| 0x68b => Some (4,
	Move (V_TEMP 0) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0)) LittleE 32)
)

(* 0x002a0ecf: VMOVDQA ymmword ptr [RDI + 0x20],YMM1 *)
(*       1679: VMOVDQA ymmword ptr [RDI + 0x20],YMM1 *)
| 0x68f => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x20 64)) $;
	Move (V_TEMP 1) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0ed4: VMOVDQA ymmword ptr [RDI + 0x40],YMM2 *)
(*       1684: VMOVDQA ymmword ptr [RDI + 0x40],YMM2 *)
| 0x694 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x40 64)) $;
	Move (V_TEMP 1) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0ed9: VMOVDQA ymmword ptr [RDI + 0x60],YMM3 *)
(*       1689: VMOVDQA ymmword ptr [RDI + 0x60],YMM3 *)
| 0x699 => Some (5,
	Move (V_TEMP 0) (BinOp OP_PLUS (Var R_RDI) (Word 0x60 64)) $;
	Move (V_TEMP 1) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 1)) LittleE 32)
)

(* 0x002a0ede: SUB RDI,-0x80 *)
(*       1694: SUB RDI,-0x80 *)
| 0x69e => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RDI) (Word 0xffffffffffffff80 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xffffffffffffff80 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_MINUS (Var R_RDI) (Word 0xffffffffffffff80 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)

(* 0x002a0ee2: CMP EDX,0x80 *)
(*       1698: CMP EDX,0x80 *)
| 0x6a2 => Some (6,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Word 0x80 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x80 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Word 0x80 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 32)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 32)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)

(* 0x002a0ee8: JA 0x002a0e95 *)
(*       1704: JA 0x002a0e95 *)
| 0x6a8 => Some (2,
	Move (V_TEMP 0) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Var (V_TEMP 0)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 1))) (
		Jmp (Word 0x655 64)
	) (* else *) (
		Nop
	)
)

(* 0x002a0eea: VMOVDQU YMM0,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
(*       1706: VMOVDQU YMM0,ymmword ptr [RSI + RDX*0x1 + -0x80] *)
| 0x6aa => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM0 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0ef0: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
(*       1712: VMOVDQU YMM1,ymmword ptr [RSI + RDX*0x1 + -0x60] *)
| 0x6b0 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffa0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM1 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0ef6: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
(*       1718: VMOVDQU YMM2,ymmword ptr [RSI + RDX*0x1 + -0x40] *)
| 0x6b6 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM2 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0efc: VMOVDQU YMM3,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
(*       1724: VMOVDQU YMM3,ymmword ptr [RSI + RDX*0x1 + -0x20] *)
| 0x6bc => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RSI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Load (Var V_MEM64) (Var (V_TEMP 2)) LittleE 32) $;
	Move R_YMM3 (Cast CAST_LOW 256 (Cast CAST_UNSIGNED 512 (Var (V_TEMP 3))))
)

(* 0x002a0f02: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x80],YMM0 *)
(*       1730: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x80],YMM0 *)
| 0x6c2 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffff80 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0f08: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x60],YMM1 *)
(*       1736: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x60],YMM1 *)
| 0x6c8 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffa0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0f0e: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x40],YMM2 *)
(*       1742: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x40],YMM2 *)
| 0x6ce => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffc0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM2) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0f14: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM3 *)
(*       1748: VMOVDQU ymmword ptr [RDI + RDX*0x1 + -0x20],YMM3 *)
| 0x6d4 => Some (6,
	Move (V_TEMP 0) (BinOp OP_PLUS (Word 0xffffffffffffffe0 64) (Var R_RDI)) $;
	Move (V_TEMP 1) (BinOp OP_TIMES (Var R_RDX) (Word 0x1 64)) $;
	Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 0)) (Var (V_TEMP 1))) $;
	Move (V_TEMP 3) (Var R_YMM3) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 2)) (Var (V_TEMP 3)) LittleE 32)
)

(* 0x002a0f1a: VZEROUPPER *)
(*       1754: VZEROUPPER *)
| 0x6da => Some (3,
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

(* 0x002a0f1d: RET *)
(*       1757: RET *)
| 0x6dd => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx memmove_avx_amd64.
Proof. Picinae_typecheck. Qed.


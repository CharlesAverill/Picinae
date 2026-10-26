(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: pthread_mutex_unlock at 0x199a70
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition pthread_mutex_unlock_amd64 : program := fun _ a => match a with

(* ---- pthread_mutex_unlock ---- *)

(* 0x00199a70: ENDBR64 *)
(*    1677936: ENDBR64 *)
| 0x199a70 => Some (4,
	Nop
)

(* 0x00199a74: MOV EAX,dword ptr [RDI + 0x10] *)
(*    1677940: MOV EAX,dword ptr [RDI + 0x10] *)
| 0x199a74 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00199a77: MOV EDX,EAX *)
(*    1677943: MOV EDX,EAX *)
| 0x199a77 => Some (2,
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Extract 31 0 (Var R_RAX))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00199a79: AND EDX,0x17f *)
(*    1677945: AND EDX,0x17f *)
| 0x199a79 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0x17f 32))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199a7f: AND EAX,0x7c *)
(*    1677951: AND EAX,0x7c *)
| 0x199a7f => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0x7c 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199a82: JNZ 0x00199ad0 *)
(*    1677954: JNZ 0x00199ad0 *)
| 0x199a82 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x199ad0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199a84: SUB RSP,0x18 *)
(*    1677956: SUB RSP,0x18 *)
| 0x199a84 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSP) (Word 0x18 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x18 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x18 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199a88: TEST EDX,EDX *)
(*    1677960: TEST EDX,EDX *)
| 0x199a88 => Some (2,
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

(* 0x00199a8a: JNZ 0x00199ae0 *)
(*    1677962: JNZ 0x00199ae0 *)
| 0x199a8a => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x199ae0 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199a8c: SUB dword ptr [RDI + 0xc],0x1 *)
(*    1677964: SUB dword ptr [RDI + 0xc],0x1 *)
| 0x199a8c => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0xc 64)) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x6b00)) (Word 0x1 32)))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x6b00)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x6b00) (BinOp OP_MINUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6b00)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6b00)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6b00)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199a90: MOV dword ptr [RDI + 0x8],0x0 *)
(*    1677968: MOV dword ptr [RDI + 0x8],0x0 *)
| 0x199a90 => Some (7,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b00) (Word 0x0 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00199a97: MOV ESI,dword ptr [RDI + 0x10] *)
(*    1677975: MOV ESI,dword ptr [RDI + 0x10] *)
| 0x199a97 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0x11f80))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00199a9a: AND ESI,0x80 *)
(*    1677978: AND ESI,0x80 *)
| 0x199a9a => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0x80 32))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199aa0: JZ 0x00199ab8 *)
(*    1677984: JZ 0x00199ab8 *)
| 0x199aa0 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x199ab8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199aa2: XOR EDX,EDX *)
(*    1677986: XOR EDX,EDX *)
| 0x199aa2 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (BinOp OP_XOR (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199aa4: XCHG dword ptr [RDI],EDX *)
(*    1677988: XCHG dword ptr [RDI],EDX *)
| 0x199aa4 => Some (2,
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move (V_TEMP 0xe8600) (Var (V_TEMP 0x6b00)) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RDX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0xe8600)))
)

(* 0x00199aa6: CMP EDX,0x1 *)
(*    1677990: CMP EDX,0x1 *)
| 0x199aa6 => Some (3,
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

(* 0x00199aa9: JG 0x00199b00 *)
(*    1677993: JG 0x00199b00 *)
| 0x199aa9 => Some (2,
	Move (V_TEMP 0x13100) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	Move (V_TEMP 0x13180) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_OF)) (Cast CAST_UNSIGNED 8 (Var R_SF)))) $;
	Move (V_TEMP 0x13280) (BinOp OP_AND (Var (V_TEMP 0x13100)) (Var (V_TEMP 0x13180))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13280))) (
		Jmp (Word 0x199b00 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199aab: NOP *)
(*    1677995: NOP *)
| 0x199aab => Some (1,
	Nop
)

(* 0x00199aac: ADD RSP,0x18 *)
(*    1677996: ADD RSP,0x18 *)
| 0x199aac => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) (Var R_RSP)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x18 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199ab0: RET *)
(*    1678000: RET *)
| 0x199ab0 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00199ab8: MOV EDX,dword ptr FS:[0x18] *)
(*    1678008: MOV EDX,dword ptr FS:[0x18] *)
| 0x199ab8 => Some (8,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Word 0x18 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00199ac0: TEST EDX,EDX *)
(*    1678016: TEST EDX,EDX *)
| 0x199ac0 => Some (2,
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

(* 0x00199ac2: JNZ 0x00199aa2 *)
(*    1678018: JNZ 0x00199aa2 *)
| 0x199ac2 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x199aa2 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199ac4: MOV dword ptr [RDI],0x0 *)
(*    1678020: MOV dword ptr [RDI],0x0 *)
| 0x199ac4 => Some (6,
	Move (V_TEMP 0x6b00) (Word 0x0 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00199aca: JMP 0x00199aab *)
(*    1678026: JMP 0x00199aab *)
| 0x199aca => Some (2,
	Jmp (Word 0x199aab 64)
)

(* 0x00199ad0: MOV ESI,0x1 *)
(*    1678032: MOV ESI,0x1 *)
| 0x199ad0 => Some (5,
	Move R_RSI (Word 0x1 64)
)

(* 0x00199ad5: JMP 0x001994c0 *)
(*    1678037: JMP 0x001994c0 *)
| 0x199ad5 => Some (5,
	Jmp (Word 0x1994c0 64)
)

(* 0x00199ae0: CMP EDX,0x100 *)
(*    1678048: CMP EDX,0x100 *)
| 0x199ae0 => Some (6,
	Move (V_TEMP 0x3e500) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e500)) (Word 0x100 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e500)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x100 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x100 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x100 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3e600) (BinOp OP_MINUS (Var (V_TEMP 0x3e500)) (Word 0x100 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e600)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e600)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e600)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199ae6: JNZ 0x00199b17 *)
(*    1678054: JNZ 0x00199b17 *)
| 0x199ae6 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x199b17 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199ae8: MOV ESI,dword ptr [RDI + 0x10] *)
(*    1678056: MOV ESI,dword ptr [RDI + 0x10] *)
| 0x199ae8 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Var (V_TEMP 0x11f80))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x00199aeb: ADD RSP,0x18 *)
(*    1678059: ADD RSP,0x18 *)
| 0x199aeb => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) (Var R_RSP)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x18 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x18 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199aef: AND ESI,0x80 *)
(*    1678063: AND ESI,0x80 *)
| 0x199aef => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0x80 32))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RSI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RSI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199af5: JMP 0x00190f50 *)
(*    1678069: JMP 0x00190f50 *)
| 0x199af5 => Some (5,
	Jmp (Word 0x190f50 64)
)

(* 0x00199b00: MOV dword ptr [RSP + 0xc],EAX *)
(*    1678080: MOV dword ptr [RSP + 0xc],EAX *)
| 0x199b00 => Some (4,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0xc 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6b00) (Extract 31 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00199b04: MOV qword ptr [RSP],RDI *)
(*    1678084: MOV qword ptr [RSP],RDI *)
| 0x199b04 => Some (4,
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00199b08: CALL 0x00191320 *)
(*    1678088: CALL 0x00191320 *)
| 0x199b08 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x199b0d 64) LittleE 8) $;
	Jmp (Word 0x191320 64)
)

(* 0x00199b0d: MOV EAX,dword ptr [RSP + 0xc] *)
(*    1678093: MOV EAX,dword ptr [RSP + 0xc] *)
| 0x199b0d => Some (4,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0xc 64) (Var R_RSP)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 4) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00199b11: MOV RDI,qword ptr [RSP] *)
(*    1678097: MOV RDI,qword ptr [RSP] *)
| 0x199b11 => Some (4,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x12000))
)

(* 0x00199b15: JMP 0x00199aab *)
(*    1678101: JMP 0x00199aab *)
| 0x199b15 => Some (2,
	Jmp (Word 0x199aab 64)
)

(* 0x00199b17: MOV ECX,dword ptr [RDI + 0x10] *)
(*    1678103: MOV ECX,dword ptr [RDI + 0x10] *)
| 0x199b17 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00199b1a: AND ECX,0x7f *)
(*    1678106: AND ECX,0x7f *)
| 0x199b1a => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x7f 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199b1d: CMP ECX,0x1 *)
(*    1678109: CMP ECX,0x1 *)
| 0x199b1d => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RCX)) $;
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

(* 0x00199b20: JNZ 0x00199b48 *)
(*    1678112: JNZ 0x00199b48 *)
| 0x199b20 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x199b48 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199b22: MOV EDX,dword ptr FS:[0x2d0] *)
(*    1678114: MOV EDX,dword ptr FS:[0x2d0] *)
| 0x199b22 => Some (8,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Word 0x2d0 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00199b2a: CMP dword ptr [RDI + 0x8],EDX *)
(*    1678122: CMP dword ptr [RDI + 0x8],EDX *)
| 0x199b2a => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x3ef80) (Var (V_TEMP 0x11f80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3ef80)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3f080) (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f080)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199b2d: JZ 0x00199b39 *)
(*    1678125: JZ 0x00199b39 *)
| 0x199b2d => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x199b39 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199b2f: MOV EAX,0x1 *)
(*    1678127: MOV EAX,0x1 *)
| 0x199b2f => Some (5,
	Move R_RAX (Word 0x1 64)
)

(* 0x00199b34: JMP 0x00199aac *)
(*    1678132: JMP 0x00199aac *)
| 0x199b34 => Some (5,
	Jmp (Word 0x199aac 64)
)

(* 0x00199b39: SUB dword ptr [RDI + 0x4],0x1 *)
(*    1678137: SUB dword ptr [RDI + 0x4],0x1 *)
| 0x199b39 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x6b00)) (Word 0x1 32)))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x6b00)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x6b00) (BinOp OP_MINUS (Var (V_TEMP 0x6b00)) (Word 0x1 32)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b00)) LittleE 4) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6b00)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6b00)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x6b00) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6b00)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199b3d: JNZ 0x00199aac *)
(*    1678141: JNZ 0x00199aac *)
| 0x199b3d => Some (6,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x199aac 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199b43: JMP 0x00199a8c *)
(*    1678147: JMP 0x00199a8c *)
| 0x199b43 => Some (5,
	Jmp (Word 0x199a8c 64)
)

(* 0x00199b48: MOV ECX,dword ptr [RDI + 0x10] *)
(*    1678152: MOV ECX,dword ptr [RDI + 0x10] *)
| 0x199b48 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x10 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00199b4b: AND ECX,0x7f *)
(*    1678155: AND ECX,0x7f *)
| 0x199b4b => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RCX (Concat (Extract 63 32 (Var R_RCX)) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0x7f 32))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RCX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RCX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199b4e: CMP ECX,0x3 *)
(*    1678158: CMP ECX,0x3 *)
| 0x199b4e => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RCX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x3 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x3 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x3 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x3 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199b51: JZ 0x00199a8c *)
(*    1678161: JZ 0x00199a8c *)
| 0x199b51 => Some (6,
	If (Var R_ZF) (
		Jmp (Word 0x199a8c 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199b57: CMP EDX,0x2 *)
(*    1678167: CMP EDX,0x2 *)
| 0x199b57 => Some (3,
	Move (V_TEMP 0x3e980) (Extract 31 0 (Var R_RDX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x2 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x2 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x2 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x2 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199b5a: JNZ 0x00199b73 *)
(*    1678170: JNZ 0x00199b73 *)
| 0x199b5a => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x199b73 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199b5c: MOV EDX,dword ptr FS:[0x2d0] *)
(*    1678172: MOV EDX,dword ptr FS:[0x2d0] *)
| 0x199b5c => Some (8,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Word 0x2d0 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x6580)) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00199b64: CMP dword ptr [RDI + 0x8],EDX *)
(*    1678180: CMP dword ptr [RDI + 0x8],EDX *)
| 0x199b64 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 4) $;
	Move (V_TEMP 0x3ef80) (Var (V_TEMP 0x11f80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3ef80)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3f080) (BinOp OP_MINUS (Var (V_TEMP 0x3ef80)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f080)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f080)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199b67: JNZ 0x00199b2f *)
(*    1678183: JNZ 0x00199b2f *)
| 0x199b67 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x199b2f 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199b69: CMP dword ptr [RDI],0x0 *)
(*    1678185: CMP dword ptr [RDI],0x0 *)
| 0x199b69 => Some (3,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move (V_TEMP 0x3e980) (Var (V_TEMP 0x11f80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e980)) (Word 0x0 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e980)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x3ea80) (BinOp OP_MINUS (Var (V_TEMP 0x3e980)) (Word 0x0 32)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3ea80)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3ea80)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00199b6c: JZ 0x00199b2f *)
(*    1678188: JZ 0x00199b2f *)
| 0x199b6c => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x199b2f 64)
	) (* else *) (
		Nop
	)
)

(* 0x00199b6e: JMP 0x00199a8c *)
(*    1678190: JMP 0x00199a8c *)
| 0x199b6e => Some (5,
	Jmp (Word 0x199a8c 64)
)

(* 0x00199b73: LEA RCX,[0x2e1880] *)
(*    1678195: LEA RCX,[0x2e1880] *)
| 0x199b73 => Some (7,
	Move R_RCX (Word 0x2e1880 64)
)

(* 0x00199b7a: MOV EDX,0x62 *)
(*    1678202: MOV EDX,0x62 *)
| 0x199b7a => Some (5,
	Move R_RDX (Word 0x62 64)
)

(* 0x00199b7f: LEA RSI,[0x2d95e6] *)
(*    1678207: LEA RSI,[0x2d95e6] *)
| 0x199b7f => Some (7,
	Move R_RSI (Word 0x2d95e6 64)
)

(* 0x00199b86: LEA RDI,[0x2ddf80] *)
(*    1678214: LEA RDI,[0x2ddf80] *)
| 0x199b86 => Some (7,
	Move R_RDI (Word 0x2ddf80 64)
)

(* 0x00199b8d: CALL 0x00139e50 *)
(*    1678221: CALL 0x00139e50 *)
| 0x199b8d => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x199b92 64) LittleE 8) $;
	Jmp (Word 0x139e50 64)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx pthread_mutex_unlock_amd64.
Proof. Picinae_typecheck. Qed.

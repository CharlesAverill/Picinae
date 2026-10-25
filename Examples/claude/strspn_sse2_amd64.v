(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: FUN_001c4780 at 0x1c4780
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition strspn_sse2_amd64 : program := fun _ a => match a with

(* ---- FUN_001c4780 ---- *)

(* 0x001c4780: ENDBR64 *)
(*    1853312: ENDBR64 *)
| 0x1c4780 => Some (4,
	Nop
)

(* 0x001c4784: MOV RDX,RDI *)
(*    1853316: MOV RDX,RDI *)
| 0x1c4784 => Some (3,
	Move R_RDX (Var R_RDI)
)

(* 0x001c4787: MOV R8,RDI *)
(*    1853319: MOV R8,RDI *)
| 0x1c4787 => Some (3,
	Move R_R8 (Var R_RDI)
)

(* 0x001c478a: SUB RSP,0x100 *)
(*    1853322: SUB RSP,0x100 *)
| 0x1c478a => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSP) (Word 0x100 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x100 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x100 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x100 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x100 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4791: MOV ECX,0x20 *)
(*    1853329: MOV ECX,0x20 *)
| 0x1c4791 => Some (5,
	Move R_RCX (Word 0x20 64)
)

(* 0x001c4796: MOV RDI,RSP *)
(*    1853334: MOV RDI,RSP *)
| 0x1c4796 => Some (3,
	Move R_RDI (Var R_RSP)
)

(* 0x001c4799: XOR EAX,EAX *)
(*    1853337: XOR EAX,EAX *)
| 0x1c4799 => Some (2,
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

(* 0x001c479b: CLD *)
(*    1853339: CLD *)
| 0x1c479b => Some (1,
	Move R_DF (Cast CAST_LOW 1 (Word 0x0 8))
)

(* 0x001c479c: STOSQ.REP RDI *)
(*    1853340: STOSQ.REP RDI *)
| 0x1c479c => Some (3,
	Move (V_TEMP 0x13500) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RCX) (Word 0x0 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x13500))) (
		Jmp (Word 0x1c479f 64)
	) (* else *) (
		Nop
	) $;
	Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x11b80) (Var R_RDI) $;
	Move (V_TEMP 0x11c00) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x11c80) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 0x11d00) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 0x11c80))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 0x11c00)) (Var (V_TEMP 0x11d00))) $;
	Move (V_TEMP 0x11e00) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x11b80)) (Var (V_TEMP 0x11e00)) LittleE 8) $;
	Jmp (Word 0x1c479c 64)
)

(* 0x001c479f: MOV RAX,RSI *)
(*    1853343: MOV RAX,RSI *)
| 0x1c479f => Some (3,
	Move R_RAX (Var R_RSI)
)

(* 0x001c47a2: NOP dword ptr CS:[RAX + RAX*0x1] *)
(*    1853346: NOP dword ptr CS:[RAX + RAX*0x1] *)
| 0x1c47a2 => Some (11,
	Move (V_TEMP 0x5580) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5680) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5580)))
)

(* 0x001c47ad: NOP dword ptr [RAX] *)
(*    1853357: NOP dword ptr [RAX] *)
| 0x1c47ad => Some (3,
	Nop
)

(* 0x001c47b0: MOV CL,byte ptr [RAX] *)
(*    1853360: MOV CL,byte ptr [RAX] *)
| 0x1c47b0 => Some (2,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RAX) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c47b2: TEST CL,CL *)
(*    1853362: TEST CL,CL *)
| 0x1c47b2 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Extract 7 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c47b4: JZ 0x001c47de *)
(*    1853364: JZ 0x001c47de *)
| 0x1c47b4 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c47de 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c47b6: MOV byte ptr [RSP + RCX*0x1],CL *)
(*    1853366: MOV byte ptr [RSP + RCX*0x1],CL *)
| 0x1c47b6 => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6a00) (Extract 7 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Var (V_TEMP 0x6a00)) LittleE 1)
)

(* 0x001c47b9: MOV CL,byte ptr [RAX + 0x1] *)
(*    1853369: MOV CL,byte ptr [RAX + 0x1] *)
| 0x1c47b9 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c47bc: TEST CL,0xff *)
(*    1853372: TEST CL,0xff *)
| 0x1c47bc => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x6fe80) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0xff 8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6fe80)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c47bf: JZ 0x001c47de *)
(*    1853375: JZ 0x001c47de *)
| 0x1c47bf => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c47de 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c47c1: MOV byte ptr [RSP + RCX*0x1],CL *)
(*    1853377: MOV byte ptr [RSP + RCX*0x1],CL *)
| 0x1c47c1 => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6a00) (Extract 7 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Var (V_TEMP 0x6a00)) LittleE 1)
)

(* 0x001c47c4: MOV CL,byte ptr [RAX + 0x2] *)
(*    1853380: MOV CL,byte ptr [RAX + 0x2] *)
| 0x1c47c4 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x2 64)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c47c7: TEST CL,0xff *)
(*    1853383: TEST CL,0xff *)
| 0x1c47c7 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x6fe80) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0xff 8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6fe80)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c47ca: JZ 0x001c47de *)
(*    1853386: JZ 0x001c47de *)
| 0x1c47ca => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c47de 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c47cc: MOV byte ptr [RSP + RCX*0x1],CL *)
(*    1853388: MOV byte ptr [RSP + RCX*0x1],CL *)
| 0x1c47cc => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6a00) (Extract 7 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Var (V_TEMP 0x6a00)) LittleE 1)
)

(* 0x001c47cf: MOV CL,byte ptr [RAX + 0x3] *)
(*    1853391: MOV CL,byte ptr [RAX + 0x3] *)
| 0x1c47cf => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x3 64)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c47d2: ADD RAX,0x4 *)
(*    1853394: ADD RAX,0x4 *)
| 0x1c47d2 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Word 0x4 64)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x4 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x4 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c47d6: MOV byte ptr [RSP + RCX*0x1],CL *)
(*    1853398: MOV byte ptr [RSP + RCX*0x1],CL *)
| 0x1c47d6 => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 0x4980))) $;
	Move (V_TEMP 0x6a00) (Extract 7 0 (Var R_RCX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4a80)) (Var (V_TEMP 0x6a00)) LittleE 1)
)

(* 0x001c47d9: TEST CL,0xff *)
(*    1853401: TEST CL,0xff *)
| 0x1c47d9 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x6fe80) (BinOp OP_AND (Extract 7 0 (Var R_RCX)) (Word 0xff 8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6fe80)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6fe80)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c47dc: JNZ 0x001c47b0 *)
(*    1853404: JNZ 0x001c47b0 *)
| 0x1c47dc => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1c47b0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c47de: LEA RAX,[RDX + -0x4] *)
(*    1853406: LEA RAX,[RDX + -0x4] *)
| 0x1c47de => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0xfffffffffffffffc 64)) $;
	Move R_RAX (Var (V_TEMP 0x4780))
)

(* 0x001c47e2: NOP dword ptr CS:[RAX + RAX*0x1] *)
(*    1853410: NOP dword ptr CS:[RAX + RAX*0x1] *)
| 0x1c47e2 => Some (11,
	Move (V_TEMP 0x5580) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5680) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5580)))
)

(* 0x001c47ed: NOP dword ptr [RAX] *)
(*    1853421: NOP dword ptr [RAX] *)
| 0x1c47ed => Some (3,
	Nop
)

(* 0x001c47f0: ADD RAX,0x4 *)
(*    1853424: ADD RAX,0x4 *)
| 0x1c47f0 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RAX) (Word 0x4 64)) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x4 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x4 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c47f4: MOV CL,byte ptr [RAX] *)
(*    1853428: MOV CL,byte ptr [RAX] *)
| 0x1c47f4 => Some (2,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RAX) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c47f6: TEST byte ptr [RSP + RCX*0x1],CL *)
(*    1853430: TEST byte ptr [RSP + RCX*0x1],CL *)
| 0x1c47f6 => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 0x4980))) $;
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var (V_TEMP 0x11e80)) (Extract 7 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c47f9: JZ 0x001c481c *)
(*    1853433: JZ 0x001c481c *)
| 0x1c47f9 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c481c 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c47fb: MOV CL,byte ptr [RAX + 0x1] *)
(*    1853435: MOV CL,byte ptr [RAX + 0x1] *)
| 0x1c47fb => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c47fe: TEST byte ptr [RSP + RCX*0x1],CL *)
(*    1853438: TEST byte ptr [RSP + RCX*0x1],CL *)
| 0x1c47fe => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 0x4980))) $;
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var (V_TEMP 0x11e80)) (Extract 7 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4801: JZ 0x001c4819 *)
(*    1853441: JZ 0x001c4819 *)
| 0x1c4801 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c4819 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4803: MOV CL,byte ptr [RAX + 0x2] *)
(*    1853443: MOV CL,byte ptr [RAX + 0x2] *)
| 0x1c4803 => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x2 64)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c4806: TEST byte ptr [RSP + RCX*0x1],CL *)
(*    1853446: TEST byte ptr [RSP + RCX*0x1],CL *)
| 0x1c4806 => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 0x4980))) $;
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var (V_TEMP 0x11e80)) (Extract 7 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4809: JZ 0x001c4816 *)
(*    1853449: JZ 0x001c4816 *)
| 0x1c4809 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c4816 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c480b: MOV CL,byte ptr [RAX + 0x3] *)
(*    1853451: MOV CL,byte ptr [RAX + 0x3] *)
| 0x1c480b => Some (3,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x3 64)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 1) $;
	Move R_RCX (Concat (Extract 63 8 (Var R_RCX)) (Var (V_TEMP 0x11e80)))
)

(* 0x001c480e: TEST byte ptr [RSP + RCX*0x1],CL *)
(*    1853454: TEST byte ptr [RSP + RCX*0x1],CL *)
| 0x1c480e => Some (3,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RSP) (Var (V_TEMP 0x4980))) $;
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var (V_TEMP 0x4a80)) LittleE 1) $;
	Move (V_TEMP 0x70280) (BinOp OP_AND (Var (V_TEMP 0x11e80)) (Extract 7 0 (Var R_RCX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70280)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70280)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4811: JNZ 0x001c47f0 *)
(*    1853457: JNZ 0x001c47f0 *)
| 0x1c4811 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x1c47f0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001c4813: INC RAX *)
(*    1853459: INC RAX *)
| 0x1c4813 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4816: INC RAX *)
(*    1853462: INC RAX *)
| 0x1c4816 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4819: INC RAX *)
(*    1853465: INC RAX *)
| 0x1c4819 => Some (3,
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c481c: ADD RSP,0x100 *)
(*    1853468: ADD RSP,0x100 *)
| 0x1c481c => Some (7,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x100 64)) (Var R_RSP)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x100 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x100 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x100 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4823: SUB RAX,RDX *)
(*    1853475: SUB RAX,RDX *)
| 0x1c4823 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RAX) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RDX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RDX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001c4826: RET *)
(*    1853478: RET *)
| 0x1c4826 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx strspn_sse2_amd64.
Proof. Picinae_typecheck. Qed.

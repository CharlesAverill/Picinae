(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: lsearch at 0x220c80
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition lsearch_amd64 : program := fun _ a => match a with

(* ---- lsearch ---- *)

(* 0x00220c80: ENDBR64 *)
(*    2231424: ENDBR64 *)
| 0x220c80 => Some (4,
	Nop
)

(* 0x00220c84: PUSH R15 *)
(*    2231428: PUSH R15 *)
| 0x220c84 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R15) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00220c86: MOV R15,RDI *)
(*    2231430: MOV R15,RDI *)
| 0x220c86 => Some (3,
	Move R_R15 (Var R_RDI)
)

(* 0x00220c89: PUSH R14 *)
(*    2231433: PUSH R14 *)
| 0x220c89 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R14) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00220c8b: MOV R14,R8 *)
(*    2231435: MOV R14,R8 *)
| 0x220c8b => Some (3,
	Move R_R14 (Var R_R8)
)

(* 0x00220c8e: PUSH R13 *)
(*    2231438: PUSH R13 *)
| 0x220c8e => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R13) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00220c90: MOV R13,RCX *)
(*    2231440: MOV R13,RCX *)
| 0x220c90 => Some (3,
	Move R_R13 (Var R_RCX)
)

(* 0x00220c93: PUSH R12 *)
(*    2231443: PUSH R12 *)
| 0x220c93 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00220c95: MOV R12,RSI *)
(*    2231445: MOV R12,RSI *)
| 0x220c95 => Some (3,
	Move R_R12 (Var R_RSI)
)

(* 0x00220c98: PUSH RBP *)
(*    2231448: PUSH RBP *)
| 0x220c98 => Some (1,
	Move (V_TEMP 0x27d80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00220c99: MOV RBP,RDX *)
(*    2231449: MOV RBP,RDX *)
| 0x220c99 => Some (3,
	Move R_RBP (Var R_RDX)
)

(* 0x00220c9c: PUSH RBX *)
(*    2231452: PUSH RBX *)
| 0x220c9c => Some (1,
	Move (V_TEMP 0x27d80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00220c9d: XOR EBX,EBX *)
(*    2231453: XOR EBX,EBX *)
| 0x220c9d => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RBX (Concat (Extract 63 32 (Var R_RBX)) (BinOp OP_XOR (Extract 31 0 (Var R_RBX)) (Extract 31 0 (Var R_RBX)))) $;
	Move R_RBX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RBX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RBX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RBX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RBX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00220c9f: SUB RSP,0x18 *)
(*    2231455: SUB RSP,0x18 *)
| 0x220c9f => Some (4,
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

(* 0x00220ca3: MOV RAX,qword ptr [RDX] *)
(*    2231459: MOV RAX,qword ptr [RDX] *)
| 0x220ca3 => Some (3,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x12000))
)

(* 0x00220ca6: MOV qword ptr [RSP + 0x8],RSI *)
(*    2231462: MOV qword ptr [RSP + 0x8],RSI *)
| 0x220ca6 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6b80) (Var R_RSI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00220cab: TEST RAX,RAX *)
(*    2231467: TEST RAX,RAX *)
| 0x220cab => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RAX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00220cae: JNZ 0x00220cc8 *)
(*    2231470: JNZ 0x00220cc8 *)
| 0x220cae => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x220cc8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00220cb0: JMP 0x00220ce8 *)
(*    2231472: JMP 0x00220ce8 *)
| 0x220cb0 => Some (2,
	Jmp (Word 0x220ce8 64)
)

(* 0x00220cb8: MOV RAX,qword ptr [RBP] *)
(*    2231480: MOV RAX,qword ptr [RBP] *)
| 0x220cb8 => Some (4,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RBP) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x12000))
)

(* 0x00220cbc: ADD RBX,0x1 *)
(*    2231484: ADD RBX,0x1 *)
| 0x220cbc => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RBX) (Word 0x1 64)) (Var R_RBX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RBX) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RBX (BinOp OP_PLUS (Var R_RBX) (Word 0x1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00220cc0: ADD R12,R13 *)
(*    2231488: ADD R12,R13 *)
| 0x220cc0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R12) (Var R_R13)) (Var R_R12)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R12) (Var R_R13)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_R12 (BinOp OP_PLUS (Var R_R12) (Var R_R13)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R12) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R12) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_R12) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00220cc3: CMP RBX,RAX *)
(*    2231491: CMP RBX,RAX *)
| 0x220cc3 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RBX) $;
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

(* 0x00220cc6: JNC 0x00220ce8 *)
(*    2231494: JNC 0x00220ce8 *)
| 0x220cc6 => Some (2,
	Move (V_TEMP 0x12780) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12780))) (
		Jmp (Word 0x220ce8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00220cc8: MOV RSI,R12 *)
(*    2231496: MOV RSI,R12 *)
| 0x220cc8 => Some (3,
	Move R_RSI (Var R_R12)
)

(* 0x00220ccb: MOV RDI,R15 *)
(*    2231499: MOV RDI,R15 *)
| 0x220ccb => Some (3,
	Move R_RDI (Var R_R15)
)

(* 0x00220cce: CALL R14 *)
(*    2231502: CALL R14 *)
| 0x220cce => Some (3,
	Move (V_TEMP 0x3cc00) (Var R_R14) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x220cd1 64) LittleE 8) $;
	Jmp (Var (V_TEMP 0x3cc00))
)

(* 0x00220cd1: TEST EAX,EAX *)
(*    2231505: TEST EAX,EAX *)
| 0x220cd1 => Some (2,
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

(* 0x00220cd3: JNZ 0x00220cb8 *)
(*    2231507: JNZ 0x00220cb8 *)
| 0x220cd3 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x220cb8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00220cd5: MOV RAX,qword ptr [RBP] *)
(*    2231509: MOV RAX,qword ptr [RBP] *)
| 0x220cd5 => Some (4,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RBP) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x12000))
)

(* 0x00220cd9: CMP RAX,RBX *)
(*    2231513: CMP RAX,RBX *)
| 0x220cd9 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_RAX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_RBX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RBX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RBX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_RBX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00220cdc: JBE 0x00220ce8 *)
(*    2231516: JBE 0x00220ce8 *)
| 0x220cdc => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x220ce8 64)
	) (* else *) (
		Nop
	)
)

(* 0x00220cde: TEST R12,R12 *)
(*    2231518: TEST R12,R12 *)
| 0x220cde => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_R12) (Var R_R12)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00220ce1: JNZ 0x00220d07 *)
(*    2231521: JNZ 0x00220d07 *)
| 0x220ce1 => Some (2,
	Move (V_TEMP 0x12880) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12880))) (
		Jmp (Word 0x220d07 64)
	) (* else *) (
		Nop
	)
)

(* 0x00220ce3: NOP dword ptr [RAX + RAX*0x1] *)
(*    2231523: NOP dword ptr [RAX + RAX*0x1] *)
| 0x220ce3 => Some (5,
	Move (V_TEMP 0x5100) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x5200) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x5100)))
)

(* 0x00220ce8: IMUL RAX,R13 *)
(*    2231528: IMUL RAX,R13 *)
| 0x220ce8 => Some (4,
	Move (V_TEMP 0x4b500) (Cast CAST_SIGNED 128 (Var R_RAX)) $;
	Move (V_TEMP 0x4b580) (Cast CAST_SIGNED 128 (Var R_R13)) $;
	Move (V_TEMP 0x4b680) (BinOp OP_TIMES (Var (V_TEMP 0x4b500)) (Var (V_TEMP 0x4b580))) $;
	Move R_RAX (BinOp OP_TIMES (Var R_RAX) (Var R_R13)) $;
	Move (V_TEMP 0x4b800) (Extract 127 64 (Var (V_TEMP 0x4b680))) $;
	Move (V_TEMP 0x2d200) (Cast CAST_SIGNED 128 (Var R_RAX)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2d200)) (Var (V_TEMP 0x4b680))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF)))
)

(* 0x00220cec: MOV RDI,qword ptr [RSP + 0x8] *)
(*    2231532: MOV RDI,qword ptr [RSP + 0x8] *)
| 0x220cec => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_RDI (Var (V_TEMP 0x12000))
)

(* 0x00220cf1: MOV RDX,R13 *)
(*    2231537: MOV RDX,R13 *)
| 0x220cf1 => Some (3,
	Move R_RDX (Var R_R13)
)

(* 0x00220cf4: MOV RSI,R15 *)
(*    2231540: MOV RSI,R15 *)
| 0x220cf4 => Some (3,
	Move R_RSI (Var R_R15)
)

(* 0x00220cf7: ADD RDI,RAX *)
(*    2231543: ADD RDI,RAX *)
| 0x220cf7 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RDI) (Var R_RAX)) (Var R_RDI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RDI) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RDI) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RDI (BinOp OP_PLUS (Var R_RDI) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDI) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RDI) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00220cfa: CALL 0x00128620 *)
(*    2231546: CALL 0x00128620 *)
| 0x220cfa => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x220cff 64) LittleE 8) $;
	Jmp (Word 0x128620 64)
)

(* 0x00220cff: ADD qword ptr [RBP],0x1 *)
(*    2231551: ADD qword ptr [RBP],0x1 *)
| 0x220cff => Some (5,
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var R_RBP) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x6b80)) (Word 0x1 64)) (Var (V_TEMP 0x6b80))))) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var R_RBP) LittleE 8) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x6b80)) (Word 0x1 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x6b80)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x6b80)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var R_RBP) LittleE 8) $;
	Move (V_TEMP 0x6b80) (BinOp OP_PLUS (Var (V_TEMP 0x6b80)) (Word 0x1 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RBP) (Var (V_TEMP 0x6b80)) LittleE 8) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var R_RBP) LittleE 8) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x6b80)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var R_RBP) LittleE 8) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x6b80)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x6b80) (Load (Var V_MEM64) (Var R_RBP) LittleE 8) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x6b80)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00220d04: MOV R12,RAX *)
(*    2231556: MOV R12,RAX *)
| 0x220d04 => Some (3,
	Move R_R12 (Var R_RAX)
)

(* 0x00220d07: ADD RSP,0x18 *)
(*    2231559: ADD RSP,0x18 *)
| 0x220d07 => Some (4,
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

(* 0x00220d0b: MOV RAX,R12 *)
(*    2231563: MOV RAX,R12 *)
| 0x220d0b => Some (3,
	Move R_RAX (Var R_R12)
)

(* 0x00220d0e: POP RBX *)
(*    2231566: POP RBX *)
| 0x220d0e => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55480))
)

(* 0x00220d0f: POP RBP *)
(*    2231567: POP RBP *)
| 0x220d0f => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55480))
)

(* 0x00220d10: POP R12 *)
(*    2231568: POP R12 *)
| 0x220d10 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55480))
)

(* 0x00220d12: POP R13 *)
(*    2231570: POP R13 *)
| 0x220d12 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R13 (Var (V_TEMP 0x55480))
)

(* 0x00220d14: POP R14 *)
(*    2231572: POP R14 *)
| 0x220d14 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R14 (Var (V_TEMP 0x55480))
)

(* 0x00220d16: POP R15 *)
(*    2231574: POP R15 *)
| 0x220d16 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R15 (Var (V_TEMP 0x55480))
)

(* 0x00220d18: RET *)
(*    2231576: RET *)
| 0x220d18 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx lsearch_amd64.
Proof. Picinae_typecheck. Qed.

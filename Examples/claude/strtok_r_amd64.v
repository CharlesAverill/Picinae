(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: strtok_r at 0x1a9350
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition strtok_r_amd64 : program := fun _ a => match a with

(* ---- strtok_r ---- *)

(* 0x001a9350: ENDBR64 *)
(*    1741648: ENDBR64 *)
| 0x1a9350 => Some (4,
	Nop
)

(* 0x001a9354: PUSH R13 *)
(*    1741652: PUSH R13 *)
| 0x1a9354 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R13) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x001a9356: MOV R13,RDX *)
(*    1741654: MOV R13,RDX *)
| 0x1a9356 => Some (3,
	Move R_R13 (Var R_RDX)
)

(* 0x001a9359: PUSH R12 *)
(*    1741657: PUSH R12 *)
| 0x1a9359 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x001a935b: PUSH RBP *)
(*    1741659: PUSH RBP *)
| 0x1a935b => Some (1,
	Move (V_TEMP 0x27d80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x001a935c: MOV RBP,RSI *)
(*    1741660: MOV RBP,RSI *)
| 0x1a935c => Some (3,
	Move R_RBP (Var R_RSI)
)

(* 0x001a935f: PUSH RBX *)
(*    1741663: PUSH RBX *)
| 0x1a935f => Some (1,
	Move (V_TEMP 0x27d80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x001a9360: MOV RBX,RDI *)
(*    1741664: MOV RBX,RDI *)
| 0x1a9360 => Some (3,
	Move R_RBX (Var R_RDI)
)

(* 0x001a9363: SUB RSP,0x8 *)
(*    1741667: SUB RSP,0x8 *)
| 0x1a9363 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RSP) (Word 0x8 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a9367: TEST RDI,RDI *)
(*    1741671: TEST RDI,RDI *)
| 0x1a9367 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RDI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a936a: JZ 0x001a93c0 *)
(*    1741674: JZ 0x001a93c0 *)
| 0x1a936a => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1a93c0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001a936c: CMP byte ptr [RBX],0x0 *)
(*    1741676: CMP byte ptr [RBX],0x0 *)
| 0x1a936c => Some (3,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RBX) LittleE 1) $;
	Move (V_TEMP 0x3e200) (Var (V_TEMP 0x11e80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e200)) (Word 0x0 8)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e200)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 8) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x3e300) (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e300)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e300)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e300)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a936f: JZ 0x001a93bb *)
(*    1741679: JZ 0x001a93bb *)
| 0x1a936f => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1a93bb 64)
	) (* else *) (
		Nop
	)
)

(* 0x001a9371: MOV RSI,RBP *)
(*    1741681: MOV RSI,RBP *)
| 0x1a9371 => Some (3,
	Move R_RSI (Var R_RBP)
)

(* 0x001a9374: MOV RDI,RBX *)
(*    1741684: MOV RDI,RBX *)
| 0x1a9374 => Some (3,
	Move R_RDI (Var R_RBX)
)

(* 0x001a9377: CALL 0x00128410 *)
(*    1741687: CALL 0x00128410 *)
| 0x1a9377 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1a937c 64) LittleE 8) $;
	Jmp (Word 0x128410 64)
)

(* 0x001a937c: LEA R12,[RBX + RAX*0x1] *)
(*    1741692: LEA R12,[RBX + RAX*0x1] *)
| 0x1a937c => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_RBX) (Var (V_TEMP 0x4980))) $;
	Move R_R12 (Var (V_TEMP 0x4a80))
)

(* 0x001a9380: CMP byte ptr [R12],0x0 *)
(*    1741696: CMP byte ptr [R12],0x0 *)
| 0x1a9380 => Some (5,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_R12) LittleE 1) $;
	Move (V_TEMP 0x3e200) (Var (V_TEMP 0x11e80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e200)) (Word 0x0 8)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e200)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 8) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x3e300) (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e300)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e300)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e300)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a9385: JZ 0x001a93b8 *)
(*    1741701: JZ 0x001a93b8 *)
| 0x1a9385 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1a93b8 64)
	) (* else *) (
		Nop
	)
)

(* 0x001a9387: MOV RSI,RBP *)
(*    1741703: MOV RSI,RBP *)
| 0x1a9387 => Some (3,
	Move R_RSI (Var R_RBP)
)

(* 0x001a938a: MOV RDI,R12 *)
(*    1741706: MOV RDI,R12 *)
| 0x1a938a => Some (3,
	Move R_RDI (Var R_R12)
)

(* 0x001a938d: CALL 0x00128570 *)
(*    1741709: CALL 0x00128570 *)
| 0x1a938d => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1a9392 64) LittleE 8) $;
	Jmp (Word 0x128570 64)
)

(* 0x001a9392: LEA RBX,[R12 + RAX*0x1] *)
(*    1741714: LEA RBX,[R12 + RAX*0x1] *)
| 0x1a9392 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_R12) (Var (V_TEMP 0x4980))) $;
	Move R_RBX (Var (V_TEMP 0x4a80))
)

(* 0x001a9396: CMP byte ptr [RBX],0x0 *)
(*    1741718: CMP byte ptr [RBX],0x0 *)
| 0x1a9396 => Some (3,
	Move (V_TEMP 0x11e80) (Load (Var V_MEM64) (Var R_RBX) LittleE 1) $;
	Move (V_TEMP 0x3e200) (Var (V_TEMP 0x11e80)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3e200)) (Word 0x0 8)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3e200)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 8) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x3e300) (BinOp OP_MINUS (Var (V_TEMP 0x3e200)) (Word 0x0 8)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3e300)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3e300)) (Word 0x0 8)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3e300)) (Word 0xff 8)) $;
	Move (V_TEMP 0x2c300) (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a9399: JZ 0x001a93a2 *)
(*    1741721: JZ 0x001a93a2 *)
| 0x1a9399 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1a93a2 64)
	) (* else *) (
		Nop
	)
)

(* 0x001a939b: MOV byte ptr [RBX],0x0 *)
(*    1741723: MOV byte ptr [RBX],0x0 *)
| 0x1a939b => Some (3,
	Move (V_TEMP 0x6a00) (Word 0x0 8) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RBX) (Var (V_TEMP 0x6a00)) LittleE 1)
)

(* 0x001a939e: ADD RBX,0x1 *)
(*    1741726: ADD RBX,0x1 *)
| 0x1a939e => Some (4,
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

(* 0x001a93a2: MOV qword ptr [R13],RBX *)
(*    1741730: MOV qword ptr [R13],RBX *)
| 0x1a93a2 => Some (4,
	Move (V_TEMP 0x6b80) (Var R_RBX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_R13) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x001a93a6: ADD RSP,0x8 *)
(*    1741734: ADD RSP,0x8 *)
| 0x1a93a6 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) (Var R_RSP)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RSP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 64) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RSP) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RSP) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RSP) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a93aa: MOV RAX,R12 *)
(*    1741738: MOV RAX,R12 *)
| 0x1a93aa => Some (3,
	Move R_RAX (Var R_R12)
)

(* 0x001a93ad: POP RBX *)
(*    1741741: POP RBX *)
| 0x1a93ad => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55480))
)

(* 0x001a93ae: POP RBP *)
(*    1741742: POP RBP *)
| 0x1a93ae => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55480))
)

(* 0x001a93af: POP R12 *)
(*    1741743: POP R12 *)
| 0x1a93af => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55480))
)

(* 0x001a93b1: POP R13 *)
(*    1741745: POP R13 *)
| 0x1a93b1 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R13 (Var (V_TEMP 0x55480))
)

(* 0x001a93b3: RET *)
(*    1741747: RET *)
| 0x1a93b3 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x001a93b8: MOV RBX,R12 *)
(*    1741752: MOV RBX,R12 *)
| 0x1a93b8 => Some (3,
	Move R_RBX (Var R_R12)
)

(* 0x001a93bb: XOR R12D,R12D *)
(*    1741755: XOR R12D,R12D *)
| 0x1a93bb => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R12 (Concat (Extract 63 32 (Var R_R12)) (BinOp OP_XOR (Extract 31 0 (Var R_R12)) (Extract 31 0 (Var R_R12)))) $;
	Move R_R12 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R12))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_R12)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_R12)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_R12)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a93be: JMP 0x001a93a2 *)
(*    1741758: JMP 0x001a93a2 *)
| 0x1a93be => Some (2,
	Jmp (Word 0x1a93a2 64)
)

(* 0x001a93c0: MOV RBX,qword ptr [RDX] *)
(*    1741760: MOV RBX,qword ptr [RDX] *)
| 0x1a93c0 => Some (3,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RDX) LittleE 8) $;
	Move R_RBX (Var (V_TEMP 0x12000))
)

(* 0x001a93c3: JMP 0x001a936c *)
(*    1741763: JMP 0x001a936c *)
| 0x1a93c3 => Some (2,
	Jmp (Word 0x1a936c 64)
)

| _ => None
end.

Theorem strtok_r_welltyped_lifted: welltyped_prog x64typctx strtok_r_amd64.
Proof. Picinae_typecheck. Qed.

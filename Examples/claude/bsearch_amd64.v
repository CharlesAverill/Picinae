(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: bsearch at 0x143680
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition bsearch_amd64 : program := fun _ a => match a with

(* ---- bsearch ---- *)

(* 0x00143680: ENDBR64 *)
(*    1324672: ENDBR64 *)
| 0x143680 => Some (4,
	Nop
)

(* 0x00143684: PUSH R15 *)
(*    1324676: PUSH R15 *)
| 0x143684 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R15) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00143686: PUSH R14 *)
(*    1324678: PUSH R14 *)
| 0x143686 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R14) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x00143688: PUSH R13 *)
(*    1324680: PUSH R13 *)
| 0x143688 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R13) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x0014368a: PUSH R12 *)
(*    1324682: PUSH R12 *)
| 0x14368a => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x0014368c: PUSH RBP *)
(*    1324684: PUSH RBP *)
| 0x14368c => Some (1,
	Move (V_TEMP 0x27d80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x0014368d: PUSH RBX *)
(*    1324685: PUSH RBX *)
| 0x14368d => Some (1,
	Move (V_TEMP 0x27d80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x0014368e: SUB RSP,0x18 *)
(*    1324686: SUB RSP,0x18 *)
| 0x14368e => Some (4,
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

(* 0x00143692: MOV qword ptr [RSP],RSI *)
(*    1324690: MOV qword ptr [RSP],RSI *)
| 0x143692 => Some (4,
	Move (V_TEMP 0x6b80) (Var R_RSI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00143696: MOV qword ptr [RSP + 0x8],RCX *)
(*    1324694: MOV qword ptr [RSP + 0x8],RCX *)
| 0x143696 => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x6b80) (Var R_RCX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4e80)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x0014369b: TEST RDX,RDX *)
(*    1324699: TEST RDX,RDX *)
| 0x14369b => Some (3,
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

(* 0x0014369e: JZ 0x001436e5 *)
(*    1324702: JZ 0x001436e5 *)
| 0x14369e => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1436e5 64)
	) (* else *) (
		Nop
	)
)

(* 0x001436a0: MOV RBP,RDI *)
(*    1324704: MOV RBP,RDI *)
| 0x1436a0 => Some (3,
	Move R_RBP (Var R_RDI)
)

(* 0x001436a3: MOV R12,RDX *)
(*    1324707: MOV R12,RDX *)
| 0x1436a3 => Some (3,
	Move R_R12 (Var R_RDX)
)

(* 0x001436a6: MOV R14,R8 *)
(*    1324710: MOV R14,R8 *)
| 0x1436a6 => Some (3,
	Move R_R14 (Var R_R8)
)

(* 0x001436a9: XOR R13D,R13D *)
(*    1324713: XOR R13D,R13D *)
| 0x1436a9 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R13 (Concat (Extract 63 32 (Var R_R13)) (BinOp OP_XOR (Extract 31 0 (Var R_R13)) (Extract 31 0 (Var R_R13)))) $;
	Move R_R13 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R13))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_R13)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_R13)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_R13)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001436ac: JMP 0x001436bb *)
(*    1324716: JMP 0x001436bb *)
| 0x1436ac => Some (2,
	Jmp (Word 0x1436bb 64)
)

(* 0x001436b0: JZ 0x001436e8 *)
(*    1324720: JZ 0x001436e8 *)
| 0x1436b0 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1436e8 64)
	) (* else *) (
		Nop
	)
)

(* 0x001436b2: LEA R13,[RBX + 0x1] *)
(*    1324722: LEA R13,[RBX + 0x1] *)
| 0x1436b2 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RBX) (Word 0x1 64)) $;
	Move R_R13 (Var (V_TEMP 0x4780))
)

(* 0x001436b6: CMP R12,R13 *)
(*    1324726: CMP R12,R13 *)
| 0x1436b6 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_R12) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_R13)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_R13)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_R13)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_R13)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001436b9: JBE 0x001436e5 *)
(*    1324729: JBE 0x001436e5 *)
| 0x1436b9 => Some (2,
	Move (V_TEMP 0x12980) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12980))) (
		Jmp (Word 0x1436e5 64)
	) (* else *) (
		Nop
	)
)

(* 0x001436bb: MOV R15,qword ptr [RSP + 0x8] *)
(*    1324731: MOV R15,qword ptr [RSP + 0x8] *)
| 0x1436bb => Some (5,
	Move (V_TEMP 0x4e80) (BinOp OP_PLUS (Word 0x8 64) (Var R_RSP)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4e80)) LittleE 8) $;
	Move R_R15 (Var (V_TEMP 0x12000))
)

(* 0x001436c0: LEA RBX,[R13 + R12*0x1] *)
(*    1324736: LEA RBX,[R13 + R12*0x1] *)
| 0x1436c0 => Some (5,
	Move (V_TEMP 0x5100) (BinOp OP_TIMES (Var R_R12) (Word 0x1 64)) $;
	Move (V_TEMP 0x5200) (BinOp OP_PLUS (Var R_R13) (Var (V_TEMP 0x5100))) $;
	Move R_RBX (Var (V_TEMP 0x5200))
)

(* 0x001436c5: MOV RDI,RBP *)
(*    1324741: MOV RDI,RBP *)
| 0x1436c5 => Some (3,
	Move R_RDI (Var R_RBP)
)

(* 0x001436c8: SHR RBX,0x1 *)
(*    1324744: SHR RBX,0x1 *)
| 0x1436c8 => Some (3,
	Move (V_TEMP 0x6e400) (BinOp OP_AND (Var R_RBX) (Word 0x1 64)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x6e400)) (Word 0x0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RBX (BinOp OP_RSHIFT (Var R_RBX) (Word 1 64)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RBX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RBX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RBX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001436cb: IMUL R15,RBX *)
(*    1324747: IMUL R15,RBX *)
| 0x1436cb => Some (4,
	Move (V_TEMP 0x4b500) (Cast CAST_SIGNED 128 (Var R_R15)) $;
	Move (V_TEMP 0x4b580) (Cast CAST_SIGNED 128 (Var R_RBX)) $;
	Move (V_TEMP 0x4b680) (BinOp OP_TIMES (Var (V_TEMP 0x4b500)) (Var (V_TEMP 0x4b580))) $;
	Move R_R15 (BinOp OP_TIMES (Var R_R15) (Var R_RBX)) $;
	Move (V_TEMP 0x4b800) (Extract 127 64 (Var (V_TEMP 0x4b680))) $;
	Move (V_TEMP 0x2d200) (Cast CAST_SIGNED 128 (Var R_R15)) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2d200)) (Var (V_TEMP 0x4b680))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF)))
)

(* 0x001436cf: ADD R15,qword ptr [RSP] *)
(*    1324751: ADD R15,qword ptr [RSP] *)
| 0x1436cf => Some (4,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R15) (Var (V_TEMP 0x12000))) (Var R_R15)))) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R15) (Var (V_TEMP 0x12000))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R15) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R15) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x12000)) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_R15 (BinOp OP_PLUS (Var R_R15) (Var (V_TEMP 0x12000))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_R15) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R15) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_R15) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001436d3: MOV RSI,R15 *)
(*    1324755: MOV RSI,R15 *)
| 0x1436d3 => Some (3,
	Move R_RSI (Var R_R15)
)

(* 0x001436d6: CALL R14 *)
(*    1324758: CALL R14 *)
| 0x1436d6 => Some (3,
	Move (V_TEMP 0x3cc00) (Var R_R14) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1436d9 64) LittleE 8) $;
	Jmp (Var (V_TEMP 0x3cc00))
)

(* 0x001436d9: TEST EAX,EAX *)
(*    1324761: TEST EAX,EAX *)
| 0x1436d9 => Some (2,
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

(* 0x001436db: JNS 0x001436b0 *)
(*    1324763: JNS 0x001436b0 *)
| 0x1436db => Some (2,
	Move (V_TEMP 0x12c00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_SF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12c00))) (
		Jmp (Word 0x1436b0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001436dd: MOV R12,RBX *)
(*    1324765: MOV R12,RBX *)
| 0x1436dd => Some (3,
	Move R_R12 (Var R_RBX)
)

(* 0x001436e0: CMP R12,R13 *)
(*    1324768: CMP R12,R13 *)
| 0x1436e0 => Some (3,
	Move (V_TEMP 0x3f100) (Var R_R12) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0x3f100)) (Var R_R13)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x3f100)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_R13)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_R13)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R13) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move (V_TEMP 0x3f200) (BinOp OP_MINUS (Var (V_TEMP 0x3f100)) (Var R_R13)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x3f200)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x3f200)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001436e3: JA 0x001436bb *)
(*    1324771: JA 0x001436bb *)
| 0x1436e3 => Some (2,
	Move (V_TEMP 0x12a00) (BinOp OP_OR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Cast CAST_UNSIGNED 8 (Var R_ZF))) $;
	Move (V_TEMP 0x12b00) (BinOp OP_XOR (Var (V_TEMP 0x12a00)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x12b00))) (
		Jmp (Word 0x1436bb 64)
	) (* else *) (
		Nop
	)
)

(* 0x001436e5: XOR R15D,R15D *)
(*    1324773: XOR R15D,R15D *)
| 0x1436e5 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_R15 (Concat (Extract 63 32 (Var R_R15)) (BinOp OP_XOR (Extract 31 0 (Var R_R15)) (Extract 31 0 (Var R_R15)))) $;
	Move R_R15 (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_R15))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_R15)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_R15)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_R15)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001436e8: ADD RSP,0x18 *)
(*    1324776: ADD RSP,0x18 *)
| 0x1436e8 => Some (4,
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

(* 0x001436ec: MOV RAX,R15 *)
(*    1324780: MOV RAX,R15 *)
| 0x1436ec => Some (3,
	Move R_RAX (Var R_R15)
)

(* 0x001436ef: POP RBX *)
(*    1324783: POP RBX *)
| 0x1436ef => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55480))
)

(* 0x001436f0: POP RBP *)
(*    1324784: POP RBP *)
| 0x1436f0 => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55480))
)

(* 0x001436f1: POP R12 *)
(*    1324785: POP R12 *)
| 0x1436f1 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55480))
)

(* 0x001436f3: POP R13 *)
(*    1324787: POP R13 *)
| 0x1436f3 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R13 (Var (V_TEMP 0x55480))
)

(* 0x001436f5: POP R14 *)
(*    1324789: POP R14 *)
| 0x1436f5 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R14 (Var (V_TEMP 0x55480))
)

(* 0x001436f7: POP R15 *)
(*    1324791: POP R15 *)
| 0x1436f7 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R15 (Var (V_TEMP 0x55480))
)

(* 0x001436f9: RET *)
(*    1324793: RET *)
| 0x1436f9 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem bsearch_welltyped_lifted: welltyped_prog x64typctx bsearch_amd64.
Proof. Picinae_typecheck. Qed.

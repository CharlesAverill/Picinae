(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: strcasecmp
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcasecmp_i386 : program := fun _ a => match a with

(* 0x00075f40: PUSH EBP *)
(*     483136: PUSH EBP *)
| 0x75f40 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBP) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00075f41: PUSH EDI *)
(*     483137: PUSH EDI *)
| 0x75f41 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EDI) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00075f42: PUSH ESI *)
(*     483138: PUSH ESI *)
| 0x75f42 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_ESI) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00075f43: PUSH EBX *)
(*     483139: PUSH EBX *)
| 0x75f43 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00075f44: CALL 0x0004a842 *)
(*     483140: CALL 0x0004a842 *)
| 0x75f44 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x75f49 32)) LittleE 4) $;
	Jmp (Word 0x4a842 32)
)

(* 0x00075f49: ADD EBX,0x3f053 *)
(*     483145: ADD EBX,0x3f053 *)
| 0x75f49 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EBX) (Word 0x3f053 32)) (Var R_EBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EBX) (Word 0x3f053 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3f053 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EBX (BinOp OP_PLUS (Var R_EBX) (Word 0x3f053 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EBX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EBX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EBX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f4f: SUB ESP,0xc *)
(*     483151: SUB ESP,0xc *)
| 0x75f4f => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_ESP) (Word 0xc 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xc 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f52: MOV EBP,dword ptr [ESP + 0x20] *)
(*     483154: MOV EBP,dword ptr [ESP + 0x20] *)
| 0x75f52 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x20 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EBP (Var (V_TEMP 0xb900))
)

(* 0x00075f56: MOV ESI,dword ptr [ESP + 0x24] *)
(*     483158: MOV ESI,dword ptr [ESP + 0x24] *)
| 0x75f56 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x24 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_ESI (Var (V_TEMP 0xb900))
)

(* 0x00075f5a: JMP 0x00075f62 *)
(*     483162: JMP 0x00075f62 *)
| 0x75f5a => Some (2,
	Jmp (Word 0x75f62 32)
)

(* 0x00075f5c: ADD EBP,0x1 *)
(*     483164: ADD EBP,0x1 *)
| 0x75f5c => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EBP) (Word 0x1 32)) (Var R_EBP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EBP) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBP) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EBP (BinOp OP_PLUS (Var R_EBP) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EBP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EBP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EBP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f5f: ADD ESI,0x1 *)
(*     483167: ADD ESI,0x1 *)
| 0x75f5f => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_ESI) (Word 0x1 32)) (Var R_ESI))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_ESI) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESI) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESI) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESI (BinOp OP_PLUS (Var R_ESI) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESI) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESI) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESI) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f62: MOVZX EAX,byte ptr [EBP] *)
(*     483170: MOVZX EAX,byte ptr [EBP] *)
| 0x75f62 => Some (4,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_EBP) LittleE 1) $;
	Move R_EAX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x00075f66: TEST AL,AL *)
(*     483174: TEST AL,AL *)
| 0x75f66 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x57000) (BinOp OP_AND (Extract 7 0 (Var R_EAX)) (Extract 7 0 (Var R_EAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x57000)) (Word 0xff 8)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f68: JZ 0x00075f96 *)
(*     483176: JZ 0x00075f96 *)
| 0x75f68 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x75f96 32)
	) (* else *) (
		Nop
	)
)

(* 0x00075f6a: MOVZX EDX,byte ptr [ESI] *)
(*     483178: MOVZX EDX,byte ptr [ESI] *)
| 0x75f6a => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) $;
	Move R_EDX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x00075f6d: TEST DL,DL *)
(*     483181: TEST DL,DL *)
| 0x75f6d => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x57000) (BinOp OP_AND (Extract 7 0 (Var R_EDX)) (Extract 7 0 (Var R_EDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x57000)) (Word 0xff 8)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f6f: JZ 0x00075f96 *)
(*     483183: JZ 0x00075f96 *)
| 0x75f6f => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x75f96 32)
	) (* else *) (
		Nop
	)
)

(* 0x00075f71: CMP AL,DL *)
(*     483185: CMP AL,DL *)
| 0x75f71 => Some (2,
	Move (V_TEMP 0x33200) (Extract 7 0 (Var R_EAX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33200)) (Extract 7 0 (Var R_EDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33200)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33200)) (Extract 7 0 (Var R_EDX))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33200)) (Extract 7 0 (Var R_EDX))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_EDX)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x33300) (BinOp OP_MINUS (Var (V_TEMP 0x33200)) (Extract 7 0 (Var R_EDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33300)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33300)) (Word 0x0 8))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33300)) (Word 0xff 8)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f73: JZ 0x00075f5c *)
(*     483187: JZ 0x00075f5c *)
| 0x75f73 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x75f5c 32)
	) (* else *) (
		Nop
	)
)

(* 0x00075f75: SUB ESP,0xc *)
(*     483189: SUB ESP,0xc *)
| 0x75f75 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_ESP) (Word 0xc 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xc 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f78: PUSH EAX *)
(*     483192: PUSH EAX *)
| 0x75f78 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EAX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00075f79: CALL 0x0004f635 *)
(*     483193: CALL 0x0004f635 *)
| 0x75f79 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x75f7e 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x00075f7e: MOV EDI,EAX *)
(*     483198: MOV EDI,EAX *)
| 0x75f7e => Some (2,
	Move R_EDI (Var R_EAX)
)

(* 0x00075f80: MOVZX EAX,byte ptr [ESI] *)
(*     483200: MOVZX EAX,byte ptr [ESI] *)
| 0x75f80 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) $;
	Move R_EAX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x00075f83: MOV dword ptr [ESP],EAX *)
(*     483203: MOV dword ptr [ESP],EAX *)
| 0x75f83 => Some (3,
	Move (V_TEMP 0x5180) (Var R_EAX) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x5180))) LittleE 4)
)

(* 0x00075f86: CALL 0x0004f635 *)
(*     483206: CALL 0x0004f635 *)
| 0x75f86 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x75f8b 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x00075f8b: ADD ESP,0x10 *)
(*     483211: ADD ESP,0x10 *)
| 0x75f8b => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_ESP) (Word 0x10 32)) (Var R_ESP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_ESP) (Word 0x10 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x10 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x10 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f8e: CMP EDI,EAX *)
(*     483214: CMP EDI,EAX *)
| 0x75f8e => Some (2,
	Move (V_TEMP 0x33500) (Var R_EDI) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33500)) (Var R_EAX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33500)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33600) (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33600)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33600)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33600)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f90: JZ 0x00075f5c *)
(*     483216: JZ 0x00075f5c *)
| 0x75f90 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x75f5c 32)
	) (* else *) (
		Nop
	)
)

(* 0x00075f92: MOVZX EAX,byte ptr [EBP] *)
(*     483218: MOVZX EAX,byte ptr [EBP] *)
| 0x75f92 => Some (4,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_EBP) LittleE 1) $;
	Move R_EAX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x00075f96: SUB ESP,0xc *)
(*     483222: SUB ESP,0xc *)
| 0x75f96 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_ESP) (Word 0xc 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xc 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075f99: PUSH EAX *)
(*     483225: PUSH EAX *)
| 0x75f99 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EAX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00075f9a: CALL 0x0004f635 *)
(*     483226: CALL 0x0004f635 *)
| 0x75f9a => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x75f9f 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x00075f9f: MOV EDI,EAX *)
(*     483231: MOV EDI,EAX *)
| 0x75f9f => Some (2,
	Move R_EDI (Var R_EAX)
)

(* 0x00075fa1: MOVZX EAX,byte ptr [ESI] *)
(*     483233: MOVZX EAX,byte ptr [ESI] *)
| 0x75fa1 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) $;
	Move R_EAX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x00075fa4: MOV dword ptr [ESP],EAX *)
(*     483236: MOV dword ptr [ESP],EAX *)
| 0x75fa4 => Some (3,
	Move (V_TEMP 0x5180) (Var R_EAX) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x5180))) LittleE 4)
)

(* 0x00075fa7: CALL 0x0004f635 *)
(*     483239: CALL 0x0004f635 *)
| 0x75fa7 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x75fac 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x00075fac: ADD ESP,0x1c *)
(*     483244: ADD ESP,0x1c *)
| 0x75fac => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_ESP) (Word 0x1c 32)) (Var R_ESP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_ESP) (Word 0x1c 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1c 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x1c 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075faf: MOV EDX,EAX *)
(*     483247: MOV EDX,EAX *)
| 0x75faf => Some (2,
	Move R_EDX (Var R_EAX)
)

(* 0x00075fb1: MOV EAX,EDI *)
(*     483249: MOV EAX,EDI *)
| 0x75fb1 => Some (2,
	Move R_EAX (Var R_EDI)
)

(* 0x00075fb3: POP EBX *)
(*     483251: POP EBX *)
| 0x75fb3 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x00075fb4: POP ESI *)
(*     483252: POP ESI *)
| 0x75fb4 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_ESI (Var (V_TEMP 0x43980))
)

(* 0x00075fb5: SUB EAX,EDX *)
(*     483253: SUB EAX,EDX *)
| 0x75fb5 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EAX) (Var R_EDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Var R_EDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Var R_EDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_MINUS (Var R_EAX) (Var R_EDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075fb7: POP EDI *)
(*     483255: POP EDI *)
| 0x75fb7 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EDI (Var (V_TEMP 0x43980))
)

(* 0x00075fb8: POP EBP *)
(*     483256: POP EBP *)
| 0x75fb8 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBP (Var (V_TEMP 0x43980))
)

(* 0x00075fb9: RET *)
(*     483257: RET *)
| 0x75fb9 => Some (1,
	Move R_EIP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Jmp (Var R_EIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x86typctx strcasecmp_i386.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: strncasecmp
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strncasecmp_i386 : program := fun _ a => match a with

(* 0x000761b4: CALL 0x0004a83e *)
(*     483764: CALL 0x0004a83e *)
| 0x761b4 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x761b9 32)) LittleE 4) $;
	Jmp (Word 0x4a83e 32)
)

(* 0x000761b9: ADD EAX,0x3ede3 *)
(*     483769: ADD EAX,0x3ede3 *)
| 0x761b9 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EAX) (Word 0x3ede3 32)) (Var R_EAX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EAX) (Word 0x3ede3 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3ede3 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_PLUS (Var R_EAX) (Word 0x3ede3 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761be: PUSH EBP *)
(*     483774: PUSH EBP *)
| 0x761be => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBP) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x000761bf: PUSH EDI *)
(*     483775: PUSH EDI *)
| 0x761bf => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EDI) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x000761c0: PUSH ESI *)
(*     483776: PUSH ESI *)
| 0x761c0 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_ESI) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x000761c1: PUSH EBX *)
(*     483777: PUSH EBX *)
| 0x761c1 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x000761c2: SUB ESP,0x1c *)
(*     483778: SUB ESP,0x1c *)
| 0x761c2 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_ESP) (Word 0x1c 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0x1c 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0x1c 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1c 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x1c 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761c5: MOV EDX,dword ptr [ESP + 0x38] *)
(*     483781: MOV EDX,dword ptr [ESP + 0x38] *)
| 0x761c5 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x38 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDX (Var (V_TEMP 0xb900))
)

(* 0x000761c9: MOV ECX,dword ptr [ESP + 0x30] *)
(*     483785: MOV ECX,dword ptr [ESP + 0x30] *)
| 0x761c9 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x30 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_ECX (Var (V_TEMP 0xb900))
)

(* 0x000761cd: MOV dword ptr [ESP + 0xc],EAX *)
(*     483789: MOV dword ptr [ESP + 0xc],EAX *)
| 0x761cd => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0xc 32) (Var R_ESP)) $;
	Move (V_TEMP 0x5180) (Var R_EAX) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0x3b00)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x5180))) LittleE 4)
)

(* 0x000761d1: XOR EAX,EAX *)
(*     483793: XOR EAX,EAX *)
| 0x761d1 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_EAX (BinOp OP_XOR (Var R_EAX) (Var R_EAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761d3: MOV EDI,dword ptr [ESP + 0x34] *)
(*     483795: MOV EDI,dword ptr [ESP + 0x34] *)
| 0x761d3 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x34 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDI (Var (V_TEMP 0xb900))
)

(* 0x000761d7: TEST EDX,EDX *)
(*     483799: TEST EDX,EDX *)
| 0x761d7 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x57200) (BinOp OP_AND (Var R_EDX) (Var R_EDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x57200)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x57200)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x57200)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761d9: JZ 0x00076258 *)
(*     483801: JZ 0x00076258 *)
| 0x761d9 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x76258 32)
	) (* else *) (
		Nop
	)
)

(* 0x000761db: SUB EDX,0x1 *)
(*     483803: SUB EDX,0x1 *)
| 0x761db => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EDX) (Word 0x1 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EDX) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EDX) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EDX (BinOp OP_MINUS (Var R_EDX) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761de: MOV ESI,ECX *)
(*     483806: MOV ESI,ECX *)
| 0x761de => Some (2,
	Move R_ESI (Var R_ECX)
)

(* 0x000761e0: JMP 0x000761e8 *)
(*     483808: JMP 0x000761e8 *)
| 0x761e0 => Some (2,
	Jmp (Word 0x761e8 32)
)

(* 0x000761e2: ADD ESI,0x1 *)
(*     483810: ADD ESI,0x1 *)
| 0x761e2 => Some (3,
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

(* 0x000761e5: ADD EDI,0x1 *)
(*     483813: ADD EDI,0x1 *)
| 0x761e5 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EDI) (Word 0x1 32)) (Var R_EDI))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EDI) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDI) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDI) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EDI (BinOp OP_PLUS (Var R_EDI) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDI) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDI) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDI) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761e8: MOVZX EAX,byte ptr [ESI] *)
(*     483816: MOVZX EAX,byte ptr [ESI] *)
| 0x761e8 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) $;
	Move R_EAX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x000761eb: TEST AL,AL *)
(*     483819: TEST AL,AL *)
| 0x761eb => Some (2,
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

(* 0x000761ed: JZ 0x00076235 *)
(*     483821: JZ 0x00076235 *)
| 0x761ed => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x76235 32)
	) (* else *) (
		Nop
	)
)

(* 0x000761ef: LEA EBP,[ECX + EDX*0x1] *)
(*     483823: LEA EBP,[ECX + EDX*0x1] *)
| 0x761ef => Some (3,
	Move (V_TEMP 0x3500) (BinOp OP_TIMES (Var R_EDX) (Word 0x1 32)) $;
	Move (V_TEMP 0x3600) (BinOp OP_PLUS (Var R_ECX) (Var (V_TEMP 0x3500))) $;
	Move R_EBP (Var (V_TEMP 0x3600))
)

(* 0x000761f2: MOVZX EBX,byte ptr [EDI] *)
(*     483826: MOVZX EBX,byte ptr [EDI] *)
| 0x761f2 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_EDI) LittleE 1) $;
	Move R_EBX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x000761f5: CMP ESI,EBP *)
(*     483829: CMP ESI,EBP *)
| 0x761f5 => Some (2,
	Move (V_TEMP 0x33500) (Var R_ESI) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33500)) (Var R_EBP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33500)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EBP)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EBP)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBP) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33600) (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EBP)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33600)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33600)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33600)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761f7: JZ 0x00076235 *)
(*     483831: JZ 0x00076235 *)
| 0x761f7 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x76235 32)
	) (* else *) (
		Nop
	)
)

(* 0x000761f9: TEST BL,BL *)
(*     483833: TEST BL,BL *)
| 0x761f9 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x57000) (BinOp OP_AND (Extract 7 0 (Var R_EBX)) (Extract 7 0 (Var R_EBX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x57000)) (Word 0xff 8)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761fb: JZ 0x00076235 *)
(*     483835: JZ 0x00076235 *)
| 0x761fb => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x76235 32)
	) (* else *) (
		Nop
	)
)

(* 0x000761fd: CMP AL,BL *)
(*     483837: CMP AL,BL *)
| 0x761fd => Some (2,
	Move (V_TEMP 0x33200) (Extract 7 0 (Var R_EAX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33200)) (Extract 7 0 (Var R_EBX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33200)) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33200)) (Extract 7 0 (Var R_EBX))) (Word 7 8)) (Word 1 8))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33200)) (Extract 7 0 (Var R_EBX))) (Word 7 8)) (Word 1 8)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 7 0 (Var R_EBX)) (Word 7 8)) (Word 1 8))) (Word 1 8))))) $;
	Move (V_TEMP 0x33300) (BinOp OP_MINUS (Var (V_TEMP 0x33200)) (Extract 7 0 (Var R_EBX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33300)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33300)) (Word 0x0 8))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33300)) (Word 0xff 8)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000761ff: JZ 0x000761e2 *)
(*     483839: JZ 0x000761e2 *)
| 0x761ff => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x761e2 32)
	) (* else *) (
		Nop
	)
)

(* 0x00076201: MOV dword ptr [ESP + 0x30],ECX *)
(*     483841: MOV dword ptr [ESP + 0x30],ECX *)
| 0x76201 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x30 32) (Var R_ESP)) $;
	Move (V_TEMP 0x5180) (Var R_ECX) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0x3b00)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x5180))) LittleE 4)
)

(* 0x00076205: SUB ESP,0xc *)
(*     483845: SUB ESP,0xc *)
| 0x76205 => Some (3,
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

(* 0x00076208: MOV dword ptr [ESP + 0x14],EDX *)
(*     483848: MOV dword ptr [ESP + 0x14],EDX *)
| 0x76208 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x14 32) (Var R_ESP)) $;
	Move (V_TEMP 0x5180) (Var R_EDX) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0x3b00)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x5180))) LittleE 4)
)

(* 0x0007620c: PUSH EAX *)
(*     483852: PUSH EAX *)
| 0x7620c => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EAX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0007620d: MOV EBX,dword ptr [ESP + 0x1c] *)
(*     483853: MOV EBX,dword ptr [ESP + 0x1c] *)
| 0x7620d => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x1c 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EBX (Var (V_TEMP 0xb900))
)

(* 0x00076211: CALL 0x0004f635 *)
(*     483857: CALL 0x0004f635 *)
| 0x76211 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x76216 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x00076216: MOV EBP,EAX *)
(*     483862: MOV EBP,EAX *)
| 0x76216 => Some (2,
	Move R_EBP (Var R_EAX)
)

(* 0x00076218: MOVZX EAX,byte ptr [EDI] *)
(*     483864: MOVZX EAX,byte ptr [EDI] *)
| 0x76218 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_EDI) LittleE 1) $;
	Move R_EAX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x0007621b: MOV dword ptr [ESP],EAX *)
(*     483867: MOV dword ptr [ESP],EAX *)
| 0x7621b => Some (3,
	Move (V_TEMP 0x5180) (Var R_EAX) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x5180))) LittleE 4)
)

(* 0x0007621e: CALL 0x0004f635 *)
(*     483870: CALL 0x0004f635 *)
| 0x7621e => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x76223 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x00076223: ADD ESP,0x10 *)
(*     483875: ADD ESP,0x10 *)
| 0x76223 => Some (3,
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

(* 0x00076226: MOV EDX,dword ptr [ESP + 0x8] *)
(*     483878: MOV EDX,dword ptr [ESP + 0x8] *)
| 0x76226 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x8 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDX (Var (V_TEMP 0xb900))
)

(* 0x0007622a: MOV ECX,dword ptr [ESP + 0x30] *)
(*     483882: MOV ECX,dword ptr [ESP + 0x30] *)
| 0x7622a => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x30 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_ECX (Var (V_TEMP 0xb900))
)

(* 0x0007622e: CMP EBP,EAX *)
(*     483886: CMP EBP,EAX *)
| 0x7622e => Some (2,
	Move (V_TEMP 0x33500) (Var R_EBP) $;
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

(* 0x00076230: JZ 0x000761e2 *)
(*     483888: JZ 0x000761e2 *)
| 0x76230 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x761e2 32)
	) (* else *) (
		Nop
	)
)

(* 0x00076232: MOVZX EAX,byte ptr [ESI] *)
(*     483890: MOVZX EAX,byte ptr [ESI] *)
| 0x76232 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_ESI) LittleE 1) $;
	Move R_EAX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x00076235: SUB ESP,0xc *)
(*     483893: SUB ESP,0xc *)
| 0x76235 => Some (3,
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

(* 0x00076238: PUSH EAX *)
(*     483896: PUSH EAX *)
| 0x76238 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EAX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00076239: MOV EBX,dword ptr [ESP + 0x1c] *)
(*     483897: MOV EBX,dword ptr [ESP + 0x1c] *)
| 0x76239 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x1c 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EBX (Var (V_TEMP 0xb900))
)

(* 0x0007623d: CALL 0x0004f635 *)
(*     483901: CALL 0x0004f635 *)
| 0x7623d => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x76242 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x00076242: MOV ESI,EAX *)
(*     483906: MOV ESI,EAX *)
| 0x76242 => Some (2,
	Move R_ESI (Var R_EAX)
)

(* 0x00076244: MOVZX EAX,byte ptr [EDI] *)
(*     483908: MOVZX EAX,byte ptr [EDI] *)
| 0x76244 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_EDI) LittleE 1) $;
	Move R_EAX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x00076247: MOV dword ptr [ESP],EAX *)
(*     483911: MOV dword ptr [ESP],EAX *)
| 0x76247 => Some (3,
	Move (V_TEMP 0x5180) (Var R_EAX) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x5180))) LittleE 4)
)

(* 0x0007624a: CALL 0x0004f635 *)
(*     483914: CALL 0x0004f635 *)
| 0x7624a => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x7624f 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x0007624f: ADD ESP,0x10 *)
(*     483919: ADD ESP,0x10 *)
| 0x7624f => Some (3,
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

(* 0x00076252: MOV EDX,EAX *)
(*     483922: MOV EDX,EAX *)
| 0x76252 => Some (2,
	Move R_EDX (Var R_EAX)
)

(* 0x00076254: MOV EAX,ESI *)
(*     483924: MOV EAX,ESI *)
| 0x76254 => Some (2,
	Move R_EAX (Var R_ESI)
)

(* 0x00076256: SUB EAX,EDX *)
(*     483926: SUB EAX,EDX *)
| 0x76256 => Some (2,
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

(* 0x00076258: ADD ESP,0x1c *)
(*     483928: ADD ESP,0x1c *)
| 0x76258 => Some (3,
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

(* 0x0007625b: POP EBX *)
(*     483931: POP EBX *)
| 0x7625b => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x0007625c: POP ESI *)
(*     483932: POP ESI *)
| 0x7625c => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_ESI (Var (V_TEMP 0x43980))
)

(* 0x0007625d: POP EDI *)
(*     483933: POP EDI *)
| 0x7625d => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EDI (Var (V_TEMP 0x43980))
)

(* 0x0007625e: POP EBP *)
(*     483934: POP EBP *)
| 0x7625e => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBP (Var (V_TEMP 0x43980))
)

(* 0x0007625f: RET *)
(*     483935: RET *)
| 0x7625f => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx strncasecmp_i386.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: stpcpy
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition stpcpy_i386 : program := fun _ a => match a with

(* 0x0003f380: PUSH ESI *)
(*     258944: PUSH ESI *)
| 0x3f380 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_ESI) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0003f381: PUSH EBX *)
(*     258945: PUSH EBX *)
| 0x3f381 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0003f382: MOV EDX,dword ptr [ESP + 0x10] *)
(*     258946: MOV EDX,dword ptr [ESP + 0x10] *)
| 0x3f382 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x10 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDX (Var (V_TEMP 0xb900))
)

(* 0x0003f386: MOV EAX,dword ptr [ESP + 0xc] *)
(*     258950: MOV EAX,dword ptr [ESP + 0xc] *)
| 0x3f386 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0xc 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x0003f38a: MOV ECX,EDX *)
(*     258954: MOV ECX,EDX *)
| 0x3f38a => Some (2,
	Move R_ECX (Var R_EDX)
)

(* 0x0003f38c: XOR ECX,EAX *)
(*     258956: XOR ECX,EAX *)
| 0x3f38c => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_ECX (BinOp OP_XOR (Var R_ECX) (Var R_EAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ECX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ECX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ECX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f38e: AND ECX,0x3 *)
(*     258958: AND ECX,0x3 *)
| 0x3f38e => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_ECX (BinOp OP_AND (Var R_ECX) (Word 0x3 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ECX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ECX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ECX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f391: JNZ 0x0003f3e6 *)
(*     258961: JNZ 0x0003f3e6 *)
| 0x3f391 => Some (2,
	Move (V_TEMP 0xbe00) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbe00))) (
		Jmp (Word 0x3f3e6 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003f393: TEST DL,0x3 *)
(*     258963: TEST DL,0x3 *)
| 0x3f393 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x56d00) (BinOp OP_AND (Extract 7 0 (Var R_EDX)) (Word 0x3 8)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x56d00)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x56d00)) (Word 0x0 8))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x56d00)) (Word 0xff 8)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f396: JZ 0x0003f3c8 *)
(*     258966: JZ 0x0003f3c8 *)
| 0x3f396 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x3f3c8 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003f398: MOVZX ECX,byte ptr [EDX] *)
(*     258968: MOVZX ECX,byte ptr [EDX] *)
| 0x3f398 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_EDX) LittleE 1) $;
	Move R_ECX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x0003f39b: MOV byte ptr [EAX],CL *)
(*     258971: MOV byte ptr [EAX],CL *)
| 0x3f39b => Some (2,
	Move (V_TEMP 0x5080) (Extract 7 0 (Var R_ECX)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_EAX) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x5080))) LittleE 1)
)

(* 0x0003f39d: TEST CL,CL *)
(*     258973: TEST CL,CL *)
| 0x3f39d => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x57000) (BinOp OP_AND (Extract 7 0 (Var R_ECX)) (Extract 7 0 (Var R_ECX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x57000)) (Word 0xff 8)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f39f: JZ 0x0003f3ef *)
(*     258975: JZ 0x0003f3ef *)
| 0x3f39f => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x3f3ef 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003f3a1: ADD EDX,0x1 *)
(*     258977: ADD EDX,0x1 *)
| 0x3f3a1 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EDX) (Word 0x1 32)) (Var R_EDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EDX) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EDX (BinOp OP_PLUS (Var R_EDX) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3a4: ADD EAX,0x1 *)
(*     258980: ADD EAX,0x1 *)
| 0x3f3a4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EAX) (Word 0x1 32)) (Var R_EAX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EAX) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_PLUS (Var R_EAX) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3a7: JMP 0x0003f393 *)
(*     258983: JMP 0x0003f393 *)
| 0x3f3a7 => Some (2,
	Jmp (Word 0x3f393 32)
)

(* 0x0003f3c0: MOV dword ptr [EAX],EBX *)
(*     259008: MOV dword ptr [EAX],EBX *)
| 0x3f3c0 => Some (2,
	Move (V_TEMP 0x5180) (Var R_EBX) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_EAX) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x5180))) LittleE 4)
)

(* 0x0003f3c2: ADD EAX,0x4 *)
(*     259010: ADD EAX,0x4 *)
| 0x3f3c2 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EAX) (Word 0x4 32)) (Var R_EAX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EAX) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_PLUS (Var R_EAX) (Word 0x4 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3c5: ADD EDX,0x4 *)
(*     259013: ADD EDX,0x4 *)
| 0x3f3c5 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EDX) (Word 0x4 32)) (Var R_EDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EDX) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EDX (BinOp OP_PLUS (Var R_EDX) (Word 0x4 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3c8: MOV EBX,dword ptr [EDX] *)
(*     259016: MOV EBX,dword ptr [EDX] *)
| 0x3f3c8 => Some (2,
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var R_EDX) LittleE 4) $;
	Move R_EBX (Var (V_TEMP 0xb900))
)

(* 0x0003f3ca: MOV ESI,EBX *)
(*     259018: MOV ESI,EBX *)
| 0x3f3ca => Some (2,
	Move R_ESI (Var R_EBX)
)

(* 0x0003f3cc: LEA ECX,[EBX + 0xfefefeff] *)
(*     259020: LEA ECX,[EBX + 0xfefefeff] *)
| 0x3f3cc => Some (6,
	Move (V_TEMP 0x3400) (BinOp OP_PLUS (Var R_EBX) (Word 0xfefefeff 32)) $;
	Move R_ECX (Var (V_TEMP 0x3400))
)

(* 0x0003f3d2: NOT ESI *)
(*     259026: NOT ESI *)
| 0x3f3d2 => Some (2,
	Move R_ESI (UnOp OP_NOT (Var R_ESI))
)

(* 0x0003f3d4: AND ECX,ESI *)
(*     259028: AND ECX,ESI *)
| 0x3f3d4 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_ECX (BinOp OP_AND (Var R_ECX) (Var R_ESI)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ECX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ECX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ECX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3d6: AND ECX,0x80808080 *)
(*     259030: AND ECX,0x80808080 *)
| 0x3f3d6 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_ECX (BinOp OP_AND (Var R_ECX) (Word 0x80808080 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ECX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ECX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ECX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3dc: JZ 0x0003f3c0 *)
(*     259036: JZ 0x0003f3c0 *)
| 0x3f3dc => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x3f3c0 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003f3de: JMP 0x0003f3e6 *)
(*     259038: JMP 0x0003f3e6 *)
| 0x3f3de => Some (2,
	Jmp (Word 0x3f3e6 32)
)

(* 0x0003f3e0: ADD EDX,0x1 *)
(*     259040: ADD EDX,0x1 *)
| 0x3f3e0 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EDX) (Word 0x1 32)) (Var R_EDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EDX) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EDX (BinOp OP_PLUS (Var R_EDX) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3e3: ADD EAX,0x1 *)
(*     259043: ADD EAX,0x1 *)
| 0x3f3e3 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EAX) (Word 0x1 32)) (Var R_EAX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EAX) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_PLUS (Var R_EAX) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3e6: MOVZX ECX,byte ptr [EDX] *)
(*     259046: MOVZX ECX,byte ptr [EDX] *)
| 0x3f3e6 => Some (3,
	Move (V_TEMP 0xb800) (Load (Var V_MEM32) (Var R_EDX) LittleE 1) $;
	Move R_ECX (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xb800)))
)

(* 0x0003f3e9: MOV byte ptr [EAX],CL *)
(*     259049: MOV byte ptr [EAX],CL *)
| 0x3f3e9 => Some (2,
	Move (V_TEMP 0x5080) (Extract 7 0 (Var R_ECX)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_EAX) (Cast CAST_UNSIGNED 8 (Var (V_TEMP 0x5080))) LittleE 1)
)

(* 0x0003f3eb: TEST CL,CL *)
(*     259051: TEST CL,CL *)
| 0x3f3eb => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x57000) (BinOp OP_AND (Extract 7 0 (Var R_ECX)) (Extract 7 0 (Var R_ECX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x57000)) (Word 0x0 8))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x57000)) (Word 0xff 8)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f3ed: JNZ 0x0003f3e0 *)
(*     259053: JNZ 0x0003f3e0 *)
| 0x3f3ed => Some (2,
	Move (V_TEMP 0xbe00) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbe00))) (
		Jmp (Word 0x3f3e0 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003f3ef: POP EBX *)
(*     259055: POP EBX *)
| 0x3f3ef => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x0003f3f0: POP ESI *)
(*     259056: POP ESI *)
| 0x3f3f0 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_ESI (Var (V_TEMP 0x43980))
)

(* 0x0003f3f1: RET *)
(*     259057: RET *)
| 0x3f3f1 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx stpcpy_i386.
Proof. Picinae_typecheck. Qed.

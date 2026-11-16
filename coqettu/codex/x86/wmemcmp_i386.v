(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: wmemcmp
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wmemcmp_i386 : program := fun _ a => match a with

(* 0x0003fc60: PUSH EBX *)
(*     261216: PUSH EBX *)
| 0x3fc60 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0003fc61: MOV ECX,dword ptr [ESP + 0x8] *)
(*     261217: MOV ECX,dword ptr [ESP + 0x8] *)
| 0x3fc61 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x8 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_ECX (Var (V_TEMP 0xb900))
)

(* 0x0003fc65: MOV EDX,dword ptr [ESP + 0xc] *)
(*     261221: MOV EDX,dword ptr [ESP + 0xc] *)
| 0x3fc65 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0xc 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDX (Var (V_TEMP 0xb900))
)

(* 0x0003fc69: MOV EAX,dword ptr [ESP + 0x10] *)
(*     261225: MOV EAX,dword ptr [ESP + 0x10] *)
| 0x3fc69 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x10 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x0003fc6d: JMP 0x0003fc89 *)
(*     261229: JMP 0x0003fc89 *)
| 0x3fc6d => Some (2,
	Jmp (Word 0x3fc89 32)
)

(* 0x0003fc80: SUB EAX,0x1 *)
(*     261248: SUB EAX,0x1 *)
| 0x3fc80 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EAX) (Word 0x1 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_MINUS (Var R_EAX) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003fc83: ADD ECX,0x4 *)
(*     261251: ADD ECX,0x4 *)
| 0x3fc83 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_ECX) (Word 0x4 32)) (Var R_ECX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_ECX) (Word 0x4 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ECX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ECX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x4 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ECX (BinOp OP_PLUS (Var R_ECX) (Word 0x4 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ECX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ECX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ECX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003fc86: ADD EDX,0x4 *)
(*     261254: ADD EDX,0x4 *)
| 0x3fc86 => Some (3,
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

(* 0x0003fc89: TEST EAX,EAX *)
(*     261257: TEST EAX,EAX *)
| 0x3fc89 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x57200) (BinOp OP_AND (Var R_EAX) (Var R_EAX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x57200)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x57200)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x57200)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003fc8b: JZ 0x0003fca4 *)
(*     261259: JZ 0x0003fca4 *)
| 0x3fc8b => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x3fca4 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003fc8d: MOV EBX,dword ptr [ECX] *)
(*     261261: MOV EBX,dword ptr [ECX] *)
| 0x3fc8d => Some (2,
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var R_ECX) LittleE 4) $;
	Move R_EBX (Var (V_TEMP 0xb900))
)

(* 0x0003fc8f: CMP EBX,dword ptr [EDX] *)
(*     261263: CMP EBX,dword ptr [EDX] *)
| 0x3fc8f => Some (2,
	Move (V_TEMP 0x5180) (Load (Var V_MEM32) (Var R_EDX) LittleE 4) $;
	Move (V_TEMP 0x33b00) (Var (V_TEMP 0x5180)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EBX) (Var (V_TEMP 0x33b00)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EBX) (Var (V_TEMP 0x33b00))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EBX) (Var (V_TEMP 0x33b00))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33b00)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33c00) (BinOp OP_MINUS (Var R_EBX) (Var (V_TEMP 0x33b00))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33c00)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33c00)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33c00)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003fc91: JZ 0x0003fc80 *)
(*     261265: JZ 0x0003fc80 *)
| 0x3fc91 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x3fc80 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003fc93: MOV EAX,0xffffffff *)
(*     261267: MOV EAX,0xffffffff *)
| 0x3fc93 => Some (5,
	Move R_EAX (Word 0xffffffff 32)
)

(* 0x0003fc98: CMP EBX,dword ptr [EDX] *)
(*     261272: CMP EBX,dword ptr [EDX] *)
| 0x3fc98 => Some (2,
	Move (V_TEMP 0x5180) (Load (Var V_MEM32) (Var R_EDX) LittleE 4) $;
	Move (V_TEMP 0x33b00) (Var (V_TEMP 0x5180)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EBX) (Var (V_TEMP 0x33b00)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EBX) (Var (V_TEMP 0x33b00))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EBX) (Var (V_TEMP 0x33b00))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33b00)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33c00) (BinOp OP_MINUS (Var R_EBX) (Var (V_TEMP 0x33b00))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33c00)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33c00)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33c00)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003fc9a: JL 0x0003fca6 *)
(*     261274: JL 0x0003fca6 *)
| 0x3fc9a => Some (2,
	Move (V_TEMP 0xc380) (BinOp OP_NEQ (Var R_OF) (Var R_SF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xc380))) (
		Jmp (Word 0x3fca6 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003fc9c: SETG AL *)
(*     261276: SETG AL *)
| 0x3fc9c => Some (3,
	Move (V_TEMP 0xc680) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0xc700) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	Move (V_TEMP 0xc800) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xc680)) (Var (V_TEMP 0xc700)))) $;
	Move R_EAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc800))) (Word 0 32)) (BinOp OP_AND (Var R_EAX) (Word 0xFFFFFF00 32)))
)

(* 0x0003fc9f: MOVZX EAX,AL *)
(*     261279: MOVZX EAX,AL *)
| 0x3fc9f => Some (3,
	Move R_EAX (Cast CAST_UNSIGNED 32 (Extract 7 0 (Var R_EAX)))
)

(* 0x0003fca2: JMP 0x0003fca6 *)
(*     261282: JMP 0x0003fca6 *)
| 0x3fca2 => Some (2,
	Jmp (Word 0x3fca6 32)
)

(* 0x0003fca4: XOR EAX,EAX *)
(*     261284: XOR EAX,EAX *)
| 0x3fca4 => Some (2,
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

(* 0x0003fca6: POP EBX *)
(*     261286: POP EBX *)
| 0x3fca6 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x0003fca7: RET *)
(*     261287: RET *)
| 0x3fca7 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx wmemcmp_i386.
Proof. Picinae_typecheck. Qed.

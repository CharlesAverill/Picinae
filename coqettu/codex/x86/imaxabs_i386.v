(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: imaxabs
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition imaxabs_i386 : program := fun _ a => match a with

(* 0x00075208: PUSH EBX *)
(*     479752: PUSH EBX *)
| 0x75208 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00075209: MOV EDX,dword ptr [ESP + 0xc] *)
(*     479753: MOV EDX,dword ptr [ESP + 0xc] *)
| 0x75209 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0xc 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDX (Var (V_TEMP 0xb900))
)

(* 0x0007520d: MOV EAX,dword ptr [ESP + 0x8] *)
(*     479757: MOV EAX,dword ptr [ESP + 0x8] *)
| 0x7520d => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x8 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x00075211: MOV EBX,EDX *)
(*     479761: MOV EBX,EDX *)
| 0x75211 => Some (2,
	Move R_EBX (Var R_EDX)
)

(* 0x00075213: SAR EBX,0x1f *)
(*     479763: SAR EBX,0x1f *)
| 0x75213 => Some (3,
	Move (V_TEMP 0x51a80) (BinOp OP_AND (Word 0x1f 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x51b00) (Var R_EBX) $;
	Move R_EBX (BinOp OP_ARSHIFT (Var R_EBX) (Var (V_TEMP 0x51a80))) $;
	Move (V_TEMP 0x27980) (BinOp OP_NEQ (Var (V_TEMP 0x51a80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x27a00) (BinOp OP_MINUS (Var (V_TEMP 0x51a80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x27a80) (BinOp OP_ARSHIFT (Var (V_TEMP 0x51b00)) (Var (V_TEMP 0x27a00))) $;
	Move (V_TEMP 0x27b00) (BinOp OP_AND (Var (V_TEMP 0x27a80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x27c00) (BinOp OP_NEQ (Var (V_TEMP 0x27b00)) (Word 0x0 32)) $;
	Move (V_TEMP 0x27c80) (UnOp OP_NOT (Var (V_TEMP 0x27980))) $;
	Move (V_TEMP 0x27d00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x27c80)) (Var R_CF))) $;
	Move (V_TEMP 0x27d80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x27980)) (Var (V_TEMP 0x27c00)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x27d00))) (Cast CAST_LOW 1 (Var (V_TEMP 0x27d80)))))) $;
	Move (V_TEMP 0x27f00) (BinOp OP_EQ (Var (V_TEMP 0x51a80)) (Word 0x1 32)) $;
	Move (V_TEMP 0x27f80) (UnOp OP_NOT (Var (V_TEMP 0x27f00))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x27f80)) (Var R_OF)))) $;
	Move (V_TEMP 0x24e80) (BinOp OP_NEQ (Var (V_TEMP 0x51a80)) (Word 0x0 32)) $;
	Move (V_TEMP 0x24f80) (BinOp OP_SLT (Var R_EBX) (Word 0x0 32)) $;
	Move (V_TEMP 0x25000) (UnOp OP_NOT (Var (V_TEMP 0x24e80))) $;
	Move (V_TEMP 0x25080) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x25000)) (Var R_SF))) $;
	Move (V_TEMP 0x25100) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x24e80)) (Var (V_TEMP 0x24f80)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x25080))) (Cast CAST_LOW 1 (Var (V_TEMP 0x25100)))))) $;
	Move (V_TEMP 0x25280) (BinOp OP_EQ (Var R_EBX) (Word 0x0 32)) $;
	Move (V_TEMP 0x25300) (UnOp OP_NOT (Var (V_TEMP 0x24e80))) $;
	Move (V_TEMP 0x25380) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x25300)) (Var R_ZF))) $;
	Move (V_TEMP 0x25400) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x24e80)) (Var (V_TEMP 0x25280)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x25380))) (Cast CAST_LOW 1 (Var (V_TEMP 0x25400)))))) $;
	Move (V_TEMP 0x25500) (BinOp OP_AND (Var R_EBX) (Word 0xff 32)) $;
	Move (V_TEMP 0x25580) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x25500)))) $;
	Move (V_TEMP 0x25600) (BinOp OP_AND (Var (V_TEMP 0x25580)) (Word 0x1 8)) $;
	Move (V_TEMP 0x25700) (BinOp OP_EQ (Var (V_TEMP 0x25600)) (Word 0x0 8)) $;
	Move (V_TEMP 0x25780) (UnOp OP_NOT (Var (V_TEMP 0x24e80))) $;
	Move (V_TEMP 0x25800) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x25780)) (Var R_PF))) $;
	Move (V_TEMP 0x25880) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x24e80)) (Var (V_TEMP 0x25700)))) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x25800))) (Cast CAST_LOW 1 (Var (V_TEMP 0x25880))))))
)

(* 0x00075216: MOV ECX,EBX *)
(*     479766: MOV ECX,EBX *)
| 0x75216 => Some (2,
	Move R_ECX (Var R_EBX)
)

(* 0x00075218: XOR EDX,EBX *)
(*     479768: XOR EDX,EBX *)
| 0x75218 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_EDX (BinOp OP_XOR (Var R_EDX) (Var R_EBX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0007521a: XOR EAX,ECX *)
(*     479770: XOR EAX,ECX *)
| 0x7521a => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_EAX (BinOp OP_XOR (Var R_EAX) (Var R_ECX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0007521c: SUB EAX,ECX *)
(*     479772: SUB EAX,ECX *)
| 0x7521c => Some (2,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EAX) (Var R_ECX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Var R_ECX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Var R_ECX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ECX) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_MINUS (Var R_EAX) (Var R_ECX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0007521e: SBB EDX,EBX *)
(*     479774: SBB EDX,EBX *)
| 0x7521e => Some (2,
	Move (V_TEMP 0x24600) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EDX) (Var R_EBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EDX) (Var R_EBX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EDX) (Var R_EBX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x24800) (BinOp OP_MINUS (Var R_EDX) (Var R_EBX)) $;
	Move (V_TEMP 0x24880) (BinOp OP_LT (Var (V_TEMP 0x24800)) (Var (V_TEMP 0x24600))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var (V_TEMP 0x24880))))) $;
	Move (V_TEMP 0x24980) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x24800)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x24800)) (Var (V_TEMP 0x24600))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x24800)) (Var (V_TEMP 0x24600))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x24600)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Var R_OF) (Cast CAST_LOW 1 (Var (V_TEMP 0x24980)))))) $;
	Move R_EDX (BinOp OP_MINUS (Var (V_TEMP 0x24800)) (Var (V_TEMP 0x24600))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00075220: POP EBX *)
(*     479776: POP EBX *)
| 0x75220 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x00075221: RET *)
(*     479777: RET *)
| 0x75221 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx imaxabs_i386.
Proof. Picinae_typecheck. Qed.

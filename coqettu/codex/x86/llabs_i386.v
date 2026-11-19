(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: llabs
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition llabs_i386 : program := fun _ a => match a with

(* 0x00075291: PUSH EBX *)
(*     479889: PUSH EBX *)
| 0x75291 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00075292: MOV EDX,dword ptr [ESP + 0xc] *)
(*     479890: MOV EDX,dword ptr [ESP + 0xc] *)
| 0x75292 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0xc 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDX (Var (V_TEMP 0xb900))
)

(* 0x00075296: MOV EAX,dword ptr [ESP + 0x8] *)
(*     479894: MOV EAX,dword ptr [ESP + 0x8] *)
| 0x75296 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x8 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x0007529a: MOV EBX,EDX *)
(*     479898: MOV EBX,EDX *)
| 0x7529a => Some (2,
	Move R_EBX (Var R_EDX)
)

(* 0x0007529c: SAR EBX,0x1f *)
(*     479900: SAR EBX,0x1f *)
| 0x7529c => Some (3,
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

(* 0x0007529f: MOV ECX,EBX *)
(*     479903: MOV ECX,EBX *)
| 0x7529f => Some (2,
	Move R_ECX (Var R_EBX)
)

(* 0x000752a1: XOR EDX,EBX *)
(*     479905: XOR EDX,EBX *)
| 0x752a1 => Some (2,
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

(* 0x000752a3: XOR EAX,ECX *)
(*     479907: XOR EAX,ECX *)
| 0x752a3 => Some (2,
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

(* 0x000752a5: SUB EAX,ECX *)
(*     479909: SUB EAX,ECX *)
| 0x752a5 => Some (2,
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

(* 0x000752a7: SBB EDX,EBX *)
(*     479911: SBB EDX,EBX *)
| 0x752a7 => Some (2,
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

(* 0x000752a9: POP EBX *)
(*     479913: POP EBX *)
| 0x752a9 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x000752aa: RET *)
(*     479914: RET *)
| 0x752aa => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx llabs_i386.
Proof. Picinae_typecheck. Qed.

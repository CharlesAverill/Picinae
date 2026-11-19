(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: wcslen
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcslen_i386 : program := fun _ a => match a with

(* 0x00047c10: MOV EDX,dword ptr [ESP + 0x4] *)
(*     293904: MOV EDX,dword ptr [ESP + 0x4] *)
| 0x47c10 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x4 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDX (Var (V_TEMP 0xb900))
)

(* 0x00047c14: MOV EAX,EDX *)
(*     293908: MOV EAX,EDX *)
| 0x47c14 => Some (2,
	Move R_EAX (Var R_EDX)
)

(* 0x00047c16: JMP 0x00047c23 *)
(*     293910: JMP 0x00047c23 *)
| 0x47c16 => Some (2,
	Jmp (Word 0x47c23 32)
)

(* 0x00047c20: ADD EAX,0x4 *)
(*     293920: ADD EAX,0x4 *)
| 0x47c20 => Some (3,
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

(* 0x00047c23: MOV ECX,dword ptr [EAX] *)
(*     293923: MOV ECX,dword ptr [EAX] *)
| 0x47c23 => Some (2,
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var R_EAX) LittleE 4) $;
	Move R_ECX (Var (V_TEMP 0xb900))
)

(* 0x00047c25: TEST ECX,ECX *)
(*     293925: TEST ECX,ECX *)
| 0x47c25 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x57200) (BinOp OP_AND (Var R_ECX) (Var R_ECX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x57200)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x57200)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x57200)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00047c27: JNZ 0x00047c20 *)
(*     293927: JNZ 0x00047c20 *)
| 0x47c27 => Some (2,
	Move (V_TEMP 0xbe00) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbe00))) (
		Jmp (Word 0x47c20 32)
	) (* else *) (
		Nop
	)
)

(* 0x00047c29: SUB EAX,EDX *)
(*     293929: SUB EAX,EDX *)
| 0x47c29 => Some (2,
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

(* 0x00047c2b: SAR EAX,0x2 *)
(*     293931: SAR EAX,0x2 *)
| 0x47c2b => Some (3,
	Move (V_TEMP 0x51a80) (BinOp OP_AND (Word 0x2 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x51b00) (Var R_EAX) $;
	Move R_EAX (BinOp OP_ARSHIFT (Var R_EAX) (Var (V_TEMP 0x51a80))) $;
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
	Move (V_TEMP 0x24f80) (BinOp OP_SLT (Var R_EAX) (Word 0x0 32)) $;
	Move (V_TEMP 0x25000) (UnOp OP_NOT (Var (V_TEMP 0x24e80))) $;
	Move (V_TEMP 0x25080) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x25000)) (Var R_SF))) $;
	Move (V_TEMP 0x25100) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x24e80)) (Var (V_TEMP 0x24f80)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x25080))) (Cast CAST_LOW 1 (Var (V_TEMP 0x25100)))))) $;
	Move (V_TEMP 0x25280) (BinOp OP_EQ (Var R_EAX) (Word 0x0 32)) $;
	Move (V_TEMP 0x25300) (UnOp OP_NOT (Var (V_TEMP 0x24e80))) $;
	Move (V_TEMP 0x25380) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x25300)) (Var R_ZF))) $;
	Move (V_TEMP 0x25400) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x24e80)) (Var (V_TEMP 0x25280)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x25380))) (Cast CAST_LOW 1 (Var (V_TEMP 0x25400)))))) $;
	Move (V_TEMP 0x25500) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x25580) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x25500)))) $;
	Move (V_TEMP 0x25600) (BinOp OP_AND (Var (V_TEMP 0x25580)) (Word 0x1 8)) $;
	Move (V_TEMP 0x25700) (BinOp OP_EQ (Var (V_TEMP 0x25600)) (Word 0x0 8)) $;
	Move (V_TEMP 0x25780) (UnOp OP_NOT (Var (V_TEMP 0x24e80))) $;
	Move (V_TEMP 0x25800) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x25780)) (Var R_PF))) $;
	Move (V_TEMP 0x25880) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x24e80)) (Var (V_TEMP 0x25700)))) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x25800))) (Cast CAST_LOW 1 (Var (V_TEMP 0x25880))))))
)

(* 0x00047c2e: RET *)
(*     293934: RET *)
| 0x47c2e => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx wcslen_i386.
Proof. Picinae_typecheck. Qed.

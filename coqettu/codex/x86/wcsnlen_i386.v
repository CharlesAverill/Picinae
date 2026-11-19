(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: wcsnlen
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcsnlen_i386 : program := fun _ a => match a with

(* 0x000768a0: PUSH EBX *)
(*     485536: PUSH EBX *)
| 0x768a0 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x000768a1: CALL 0x0004a842 *)
(*     485537: CALL 0x0004a842 *)
| 0x768a1 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x768a6 32)) LittleE 4) $;
	Jmp (Word 0x4a842 32)
)

(* 0x000768a6: ADD EBX,0x3e6f6 *)
(*     485542: ADD EBX,0x3e6f6 *)
| 0x768a6 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EBX) (Word 0x3e6f6 32)) (Var R_EBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EBX) (Word 0x3e6f6 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x3e6f6 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EBX (BinOp OP_PLUS (Var R_EBX) (Word 0x3e6f6 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EBX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EBX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EBX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000768ac: SUB ESP,0xc *)
(*     485548: SUB ESP,0xc *)
| 0x768ac => Some (3,
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

(* 0x000768af: PUSH dword ptr [ESP + 0x18] *)
(*     485551: PUSH dword ptr [ESP + 0x18] *)
| 0x768af => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x18 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move (V_TEMP 0x20a80) (Var (V_TEMP 0xb900)) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x000768b3: PUSH 0x0 *)
(*     485555: PUSH 0x0 *)
| 0x768b3 => Some (2,
	Move (V_TEMP 0x43d80) (Word 0x0 32) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x43d80))) LittleE 4)
)

(* 0x000768b5: PUSH dword ptr [ESP + 0x1c] *)
(*     485557: PUSH dword ptr [ESP + 0x1c] *)
| 0x768b5 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x1c 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move (V_TEMP 0x20a80) (Var (V_TEMP 0xb900)) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x000768b9: CALL 0x00047c80 *)
(*     485561: CALL 0x00047c80 *)
| 0x768b9 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x768be 32)) LittleE 4) $;
	Jmp (Word 0x47c80 32)
)

(* 0x000768be: ADD ESP,0x10 *)
(*     485566: ADD ESP,0x10 *)
| 0x768be => Some (3,
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

(* 0x000768c1: MOV EDX,EAX *)
(*     485569: MOV EDX,EAX *)
| 0x768c1 => Some (2,
	Move R_EDX (Var R_EAX)
)

(* 0x000768c3: MOV EAX,dword ptr [ESP + 0x14] *)
(*     485571: MOV EAX,dword ptr [ESP + 0x14] *)
| 0x768c3 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x14 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x000768c7: TEST EDX,EDX *)
(*     485575: TEST EDX,EDX *)
| 0x768c7 => Some (2,
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

(* 0x000768c9: JZ 0x000768d4 *)
(*     485577: JZ 0x000768d4 *)
| 0x768c9 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x768d4 32)
	) (* else *) (
		Nop
	)
)

(* 0x000768cb: SUB EDX,dword ptr [ESP + 0x10] *)
(*     485579: SUB EDX,dword ptr [ESP + 0x10] *)
| 0x768cb => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x10 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EDX) (Var (V_TEMP 0xb900)))) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EDX) (Var (V_TEMP 0xb900))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EDX) (Var (V_TEMP 0xb900))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xb900)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EDX (BinOp OP_MINUS (Var R_EDX) (Var (V_TEMP 0xb900))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000768cf: MOV EAX,EDX *)
(*     485583: MOV EAX,EDX *)
| 0x768cf => Some (2,
	Move R_EAX (Var R_EDX)
)

(* 0x000768d1: SAR EAX,0x2 *)
(*     485585: SAR EAX,0x2 *)
| 0x768d1 => Some (3,
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

(* 0x000768d4: ADD ESP,0x8 *)
(*     485588: ADD ESP,0x8 *)
| 0x768d4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_ESP) (Word 0x8 32)) (Var R_ESP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_ESP) (Word 0x8 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x8 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x8 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x000768d7: POP EBX *)
(*     485591: POP EBX *)
| 0x768d7 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x000768d8: RET *)
(*     485592: RET *)
| 0x768d8 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx wcsnlen_i386.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: wcscmp
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcscmp_i386 : program := fun _ a => match a with

(* 0x0003f860: PUSH ESI *)
(*     260192: PUSH ESI *)
| 0x3f860 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_ESI) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0003f861: XOR EAX,EAX *)
(*     260193: XOR EAX,EAX *)
| 0x3f861 => Some (2,
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

(* 0x0003f863: PUSH EBX *)
(*     260195: PUSH EBX *)
| 0x3f863 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0003f864: MOV EBX,dword ptr [ESP + 0xc] *)
(*     260196: MOV EBX,dword ptr [ESP + 0xc] *)
| 0x3f864 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0xc 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EBX (Var (V_TEMP 0xb900))
)

(* 0x0003f868: MOV ESI,dword ptr [ESP + 0x10] *)
(*     260200: MOV ESI,dword ptr [ESP + 0x10] *)
| 0x3f868 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x10 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_ESI (Var (V_TEMP 0xb900))
)

(* 0x0003f86c: LEA ESI,[ESI] *)
(*     260204: LEA ESI,[ESI] *)
| 0x3f86c => Some (4,
	Move R_ESI (Var R_ESI)
)

(* 0x0003f870: LEA ESI,[ESI] *)
(*     260208: LEA ESI,[ESI] *)
| 0x3f870 => Some (8,
	Move R_ESI (Var R_ESI)
)

(* 0x0003f878: LEA ESI,[ESI] *)
(*     260216: LEA ESI,[ESI] *)
| 0x3f878 => Some (8,
	Move R_ESI (Var R_ESI)
)

(* 0x0003f880: MOV EDX,dword ptr [EBX + EAX*0x1] *)
(*     260224: MOV EDX,dword ptr [EBX + EAX*0x1] *)
| 0x3f880 => Some (3,
	Move (V_TEMP 0x3500) (BinOp OP_TIMES (Var R_EAX) (Word 0x1 32)) $;
	Move (V_TEMP 0x3600) (BinOp OP_PLUS (Var R_EBX) (Var (V_TEMP 0x3500))) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3600)) LittleE 4) $;
	Move R_EDX (Var (V_TEMP 0xb900))
)

(* 0x0003f883: MOV ECX,dword ptr [ESI + EAX*0x1] *)
(*     260227: MOV ECX,dword ptr [ESI + EAX*0x1] *)
| 0x3f883 => Some (3,
	Move (V_TEMP 0x3500) (BinOp OP_TIMES (Var R_EAX) (Word 0x1 32)) $;
	Move (V_TEMP 0x3600) (BinOp OP_PLUS (Var R_ESI) (Var (V_TEMP 0x3500))) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3600)) LittleE 4) $;
	Move R_ECX (Var (V_TEMP 0xb900))
)

(* 0x0003f886: CMP EDX,ECX *)
(*     260230: CMP EDX,ECX *)
| 0x3f886 => Some (2,
	Move (V_TEMP 0x33500) (Var R_EDX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33500)) (Var R_ECX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33500)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_ECX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_ECX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ECX) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33600) (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_ECX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33600)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33600)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33600)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f888: JNZ 0x0003f891 *)
(*     260232: JNZ 0x0003f891 *)
| 0x3f888 => Some (2,
	Move (V_TEMP 0xbe00) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbe00))) (
		Jmp (Word 0x3f891 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003f88a: ADD EAX,0x4 *)
(*     260234: ADD EAX,0x4 *)
| 0x3f88a => Some (3,
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

(* 0x0003f88d: TEST EDX,EDX *)
(*     260237: TEST EDX,EDX *)
| 0x3f88d => Some (2,
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

(* 0x0003f88f: JNZ 0x0003f880 *)
(*     260239: JNZ 0x0003f880 *)
| 0x3f88f => Some (2,
	Move (V_TEMP 0xbe00) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbe00))) (
		Jmp (Word 0x3f880 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003f891: MOV EAX,0xffffffff *)
(*     260241: MOV EAX,0xffffffff *)
| 0x3f891 => Some (5,
	Move R_EAX (Word 0xffffffff 32)
)

(* 0x0003f896: CMP ECX,EDX *)
(*     260246: CMP ECX,EDX *)
| 0x3f896 => Some (2,
	Move (V_TEMP 0x33500) (Var R_ECX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33500)) (Var R_EDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33500)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EDX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EDX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33600) (BinOp OP_MINUS (Var (V_TEMP 0x33500)) (Var R_EDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33600)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33600)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33600)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0003f898: JG 0x0003f8a0 *)
(*     260248: JG 0x0003f8a0 *)
| 0x3f898 => Some (2,
	Move (V_TEMP 0xc680) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0xc700) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	Move (V_TEMP 0xc800) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xc680)) (Var (V_TEMP 0xc700)))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xc800))) (
		Jmp (Word 0x3f8a0 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003f89a: SETL AL *)
(*     260250: SETL AL *)
| 0x3f89a => Some (3,
	Move (V_TEMP 0xc380) (BinOp OP_NEQ (Var R_OF) (Var R_SF)) $;
	Move R_EAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xc380))) (Word 0 32)) (BinOp OP_AND (Var R_EAX) (Word 0xFFFFFF00 32)))
)

(* 0x0003f89d: MOVZX EAX,AL *)
(*     260253: MOVZX EAX,AL *)
| 0x3f89d => Some (3,
	Move R_EAX (Cast CAST_UNSIGNED 32 (Extract 7 0 (Var R_EAX)))
)

(* 0x0003f8a0: POP EBX *)
(*     260256: POP EBX *)
| 0x3f8a0 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x0003f8a1: POP ESI *)
(*     260257: POP ESI *)
| 0x3f8a1 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_ESI (Var (V_TEMP 0x43980))
)

(* 0x0003f8a2: RET *)
(*     260258: RET *)
| 0x3f8a2 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx wcscmp_i386.
Proof. Picinae_typecheck. Qed.

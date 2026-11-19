(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: iswcntrl
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition iswcntrl_i386 : program := fun _ a => match a with

(* 0x0004f1b8: MOV EAX,dword ptr [ESP + 0x4] *)
(*     324024: MOV EAX,dword ptr [ESP + 0x4] *)
| 0x4f1b8 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x4 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x0004f1bc: LEA EDX,[EAX + -0x7f] *)
(*     324028: LEA EDX,[EAX + -0x7f] *)
| 0x4f1bc => Some (3,
	Move (V_TEMP 0x3300) (BinOp OP_PLUS (Var R_EAX) (Word 0xffffff81 32)) $;
	Move R_EDX (Var (V_TEMP 0x3300))
)

(* 0x0004f1bf: CMP EDX,0x20 *)
(*     324031: CMP EDX,0x20 *)
| 0x4f1bf => Some (3,
	Move (V_TEMP 0x33080) (Var R_EDX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33080)) (Word 0x20 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33080)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x20 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33180) (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x20 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f1c2: JBE 0x0004f1e8 *)
(*     324034: JBE 0x0004f1e8 *)
| 0x4f1c2 => Some (2,
	Move (V_TEMP 0xbf00) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbf00))) (
		Jmp (Word 0x4f1e8 32)
	) (* else *) (
		Nop
	)
)

(* 0x0004f1c4: CMP EAX,0x1f *)
(*     324036: CMP EAX,0x1f *)
| 0x4f1c4 => Some (3,
	Move (V_TEMP 0x33080) (Var R_EAX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33080)) (Word 0x1f 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33080)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x1f 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x1f 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1f 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33180) (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x1f 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f1c7: JBE 0x0004f1e8 *)
(*     324039: JBE 0x0004f1e8 *)
| 0x4f1c7 => Some (2,
	Move (V_TEMP 0xbf00) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbf00))) (
		Jmp (Word 0x4f1e8 32)
	) (* else *) (
		Nop
	)
)

(* 0x0004f1c9: LEA ECX,[EAX + 0xffffdfd8] *)
(*     324041: LEA ECX,[EAX + 0xffffdfd8] *)
| 0x4f1c9 => Some (6,
	Move (V_TEMP 0x3400) (BinOp OP_PLUS (Var R_EAX) (Word 0xffffdfd8 32)) $;
	Move R_ECX (Var (V_TEMP 0x3400))
)

(* 0x0004f1cf: MOV EDX,0x1 *)
(*     324047: MOV EDX,0x1 *)
| 0x4f1cf => Some (5,
	Move R_EDX (Word 0x1 32)
)

(* 0x0004f1d4: CMP ECX,0x1 *)
(*     324052: CMP ECX,0x1 *)
| 0x4f1d4 => Some (3,
	Move (V_TEMP 0x33080) (Var R_ECX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33080)) (Word 0x1 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33080)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33180) (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x1 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f1d7: JBE 0x0004f1ed *)
(*     324055: JBE 0x0004f1ed *)
| 0x4f1d7 => Some (2,
	Move (V_TEMP 0xbf00) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbf00))) (
		Jmp (Word 0x4f1ed 32)
	) (* else *) (
		Nop
	)
)

(* 0x0004f1d9: SUB EAX,0xfff9 *)
(*     324057: SUB EAX,0xfff9 *)
| 0x4f1d9 => Some (5,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EAX) (Word 0xfff9 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Word 0xfff9 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Word 0xfff9 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xfff9 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_MINUS (Var R_EAX) (Word 0xfff9 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f1de: XOR EDX,EDX *)
(*     324062: XOR EDX,EDX *)
| 0x4f1de => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_EDX (BinOp OP_XOR (Var R_EDX) (Var R_EDX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f1e0: CMP EAX,0x2 *)
(*     324064: CMP EAX,0x2 *)
| 0x4f1e0 => Some (3,
	Move (V_TEMP 0x33080) (Var R_EAX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33080)) (Word 0x2 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33080)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x2 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x2 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x2 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33180) (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x2 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f1e3: SETBE DL *)
(*     324067: SETBE DL *)
| 0x4f1e3 => Some (3,
	Move (V_TEMP 0xbf00) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	Move R_EDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbf00))) (Word 0 32)) (BinOp OP_AND (Var R_EDX) (Word 0xFFFFFF00 32)))
)

(* 0x0004f1e6: JMP 0x0004f1ed *)
(*     324070: JMP 0x0004f1ed *)
| 0x4f1e6 => Some (2,
	Jmp (Word 0x4f1ed 32)
)

(* 0x0004f1e8: MOV EDX,0x1 *)
(*     324072: MOV EDX,0x1 *)
| 0x4f1e8 => Some (5,
	Move R_EDX (Word 0x1 32)
)

(* 0x0004f1ed: MOV EAX,EDX *)
(*     324077: MOV EAX,EDX *)
| 0x4f1ed => Some (2,
	Move R_EAX (Var R_EDX)
)

(* 0x0004f1ef: RET *)
(*     324079: RET *)
| 0x4f1ef => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx iswcntrl_i386.
Proof. Picinae_typecheck. Qed.

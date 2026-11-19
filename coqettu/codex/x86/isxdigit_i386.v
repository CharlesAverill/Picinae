(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: isxdigit
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition isxdigit_i386 : program := fun _ a => match a with

(* 0x0004f5ee: MOV EAX,dword ptr [ESP + 0x4] *)
(*     325102: MOV EAX,dword ptr [ESP + 0x4] *)
| 0x4f5ee => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x4 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x0004f5f2: MOV EDX,0x1 *)
(*     325106: MOV EDX,0x1 *)
| 0x4f5f2 => Some (5,
	Move R_EDX (Word 0x1 32)
)

(* 0x0004f5f7: LEA ECX,[EAX + -0x30] *)
(*     325111: LEA ECX,[EAX + -0x30] *)
| 0x4f5f7 => Some (3,
	Move (V_TEMP 0x3300) (BinOp OP_PLUS (Var R_EAX) (Word 0xffffffd0 32)) $;
	Move R_ECX (Var (V_TEMP 0x3300))
)

(* 0x0004f5fa: CMP ECX,0x9 *)
(*     325114: CMP ECX,0x9 *)
| 0x4f5fa => Some (3,
	Move (V_TEMP 0x33080) (Var R_ECX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33080)) (Word 0x9 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33080)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x9 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x9 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x9 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33180) (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x9 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f5fd: JBE 0x0004f60d *)
(*     325117: JBE 0x0004f60d *)
| 0x4f5fd => Some (2,
	Move (V_TEMP 0xbf00) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbf00))) (
		Jmp (Word 0x4f60d 32)
	) (* else *) (
		Nop
	)
)

(* 0x0004f5ff: OR EAX,0x20 *)
(*     325119: OR EAX,0x20 *)
| 0x4f5ff => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_EAX (BinOp OP_OR (Var R_EAX) (Word 0x20 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f602: XOR EDX,EDX *)
(*     325122: XOR EDX,EDX *)
| 0x4f602 => Some (2,
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

(* 0x0004f604: SUB EAX,0x61 *)
(*     325124: SUB EAX,0x61 *)
| 0x4f604 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_EAX) (Word 0x61 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EAX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Word 0x61 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_EAX) (Word 0x61 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x61 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EAX (BinOp OP_MINUS (Var R_EAX) (Word 0x61 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f607: CMP EAX,0x5 *)
(*     325127: CMP EAX,0x5 *)
| 0x4f607 => Some (3,
	Move (V_TEMP 0x33080) (Var R_EAX) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x33080)) (Word 0x5 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x33080)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x5 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x5 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x5 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x33180) (BinOp OP_MINUS (Var (V_TEMP 0x33080)) (Word 0x5 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x33180)) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var (V_TEMP 0x33180)) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f60a: SETBE DL *)
(*     325130: SETBE DL *)
| 0x4f60a => Some (3,
	Move (V_TEMP 0xbf00) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))) $;
	Move R_EDX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xbf00))) (Word 0 32)) (BinOp OP_AND (Var R_EDX) (Word 0xFFFFFF00 32)))
)

(* 0x0004f60d: MOV EAX,EDX *)
(*     325133: MOV EAX,EDX *)
| 0x4f60d => Some (2,
	Move R_EAX (Var R_EDX)
)

(* 0x0004f60f: RET *)
(*     325135: RET *)
| 0x4f60f => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx isxdigit_i386.
Proof. Picinae_typecheck. Qed.

(* Codex-local BSF32 adapter: bsf_adapter.py + pcode2coq_codex.py.
   Exact Ghidra graph; bounded guarded Rep; other loops remain rejected. *)
(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: ffsll
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ffsll_i386 : program := fun _ a => match a with

(* 0x00063bb4: PUSH EBX *)
(*     408500: PUSH EBX *)
| 0x63bb4 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00063bb5: MOV EBX,dword ptr [ESP + 0x8] *)
(*     408501: MOV EBX,dword ptr [ESP + 0x8] *)
| 0x63bb5 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x8 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EBX (Var (V_TEMP 0xb900))
)

(* 0x00063bb9: MOV ECX,dword ptr [ESP + 0xc] *)
(*     408505: MOV ECX,dword ptr [ESP + 0xc] *)
| 0x63bb9 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0xc 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_ECX (Var (V_TEMP 0xb900))
)

(* 0x00063bbd: MOV EAX,EBX *)
(*     408509: MOV EAX,EBX *)
| 0x63bbd => Some (2,
	Move R_EAX (Var R_EBX)
)

(* 0x00063bbf: OR EAX,ECX *)
(*     408511: OR EAX,ECX *)
| 0x63bbf => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_EAX (BinOp OP_OR (Var R_EAX) (Var R_ECX)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EAX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00063bc1: JZ 0x00063bd5 *)
(*     408513: JZ 0x00063bd5 *)
| 0x63bc1 => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x63bd5 32)
	) (* else *) (
		Nop
	)
)

(* 0x00063bc3: BSF EDX,EBX *)
(*     408515: BSF EDX,EBX *)
| 0x63bc3 => Some (3,
	Move (V_TEMP 0x2c680) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EBX) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	(* Codex BSF32: exact graph, 32 guarded iterations. *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x2c780))) (
		Nop
	) (* else *) (
		Rep (Word 32 32) (
	Move (V_TEMP 0x2c800) (BinOp OP_RSHIFT (Var R_EBX) (Var (V_TEMP 0x2c680))) $;
	Move (V_TEMP 0x2c880) (BinOp OP_AND (Var (V_TEMP 0x2c800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2c900) (BinOp OP_NEQ (Var (V_TEMP 0x2c880)) (Word 0x0 32)) $;
		If (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Nop) (* else *) (Move (V_TEMP 0x2c680) (BinOp OP_PLUS (Var (V_TEMP 0x2c680)) (Word 0x1 32)))
		)
	) $;
	Move R_EDX (Var (V_TEMP 0x2c680))
)

(* 0x00063bc6: JNZ 0x00063bce *)
(*     408518: JNZ 0x00063bce *)
| 0x63bc6 => Some (2,
	Move (V_TEMP 0xbe00) (UnOp OP_NOT (Var R_ZF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xbe00))) (
		Jmp (Word 0x63bce 32)
	) (* else *) (
		Nop
	)
)

(* 0x00063bc8: BSF EDX,ECX *)
(*     408520: BSF EDX,ECX *)
| 0x63bc8 => Some (3,
	Move (V_TEMP 0x2c680) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ECX) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	(* Codex BSF32: exact graph, 32 guarded iterations. *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x2c780))) (
		Nop
	) (* else *) (
		Rep (Word 32 32) (
	Move (V_TEMP 0x2c800) (BinOp OP_RSHIFT (Var R_ECX) (Var (V_TEMP 0x2c680))) $;
	Move (V_TEMP 0x2c880) (BinOp OP_AND (Var (V_TEMP 0x2c800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2c900) (BinOp OP_NEQ (Var (V_TEMP 0x2c880)) (Word 0x0 32)) $;
		If (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Nop) (* else *) (Move (V_TEMP 0x2c680) (BinOp OP_PLUS (Var (V_TEMP 0x2c680)) (Word 0x1 32)))
		)
	) $;
	Move R_EDX (Var (V_TEMP 0x2c680))
)

(* 0x00063bcb: ADD EDX,0x20 *)
(*     408523: ADD EDX,0x20 *)
| 0x63bcb => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EDX) (Word 0x20 32)) (Var R_EDX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EDX) (Word 0x20 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EDX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x20 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EDX (BinOp OP_PLUS (Var R_EDX) (Word 0x20 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EDX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EDX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EDX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00063bce: ADD EDX,0x1 *)
(*     408526: ADD EDX,0x1 *)
| 0x63bce => Some (3,
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

(* 0x00063bd1: MOV EAX,EDX *)
(*     408529: MOV EAX,EDX *)
| 0x63bd1 => Some (2,
	Move R_EAX (Var R_EDX)
)

(* 0x00063bd3: POP EBX *)
(*     408531: POP EBX *)
| 0x63bd3 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x00063bd4: RET *)
(*     408532: RET *)
| 0x63bd4 => Some (1,
	Move R_EIP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Jmp (Var R_EIP)
)

(* 0x00063bd5: XOR EDX,EDX *)
(*     408533: XOR EDX,EDX *)
| 0x63bd5 => Some (2,
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

(* 0x00063bd7: JMP 0x00063bd1 *)
(*     408535: JMP 0x00063bd1 *)
| 0x63bd7 => Some (2,
	Jmp (Word 0x63bd1 32)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x86typctx ffsll_i386.
Proof. Picinae_typecheck. Qed.

(* Codex-local BSF32 adapter: bsf_adapter.py + pcode2coq_codex.py.
   Exact Ghidra graph; bounded guarded Rep; other loops remain rejected. *)
(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: ffsl
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ffsl_i386 : program := fun _ a => match a with

(* 0x00063ba5: MOV EAX,dword ptr [ESP + 0x4] *)
(*     408485: MOV EAX,dword ptr [ESP + 0x4] *)
| 0x63ba5 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x4 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x00063ba9: TEST EAX,EAX *)
(*     408489: TEST EAX,EAX *)
| 0x63ba9 => Some (2,
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

(* 0x00063bab: JZ 0x00063bb3 *)
(*     408491: JZ 0x00063bb3 *)
| 0x63bab => Some (2,
	If (Cast CAST_LOW 1 (Var R_ZF)) (
		Jmp (Word 0x63bb3 32)
	) (* else *) (
		Nop
	)
)

(* 0x00063bad: BSF EAX,EAX *)
(*     408493: BSF EAX,EAX *)
| 0x63bad => Some (3,
	Move (V_TEMP 0x2c680) (Word 0x0 32) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EAX) (Word 0x0 32))) $;
	Move (V_TEMP 0x2c780) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x1 8))) $;
	(* Codex BSF32: exact graph, 32 guarded iterations. *)
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x2c780))) (
		Nop
	) (* else *) (
		Rep (Word 32 32) (
	Move (V_TEMP 0x2c800) (BinOp OP_RSHIFT (Var R_EAX) (Var (V_TEMP 0x2c680))) $;
	Move (V_TEMP 0x2c880) (BinOp OP_AND (Var (V_TEMP 0x2c800)) (Word 0x1 32)) $;
	Move (V_TEMP 0x2c900) (BinOp OP_NEQ (Var (V_TEMP 0x2c880)) (Word 0x0 32)) $;
		If (Cast CAST_LOW 1 (Var (V_TEMP 0x2c900))) (Nop) (* else *) (Move (V_TEMP 0x2c680) (BinOp OP_PLUS (Var (V_TEMP 0x2c680)) (Word 0x1 32)))
		)
	) $;
	Move R_EAX (Var (V_TEMP 0x2c680))
)

(* 0x00063bb0: ADD EAX,0x1 *)
(*     408496: ADD EAX,0x1 *)
| 0x63bb0 => Some (3,
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

(* 0x00063bb3: RET *)
(*     408499: RET *)
| 0x63bb3 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx ffsl_i386.
Proof. Picinae_typecheck. Qed.

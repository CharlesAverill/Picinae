(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: ffsll
entry: 0x1a9930 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition ffsl_amd64 : program := fun _ a => match a with

(* 0x001a9930: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x001a9934: MOV EDX,0xffffffff *)
(*          4: MOV EDX,0xffffffff *)
| 0x4 => Some (5,
	Move R_RDX (Word 0xffffffff 64)
)

(* 0x001a9939: BSF RAX,RDI *)
(*          9: BSF RAX,RDI *)
| 0x9 => Some (4,
	Move (V_TEMP 0x34580) (Word 0x0 64) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDI) (Word 0x0 64)))) $;
	Move (V_TEMP 0x34680) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x34680))) (
		Move R_RAX (Var (V_TEMP 0x34580))
	) (* else *) (
		Rep (Word 65 64) (
			Move (V_TEMP 0x34580) (Ite (Cast CAST_LOW 1 ((Cast CAST_UNSIGNED 8 (BinOp OP_NEQ ((BinOp OP_AND ((BinOp OP_RSHIFT (Var R_RDI) (Var (V_TEMP 0x34580)))) (Word 0x1 64))) (Word 0x0 64))))) (Var (V_TEMP 0x34580)) (BinOp OP_PLUS (Var (V_TEMP 0x34580)) (Word 0x1 64)))
		) $;
		Move R_RAX (Var (V_TEMP 0x34580))
	)
)

(* 0x001a993d: CMOVZ RAX,RDX *)
(*         13: CMOVZ RAX,RDX *)
| 0xd => Some (4,
	Move (V_TEMP 0x3dd00) (Var R_RDX) $;
	Move (V_TEMP 0x3dd80) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dd80))) (
		Jmp (Word 0x11 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (Var (V_TEMP 0x3dd00))
)

(* 0x001a9941: ADD EAX,0x1 *)
(*         17: ADD EAX,0x1 *)
| 0x11 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a9944: RET *)
(*         20: RET *)
| 0x14 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx ffsl_amd64.
Proof. Picinae_typecheck. Qed.


(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: imaxabs
entry: 0x145de0 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition labs_amd64 : program := fun _ a => match a with

(* 0x00145de0: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00145de4: MOV RAX,RDI *)
(*          4: MOV RAX,RDI *)
| 0x4 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x00145de7: NEG RAX *)
(*          7: NEG RAX *)
| 0x7 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_RAX) (Word 0x0 64)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 64) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 64) (Var R_RAX)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 64) (Var R_RAX)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (UnOp OP_NEG (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00145dea: CMOVS RAX,RDI *)
(*         10: CMOVS RAX,RDI *)
| 0xa => Some (4,
	Move (V_TEMP 0x3dd00) (Var R_RDI) $;
	Move (V_TEMP 0x3dd80) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_SF)) (Word 1 8)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x3dd80))) (
		Jmp (Word 0xe 64)
	) (* else *) (
		Nop
	) $;
	Move R_RAX (Var (V_TEMP 0x3dd00))
)

(* 0x00145dee: RET *)
(*         14: RET *)
| 0xe => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx labs_amd64.
Proof. Picinae_typecheck. Qed.


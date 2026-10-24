(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: insque
entry: 0x21d090 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition insque_amd64 : program := fun _ a => match a with

(* 0x0021d090: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x0021d094: XOR EAX,EAX *)
(*          4: XOR EAX,EAX *)
| 0x4 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021d096: TEST RSI,RSI *)
(*          6: TEST RSI,RSI *)
| 0x6 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RSI) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021d099: JZ 0x0021d0aa *)
(*          9: JZ 0x0021d0aa *)
| 0x9 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1a 64)
	) (* else *) (
		Nop
	)
)

(* 0x0021d09b: MOV RAX,qword ptr [RSI] *)
(*         11: MOV RAX,qword ptr [RSI] *)
| 0xb => Some (3,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x12000))
)

(* 0x0021d09e: MOV qword ptr [RSI],RDI *)
(*         14: MOV qword ptr [RSI],RDI *)
| 0xe => Some (3,
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSI) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x0021d0a1: TEST RAX,RAX *)
(*         17: TEST RAX,RAX *)
| 0x11 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RAX) (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021d0a4: JZ 0x0021d0aa *)
(*         20: JZ 0x0021d0aa *)
| 0x14 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1a 64)
	) (* else *) (
		Nop
	)
)

(* 0x0021d0a6: MOV qword ptr [RAX + 0x8],RDI *)
(*         22: MOV qword ptr [RAX + 0x8],RDI *)
| 0x16 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RDI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x0021d0aa: MOV qword ptr [RDI],RAX *)
(*         26: MOV qword ptr [RDI],RAX *)
| 0x1a => Some (3,
	Move (V_TEMP 0x6b80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x0021d0ad: MOV qword ptr [RDI + 0x8],RSI *)
(*         29: MOV qword ptr [RDI + 0x8],RSI *)
| 0x1d => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RSI) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x0021d0b1: RET *)
(*         33: RET *)
| 0x21 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx insque_amd64.
Proof. Picinae_typecheck. Qed.


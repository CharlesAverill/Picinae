(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: remque
entry: 0x21d0c0 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition remque_amd64 : program := fun _ a => match a with

(* 0x0021d0c0: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x0021d0c4: MOV RDX,qword ptr [RDI] *)
(*          4: MOV RDX,qword ptr [RDI] *)
| 0x4 => Some (3,
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var R_RDI) LittleE 8) $;
	Move R_RDX (Var (V_TEMP 0x12000))
)

(* 0x0021d0c7: MOV RAX,qword ptr [RDI + 0x8] *)
(*          7: MOV RAX,qword ptr [RDI + 0x8] *)
| 0x7 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 0x12000) (Load (Var V_MEM64) (Var (V_TEMP 0x4780)) LittleE 8) $;
	Move R_RAX (Var (V_TEMP 0x12000))
)

(* 0x0021d0cb: TEST RDX,RDX *)
(*         11: TEST RDX,RDX *)
| 0xb => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RDX) (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0021d0ce: JZ 0x0021d0d4 *)
(*         14: JZ 0x0021d0d4 *)
| 0xe => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x14 64)
	) (* else *) (
		Nop
	)
)

(* 0x0021d0d0: MOV qword ptr [RDX + 0x8],RAX *)
(*         16: MOV qword ptr [RDX + 0x8],RAX *)
| 0x10 => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RDX) (Word 0x8 64)) $;
	Move (V_TEMP 0x6b80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x4780)) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x0021d0d4: TEST RAX,RAX *)
(*         20: TEST RAX,RAX *)
| 0x14 => Some (3,
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

(* 0x0021d0d7: JZ 0x0021d0dc *)
(*         23: JZ 0x0021d0dc *)
| 0x17 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0021d0d9: MOV qword ptr [RAX],RDX *)
(*         25: MOV qword ptr [RAX],RDX *)
| 0x19 => Some (3,
	Move (V_TEMP 0x6b80) (Var R_RDX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RAX) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x0021d0dc: RET *)
(*         28: RET *)
| 0x1c => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx remque_amd64.
Proof. Picinae_typecheck. Qed.


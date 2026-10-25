(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: sigfillset
entry: 0x142e70 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition sigfillset_amd64 : program := fun _ a => match a with

(* 0x00142e70: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00142e74: TEST RDI,RDI *)
(*          4: TEST RDI,RDI *)
| 0x4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70580) (BinOp OP_AND (Var R_RDI) (Var R_RDI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70580)) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70580)) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x00142e77: JZ 0x00142e89 *)
(*          7: JZ 0x00142e89 *)
| 0x7 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x19 64)
	) (* else *) (
		Nop
	)
)

(* 0x00142e79: MOV RAX,-0x180000001 *)
(*          9: MOV RAX,-0x180000001 *)
| 0x9 => Some (10,
	Move R_RAX (Word 0xfffffffe7fffffff 64)
)

(* 0x00142e83: MOV qword ptr [RDI],RAX *)
(*         19: MOV qword ptr [RDI],RAX *)
| 0x13 => Some (3,
	Move (V_TEMP 0x6b80) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Var (V_TEMP 0x6b80)) LittleE 8)
)

(* 0x00142e86: XOR EAX,EAX *)
(*         22: XOR EAX,EAX *)
| 0x16 => Some (2,
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

(* 0x00142e88: RET *)
(*         24: RET *)
| 0x18 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00142e89: MOV RAX,qword ptr [0x00319e10] *)
(*         25: MOV RAX,qword ptr [0x00319e10] *)
| 0x19 => Some (7,
	Move R_RAX (Load (Var V_MEM64) (Word 0x319e10 64) LittleE 8)
)

(* 0x00142e90: MOV dword ptr FS:[RAX],0x16 *)
(*         32: MOV dword ptr FS:[RAX],0x16 *)
| 0x20 => Some (7,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Var R_RAX)) $;
	Move (V_TEMP 0x6b00) (Word 0x16 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00142e97: MOV EAX,0xffffffff *)
(*         39: MOV EAX,0xffffffff *)
| 0x27 => Some (5,
	Move R_RAX (Word 0xffffffff 64)
)

(* 0x00142e9c: RET *)
(*         44: RET *)
| 0x2c => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx sigfillset_amd64.
Proof. Picinae_typecheck. Qed.


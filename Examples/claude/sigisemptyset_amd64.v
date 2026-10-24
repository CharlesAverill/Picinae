(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: sigisemptyset
entry: 0x143070 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition sigisemptyset_amd64 : program := fun _ a => match a with

(* 0x00143070: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00143074: TEST RDI,RDI *)
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

(* 0x00143077: JZ 0x00143088 *)
(*          7: JZ 0x00143088 *)
| 0x7 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x18 64)
	) (* else *) (
		Nop
	)
)

(* 0x00143079: MOV EDX,dword ptr [RDI] *)
(*          9: MOV EDX,dword ptr [RDI] *)
| 0x9 => Some (2,
	Move (V_TEMP 0x11f80) (Load (Var V_MEM64) (Var R_RDI) LittleE 4) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Var (V_TEMP 0x11f80))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0014307b: XOR EAX,EAX *)
(*         11: XOR EAX,EAX *)
| 0xb => Some (2,
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

(* 0x0014307d: TEST EDX,EDX *)
(*         13: TEST EDX,EDX *)
| 0xd => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move (V_TEMP 0x70480) (BinOp OP_AND (Extract 31 0 (Var R_RDX)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x70480)) (Word 0x0 32)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var (V_TEMP 0x70480)) (Word 0xff 32)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x0014307f: SETZ AL *)
(*         15: SETZ AL *)
| 0xf => Some (3,
	Move R_RAX (Concat (Extract 63 8 (Var R_RAX)) (Cast CAST_UNSIGNED 8 (Var R_ZF)))
)

(* 0x00143082: RET *)
(*         18: RET *)
| 0x12 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

(* 0x00143088: MOV RAX,qword ptr [0x00319e10] *)
(*         24: MOV RAX,qword ptr [0x00319e10] *)
| 0x18 => Some (7,
	Move R_RAX (Load (Var V_MEM64) (Word 0x319e10 64) LittleE 8)
)

(* 0x0014308f: MOV dword ptr FS:[RAX],0x16 *)
(*         31: MOV dword ptr FS:[RAX],0x16 *)
| 0x1f => Some (7,
	Move (V_TEMP 0x6580) (BinOp OP_PLUS (Var R_FS_BASE) (Var R_RAX)) $;
	Move (V_TEMP 0x6b00) (Word 0x16 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6580)) (Var (V_TEMP 0x6b00)) LittleE 4)
)

(* 0x00143096: MOV EAX,0xffffffff *)
(*         38: MOV EAX,0xffffffff *)
| 0x26 => Some (5,
	Move R_RAX (Word 0xffffffff 64)
)

(* 0x0014309b: RET *)
(*         43: RET *)
| 0x2b => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx sigisemptyset_amd64.
Proof. Picinae_typecheck. Qed.


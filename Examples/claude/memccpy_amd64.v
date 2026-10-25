(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: memccpy at 0x1a9bb0
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition memccpy_amd64 : program := fun _ a => match a with

(* ---- memccpy ---- *)

(* 0x001a9bb0: ENDBR64 *)
(*    1743792: ENDBR64 *)
| 0x1a9bb0 => Some (4,
	Nop
)

(* 0x001a9bb4: PUSH R13 *)
(*    1743796: PUSH R13 *)
| 0x1a9bb4 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R13) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x001a9bb6: MOV R13,RDI *)
(*    1743798: MOV R13,RDI *)
| 0x1a9bb6 => Some (3,
	Move R_R13 (Var R_RDI)
)

(* 0x001a9bb9: PUSH R12 *)
(*    1743801: PUSH R12 *)
| 0x1a9bb9 => Some (2,
	Move (V_TEMP 0x27d80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x001a9bbb: MOV R12,RCX *)
(*    1743803: MOV R12,RCX *)
| 0x1a9bbb => Some (3,
	Move R_R12 (Var R_RCX)
)

(* 0x001a9bbe: PUSH RBP *)
(*    1743806: PUSH RBP *)
| 0x1a9bbe => Some (1,
	Move (V_TEMP 0x27d80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Var (V_TEMP 0x27d80)) LittleE 8)
)

(* 0x001a9bbf: MOV RBP,RSI *)
(*    1743807: MOV RBP,RSI *)
| 0x1a9bbf => Some (3,
	Move R_RBP (Var R_RSI)
)

(* 0x001a9bc2: MOV ESI,EDX *)
(*    1743810: MOV ESI,EDX *)
| 0x1a9bc2 => Some (2,
	Move R_RSI (Concat (Extract 63 32 (Var R_RSI)) (Extract 31 0 (Var R_RDX))) $;
	Move R_RSI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RSI)))
)

(* 0x001a9bc4: MOV RDX,RCX *)
(*    1743812: MOV RDX,RCX *)
| 0x1a9bc4 => Some (3,
	Move R_RDX (Var R_RCX)
)

(* 0x001a9bc7: MOV RDI,RBP *)
(*    1743815: MOV RDI,RBP *)
| 0x1a9bc7 => Some (3,
	Move R_RDI (Var R_RBP)
)

(* 0x001a9bca: CALL 0x00128420 *)
(*    1743818: CALL 0x00128420 *)
| 0x1a9bca => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1a9bcf 64) LittleE 8) $;
	Jmp (Word 0x128420 64)
)

(* 0x001a9bcf: TEST RAX,RAX *)
(*    1743823: TEST RAX,RAX *)
| 0x1a9bcf => Some (3,
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

(* 0x001a9bd2: JZ 0x001a9bf0 *)
(*    1743826: JZ 0x001a9bf0 *)
| 0x1a9bd2 => Some (2,
	If (Var R_ZF) (
		Jmp (Word 0x1a9bf0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001a9bd4: SUB RAX,RBP *)
(*    1743828: SUB RAX,RBP *)
| 0x1a9bd4 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var R_RAX) (Var R_RBP)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RAX) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RBP)) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_RAX) (Var R_RBP)) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_RBP) (Word 63 64)) (Word 1 64))) (Word 1 64))))) $;
	Move R_RAX (BinOp OP_MINUS (Var R_RAX) (Var R_RBP)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0x2c280) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 0x2c300) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x2c280)))) $;
	Move (V_TEMP 0x2c380) (BinOp OP_AND (Var (V_TEMP 0x2c300)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x2c380)) (Word 0x0 8))))
)

(* 0x001a9bd7: MOV RSI,RBP *)
(*    1743831: MOV RSI,RBP *)
| 0x1a9bd7 => Some (3,
	Move R_RSI (Var R_RBP)
)

(* 0x001a9bda: MOV RDI,R13 *)
(*    1743834: MOV RDI,R13 *)
| 0x1a9bda => Some (3,
	Move R_RDI (Var R_R13)
)

(* 0x001a9bdd: POP RBP *)
(*    1743837: POP RBP *)
| 0x1a9bdd => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55480))
)

(* 0x001a9bde: LEA RDX,[RAX + 0x1] *)
(*    1743838: LEA RDX,[RAX + 0x1] *)
| 0x1a9bde => Some (4,
	Move (V_TEMP 0x4780) (BinOp OP_PLUS (Var R_RAX) (Word 0x1 64)) $;
	Move R_RDX (Var (V_TEMP 0x4780))
)

(* 0x001a9be2: POP R12 *)
(*    1743842: POP R12 *)
| 0x1a9be2 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55480))
)

(* 0x001a9be4: POP R13 *)
(*    1743844: POP R13 *)
| 0x1a9be4 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R13 (Var (V_TEMP 0x55480))
)

(* 0x001a9be6: JMP 0x001283e0 *)
(*    1743846: JMP 0x001283e0 *)
| 0x1a9be6 => Some (5,
	Jmp (Word 0x1283e0 64)
)

(* 0x001a9bf0: MOV RDX,R12 *)
(*    1743856: MOV RDX,R12 *)
| 0x1a9bf0 => Some (3,
	Move R_RDX (Var R_R12)
)

(* 0x001a9bf3: MOV RSI,RBP *)
(*    1743859: MOV RSI,RBP *)
| 0x1a9bf3 => Some (3,
	Move R_RSI (Var R_RBP)
)

(* 0x001a9bf6: MOV RDI,R13 *)
(*    1743862: MOV RDI,R13 *)
| 0x1a9bf6 => Some (3,
	Move R_RDI (Var R_R13)
)

(* 0x001a9bf9: CALL 0x00128620 *)
(*    1743865: CALL 0x00128620 *)
| 0x1a9bf9 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x1a9bfe 64) LittleE 8) $;
	Jmp (Word 0x128620 64)
)

(* 0x001a9bfe: POP RBP *)
(*    1743870: POP RBP *)
| 0x1a9bfe => Some (1,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55480))
)

(* 0x001a9bff: XOR EAX,EAX *)
(*    1743871: XOR EAX,EAX *)
| 0x1a9bff => Some (2,
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

(* 0x001a9c01: POP R12 *)
(*    1743873: POP R12 *)
| 0x1a9c01 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55480))
)

(* 0x001a9c03: POP R13 *)
(*    1743875: POP R13 *)
| 0x1a9c03 => Some (2,
	Move (V_TEMP 0x55480) (Word 0x0 64) $;
	Move (V_TEMP 0x55480) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R13 (Var (V_TEMP 0x55480))
)

(* 0x001a9c05: RET *)
(*    1743877: RET *)
| 0x1a9c05 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx memccpy_amd64.
Proof. Picinae_typecheck. Qed.

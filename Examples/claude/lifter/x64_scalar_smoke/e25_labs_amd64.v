(* Strict AMD64 scalar profile, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: glibc; ELF SHA256: 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
Symbol: labs; global entry: 0x145de0; selected: toascii, isascii, abs, labs, pthread_equal
Profile: cet-disabled (CET-enabled execution is outside this model).
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e25_labs_amd64 : program := fun _ a => match a with
(* 0x13a170: ENDBR64 *)
| 0x13a170 => Some (4,
	Nop
)
(* 0x13a174: MOV EAX,EDI *)
| 0x13a174 => Some (2,
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)
(* 0x13a176: AND EAX,0x7f *)
| 0x13a176 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0x7f 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x13a179: RET *)
| 0x13a179 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x13a180: ENDBR64 *)
| 0x13a180 => Some (4,
	Nop
)
(* 0x13a184: XOR EAX,EAX *)
| 0x13a184 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x13a186: AND EDI,0xffffff80 *)
| 0x13a186 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xffffff80 32))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RDI)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x13a189: SETZ AL *)
| 0x13a189 => Some (3,
	Move R_RAX (BinOp OP_OR (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffff00 64)) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_ZF))))
)
(* 0x13a18c: RET *)
| 0x13a18c => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x145dd0: ENDBR64 *)
| 0x145dd0 => Some (4,
	Nop
)
(* 0x145dd4: MOV EAX,EDI *)
| 0x145dd4 => Some (2,
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)
(* 0x145dd6: NEG EAX *)
| 0x145dd6 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Word 0x0 32) (Extract 31 0 (Var R_RAX))) (BinOp OP_MINUS (Word 0x0 32) (Extract 31 0 (Var R_RAX))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 31 31 (Word 0x0 32)) (Extract 31 31 (Extract 31 0 (Var R_RAX)))) (BinOp OP_XOR (Extract 31 31 (Word 0x0 32)) (Extract 31 31 (BinOp OP_MINUS (Word 0x0 32) (Extract 31 0 (Var R_RAX)))))))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (UnOp OP_NEG (Extract 31 0 (Var R_RAX)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)
(* 0x145dd8: CMOVS EAX,EDI *)
| 0x145dd8 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDI)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_SF)) (Word 0x1 8)) $;
	If (BinOp OP_NEQ (Var (V_TEMP 1)) (Word 0x0 8)) (Jmp (Word 0x145ddb 64)) (Move R_RAX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0))))
)
(* 0x145ddb: RET *)
| 0x145ddb => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x145de0: ENDBR64 *)
| 0x145de0 => Some (4,
	Nop
)
(* 0x145de4: MOV RAX,RDI *)
| 0x145de4 => Some (3,
	Move R_RAX (Var R_RDI)
)
(* 0x145de7: NEG RAX *)
| 0x145de7 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_RAX) (Word 0x0 64)))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Word 0x0 64) (Var R_RAX)) (BinOp OP_MINUS (Word 0x0 64) (Var R_RAX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Word 0x0 64)) (Extract 63 63 (Var R_RAX))) (BinOp OP_XOR (Extract 63 63 (Word 0x0 64)) (Extract 63 63 (BinOp OP_MINUS (Word 0x0 64) (Var R_RAX))))))) $;
	Move R_RAX (UnOp OP_NEG (Var R_RAX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RAX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RAX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RAX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x145dea: CMOVS RAX,RDI *)
| 0x145dea => Some (4,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_SF)) (Word 0x1 8)) $;
	If (BinOp OP_NEQ (Var (V_TEMP 1)) (Word 0x0 8)) (Jmp (Word 0x145dee 64)) (Move R_RAX (Var (V_TEMP 0)))
)
(* 0x145dee: RET *)
| 0x145dee => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x195c70: ENDBR64 *)
| 0x195c70 => Some (4,
	Nop
)
(* 0x195c74: XOR EAX,EAX *)
| 0x195c74 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_OF (Cast CAST_LOW 1 (Word 0x0 8)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Extract 31 0 (Var R_RAX)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x195c76: CMP RDI,RSI *)
| 0x195c76 => Some (3,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Var R_RSI)))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 0)) (Var R_RSI)) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RSI)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var (V_TEMP 0))) (Extract 63 63 (Var R_RSI))) (BinOp OP_XOR (Extract 63 63 (Var (V_TEMP 0))) (Extract 63 63 (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RSI))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RSI)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)
(* 0x195c79: SETZ AL *)
| 0x195c79 => Some (3,
	Move R_RAX (BinOp OP_OR (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffff00 64)) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_ZF))))
)
(* 0x195c7c: RET *)
| 0x195c7c => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e25_labs_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

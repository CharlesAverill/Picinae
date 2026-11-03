(* Strict AMD64 scalar profile, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: synthetic; ELF SHA256: fbc4ef542d199d81f98f0c1a19ff339694a6a6ac0ef509653d12d75bec5f7576
Symbol: scalar_caller; global entry: 0x101000; selected: scalar_caller, scalar_callee
Profile: strict (CET-enabled execution is outside this model).
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e25_scalar_caller_amd64 : program := fun _ a => match a with
(* 0x101000: CALL 0x00101006 *)
| 0x101000 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Word 0x101005 64) LittleE 8) $;
	Jmp (Word 0x101006 64)
)
(* 0x101005: RET *)
| 0x101005 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x101006: MOV RAX,RDI *)
| 0x101006 => Some (3,
	Move R_RAX (Var R_RDI)
)
(* 0x101009: MOV AH,0xab *)
| 0x101009 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffff00ff 64)) (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Word 0xab 8)) (Word 0x8 64)))
)
(* 0x10100b: MOV AX,0x1234 *)
| 0x10100b => Some (4,
	Move R_RAX (BinOp OP_OR (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffff0000 64)) (Cast CAST_UNSIGNED 64 (Word 0x1234 16)))
)
(* 0x10100f: MOV EAX,0x89abcdef *)
| 0x10100f => Some (5,
	Move R_RAX (Word 0x89abcdef 64)
)
(* 0x101014: MOV qword ptr [RSI],RAX *)
| 0x101014 => Some (3,
	Move (V_TEMP 0) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSI) (Var (V_TEMP 0)) LittleE 8)
)
(* 0x101017: ADD AL,0x1 *)
| 0x101017 => Some (2,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 7 0 (Var R_RAX)) (Word 0x1 8)) (Extract 7 0 (Var R_RAX))))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Extract 7 0 (Var R_RAX)) (Word 0x1 8)) (BinOp OP_PLUS (Extract 7 0 (Var R_RAX)) (Word 0x1 8)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 7 7 (Extract 7 0 (Var R_RAX))) (Extract 7 7 (Word 0x1 8))) (Word 0x1 1)) (BinOp OP_XOR (Extract 7 7 (Extract 7 0 (Var R_RAX))) (Extract 7 7 (BinOp OP_PLUS (Extract 7 0 (Var R_RAX)) (Word 0x1 8))))))) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffffff00 64)) (Cast CAST_UNSIGNED 64 (BinOp OP_PLUS (Extract 7 0 (Var R_RAX)) (Word 0x1 8)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 7 0 (Var R_RAX)) (Word 0x0 8)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 7 0 (Var R_RAX)) (Word 0x0 8)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 7 0 (Var R_RAX)) (Word 0xff 8)) $;
	Move (V_TEMP 1) (UnOp OP_POPCOUNT (Var (V_TEMP 0))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x101019: SUB AX,0x1 *)
| 0x101019 => Some (4,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Extract 15 0 (Var R_RAX)) (Word 0x1 16)))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Extract 15 0 (Var R_RAX)) (Word 0x1 16)) (BinOp OP_MINUS (Extract 15 0 (Var R_RAX)) (Word 0x1 16)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 15 15 (Extract 15 0 (Var R_RAX))) (Extract 15 15 (Word 0x1 16))) (BinOp OP_XOR (Extract 15 15 (Extract 15 0 (Var R_RAX))) (Extract 15 15 (BinOp OP_MINUS (Extract 15 0 (Var R_RAX)) (Word 0x1 16))))))) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_AND (Var R_RAX) (Word 0xffffffffffff0000 64)) (Cast CAST_UNSIGNED 64 (BinOp OP_MINUS (Extract 15 0 (Var R_RAX)) (Word 0x1 16)))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 15 0 (Var R_RAX)) (Word 0x0 16)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 15 0 (Var R_RAX)) (Word 0x0 16)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 15 0 (Var R_RAX)) (Word 0xff 16)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x10101d: MOV RDX,qword ptr [RSI] *)
| 0x10101d => Some (3,
	Move (V_TEMP 0) (Load (Var V_MEM64) (Var R_RSI) LittleE 8) $;
	Move R_RDX (Var (V_TEMP 0))
)
(* 0x101020: MOV RCX,qword ptr [0x00103000] *)
| 0x101020 => Some (7,
	Move R_RCX (Load (Var V_MEM64) (Word 0x103000 64) LittleE 8)
)
(* 0x101027: CMP RDX,RCX *)
| 0x101027 => Some (3,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (Var (V_TEMP 0)) (Var R_RCX)))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 0)) (Var R_RCX)) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Var (V_TEMP 0))) (Extract 63 63 (Var R_RCX))) (BinOp OP_XOR (Extract 63 63 (Var (V_TEMP 0))) (Extract 63 63 (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX))))))) $;
	Move (V_TEMP 1) (BinOp OP_MINUS (Var (V_TEMP 0)) (Var R_RCX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 1)) (Word 0x0 64)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0xff 64)) $;
	Move (V_TEMP 3) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 2)))) $;
	Move (V_TEMP 4) (BinOp OP_AND (Var (V_TEMP 3)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 4)) (Word 0x0 8))))
)
(* 0x10102a: JZ 0x0010102f *)
| 0x10102a => Some (2,
	If (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x0 8)) (Jmp (Word 0x10102f 64)) (Nop)
)
(* 0x10102c: NEG RDX *)
| 0x10102c => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var R_RDX) (Word 0x0 64)))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Word 0x0 64) (Var R_RDX)) (BinOp OP_MINUS (Word 0x0 64) (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (Extract 63 63 (Word 0x0 64)) (Extract 63 63 (Var R_RDX))) (BinOp OP_XOR (Extract 63 63 (Word 0x0 64)) (Extract 63 63 (BinOp OP_MINUS (Word 0x0 64) (Var R_RDX))))))) $;
	Move R_RDX (UnOp OP_NEG (Var R_RDX)) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var R_RDX) (Word 0x0 64)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_RDX) (Word 0x0 64)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Var R_RDX) (Word 0xff 64)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x10102f: RET *)
| 0x10102f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e25_scalar_caller_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

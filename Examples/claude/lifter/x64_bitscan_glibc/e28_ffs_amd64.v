(* Strict AMD64 scalar profile, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: glibc; ELF SHA256: 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
Symbol: ffs; global entry: 0x1a9910; selected: ffs, ffsl, ffsll
Scope: selected closed function extents.
Undefined scan destinations/flags use Unknown; BSF/BSR zero-input full destination is havoc.
Feature profiles are caller assumptions, not runtime CPUID detection.
Profile: cet-disabled;bmi1=unspecified;abm=unspecified (CET-enabled execution is outside this model).
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e28_ffs_amd64 : program := fun _ a => match a with
(* 0x1a9910: ENDBR64 *)
| 0x1a9910 => Some (4,
	Nop
)
(* 0x1a9914: MOV EDX,0xffffffff *)
| 0x1a9914 => Some (5,
	Move R_RDX (Word 0xffffffff 64)
)
(* 0x1a9919: BSF EAX,EDI *)
| 0x1a9919 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDI)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) (Move R_RAX (Unknown 64)) (Move R_RAX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1a991c: CMOVZ EAX,EDX *)
| 0x1a991c => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8)) $;
	If (BinOp OP_NEQ (Var (V_TEMP 1)) (Word 0x0 8)) (Jmp (Word 0x1a991f 64)) (Move R_RAX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0))))
)
(* 0x1a991f: ADD EAX,0x1 *)
| 0x1a991f => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_RAX))) (Extract 31 31 (Word 0x1 32))) (Word 0x1 1)) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_RAX))) (Extract 31 31 (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))))))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x1a9922: RET *)
| 0x1a9922 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x1a9930: ENDBR64 *)
| 0x1a9930 => Some (4,
	Nop
)
(* 0x1a9934: MOV EDX,0xffffffff *)
| 0x1a9934 => Some (5,
	Move R_RDX (Word 0xffffffff 64)
)
(* 0x1a9939: BSF RAX,RDI *)
| 0x1a9939 => Some (4,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RAX (Unknown 64)) (Move R_RAX (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1a993d: CMOVZ RAX,RDX *)
| 0x1a993d => Some (4,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move (V_TEMP 1) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x1 8)) $;
	If (BinOp OP_NEQ (Var (V_TEMP 1)) (Word 0x0 8)) (Jmp (Word 0x1a9941 64)) (Move R_RAX (Var (V_TEMP 0)))
)
(* 0x1a9941: ADD EAX,0x1 *)
| 0x1a9941 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Extract 31 0 (Var R_RAX))))) $;
	Move R_AF (Extract 4 4 (BinOp OP_XOR (BinOp OP_XOR (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_RAX))) (Extract 31 31 (Word 0x1 32))) (Word 0x1 1)) (BinOp OP_XOR (Extract 31 31 (Extract 31 0 (Var R_RAX))) (Extract 31 31 (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))))))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_PLUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32)))) $;
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 1) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0)))) $;
	Move (V_TEMP 2) (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 8))))
)
(* 0x1a9944: RET *)
| 0x1a9944 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e28_ffs_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

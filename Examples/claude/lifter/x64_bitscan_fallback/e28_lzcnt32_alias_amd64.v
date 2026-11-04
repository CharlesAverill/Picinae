(* Strict AMD64 scalar profile, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: synthetic; ELF SHA256: 4e44c4c19f2432684f42dd2737e6198be20647ffa0775fda02f97eea9af45481
Symbol: lzcnt32_alias; global entry: 0x101046; selected: tzcnt32_alias, tzcnt64_alias, lzcnt32_alias, lzcnt64_alias
Scope: selected closed function extents.
Undefined scan destinations/flags use Unknown; BSF/BSR zero-input full destination is havoc.
Feature profiles are caller assumptions, not runtime CPUID detection.
Profile: strict;bmi1=absent;abm=absent (CET-enabled execution is outside this model).
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e28_lzcnt32_alias_amd64 : program := fun _ a => match a with
(* 0x10102e: TZCNT R9D,R9D *)
| 0x10102e => Some (5,
	Move (V_TEMP 0) (Extract 31 0 (Var R_R9)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) (Move R_R9 (Unknown 64)) (Move R_R9 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x101033: RET *)
| 0x101033 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x10103a: TZCNT R9,R9 *)
| 0x10103a => Some (5,
	Move (V_TEMP 0) (Var R_R9) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_R9 (Unknown 64)) (Move R_R9 (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x10103f: RET *)
| 0x10103f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x101046: LZCNT R9D,R9D *)
| 0x101046 => Some (5,
	Move (V_TEMP 0) (Extract 31 0 (Var R_R9)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x80000000 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) (Move R_R9 (Unknown 64)) (Move R_R9 (Cast CAST_UNSIGNED 64 (BinOp OP_MINUS (Word 0x1f 32) (Var (V_TEMP 2))))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x10104b: RET *)
| 0x10104b => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
(* 0x101052: LZCNT R9,R9 *)
| 0x101052 => Some (5,
	Move (V_TEMP 0) (Var R_R9) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8000000000000000 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_R9 (Unknown 64)) (Move R_R9 (BinOp OP_MINUS (Word 0x3f 64) (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x101057: RET *)
| 0x101057 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e28_lzcnt32_alias_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

(* Strict AMD64 scalar profile, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: samples; ELF SHA256: 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
Symbol: hot_scans; global entry: 0x1b2d40; selected: hot_scans
Scope: instruction samples only; open fallthroughs.
Undefined scan destinations/flags use Unknown; BSF/BSR zero-input full destination is havoc.
Feature profiles are caller assumptions, not runtime CPUID detection.
Profile: strict;bmi1=present;abm=unspecified (CET-enabled execution is outside this model).
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e28_hot_scans_amd64 : program := fun _ a => match a with
(* 0x1b2d40: BSF RDX,RDX *)
| 0x1b2d40 => Some (4,
	Move (V_TEMP 0) (Var R_RDX) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RDX (Unknown 64)) (Move R_RDX (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1b2daf: BSF RDX,RAX *)
| 0x1b2daf => Some (4,
	Move (V_TEMP 0) (Var R_RAX) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RDX (Unknown 64)) (Move R_RDX (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1b2f19: BSF RCX,RCX *)
| 0x1b2f19 => Some (4,
	Move (V_TEMP 0) (Var R_RCX) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RCX (Unknown 64)) (Move R_RCX (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1b2fdf: BSF RCX,RDI *)
| 0x1b2fdf => Some (4,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RCX (Unknown 64)) (Move R_RCX (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1b48f9: BSF EAX,EAX *)
| 0x1b48f9 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RAX)) $;
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
(* 0x1b4f66: BSR EAX,EAX *)
| 0x1b4f66 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RAX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x80000000 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) (Move R_RAX (Unknown 64)) (Move R_RAX (Cast CAST_UNSIGNED 64 (BinOp OP_MINUS (Word 0x1f 32) (Var (V_TEMP 2))))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1b5251: BSF ECX,EDX *)
| 0x1b5251 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) (Move R_RCX (Unknown 64)) (Move R_RCX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1b5275: BSF RCX,R11 *)
| 0x1b5275 => Some (4,
	Move (V_TEMP 0) (Var R_R11) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RCX (Unknown 64)) (Move R_RCX (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1ba380: BSF RAX,RAX *)
| 0x1ba380 => Some (4,
	Move (V_TEMP 0) (Var R_RAX) $;
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
(* 0x1ba6aa: BSR RAX,RAX *)
| 0x1ba6aa => Some (4,
	Move (V_TEMP 0) (Var R_RAX) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8000000000000000 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RAX (Unknown 64)) (Move R_RAX (BinOp OP_MINUS (Word 0x3f 64) (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1ba744: BSR RSI,RSI *)
| 0x1ba744 => Some (4,
	Move (V_TEMP 0) (Var R_RSI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8000000000000000 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RSI (Unknown 64)) (Move R_RSI (BinOp OP_MINUS (Word 0x3f 64) (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1ba93a: BSR RAX,RSI *)
| 0x1ba93a => Some (4,
	Move (V_TEMP 0) (Var R_RSI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8000000000000000 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RAX (Unknown 64)) (Move R_RAX (BinOp OP_MINUS (Word 0x3f 64) (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1ba98a: BSF EAX,EDX *)
| 0x1ba98a => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
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
(* 0x1ba9d2: BSF RAX,RDX *)
| 0x1ba9d2 => Some (4,
	Move (V_TEMP 0) (Var R_RDX) $;
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
(* 0x1bfa88: BSF RDX,RCX *)
| 0x1bfa88 => Some (4,
	Move (V_TEMP 0) (Var R_RCX) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RDX (Unknown 64)) (Move R_RDX (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x1c422a: BSF RAX,R8 *)
| 0x1c422a => Some (4,
	Move (V_TEMP 0) (Var R_R8) $;
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
(* 0x1c4455: BSF RCX,R8 *)
| 0x1c4455 => Some (4,
	Move (V_TEMP 0) (Var R_R8) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RCX (Unknown 64)) (Move R_RCX (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x2989f6: TZCNT EDX,ECX *)
| 0x2989f6 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RCX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 32)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x298b73: TZCNT ECX,EDI *)
| 0x298b73 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDI)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 32)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x298b9c: TZCNT EDI,ECX *)
| 0x298b9c => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RCX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 32)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x298bd8: TZCNT ECX,ESI *)
| 0x298bd8 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RSI)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 32)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x298c42: TZCNT RCX,RDI *)
| 0x298c42 => Some (5,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 64)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_RCX (Var (V_TEMP 2)) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x299376: TZCNT EAX,EAX *)
| 0x299376 => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RAX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 32)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x29952b: TZCNT RAX,RAX *)
| 0x29952b => Some (5,
	Move (V_TEMP 0) (Var R_RAX) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 64)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_RAX (Var (V_TEMP 2)) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x299c5b: TZCNT ECX,ECX *)
| 0x299c5b => Some (4,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RCX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 32)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x29e170: BSF EDX,ECX *)
| 0x29e170 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RCX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) (Move R_RDX (Unknown 64)) (Move R_RDX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x29e1c6: BSF EDX,EDX *)
| 0x29e1c6 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RDX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) (Move R_RDX (Unknown 64)) (Move R_RDX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x2ae9d8: BSF ECX,ECX *)
| 0x2ae9d8 => Some (3,
	Move (V_TEMP 0) (Extract 31 0 (Var R_RCX)) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 32) $;
	Rep (Word 0x20 32) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x20 32)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 32)) (Word 0x0 32))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 32)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 32))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 32)) (Move R_RCX (Unknown 64)) (Move R_RCX (Cast CAST_UNSIGNED 64 (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e28_hot_scans_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

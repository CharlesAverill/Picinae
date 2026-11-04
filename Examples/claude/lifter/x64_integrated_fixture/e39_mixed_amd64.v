(* Strict AMD64 scalar/copy256/REP/scan composition, Ghidra 11.4.2 raw SLEIGH pcode.
Source kind: synthetic; ELF SHA256: f376e400aa6c65f45141bad5d8a3cc5c7bd41c6ff369613705554cfee9e3a6f9
Symbol: mixed; global entry: 0x101000; selected: mixed
Profile: integrated-cet-disabled;bmi1=present;abm=present (CET-enabled execution is outside this model).
Global memory/return addresses; instruction-local temporaries; staticMemory=False.
Closed selected instruction boundaries, dynamic RET targets remain an ABI boundary.
Low256 vector state; CPU/OS vector enabled; nonfaulting/aligned memory as required.
REP successful sequential completion; NT sequential bytes only; undefined scan outputs Unknown.
No faults, interrupts, cache/order/timing, upper>256 or CET execution claim.
Engineering typing only; no functional correctness or lifter soundness claim. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e39_mixed_amd64 : program := fun _ a => match a with
(* 0x101000: ENDBR64 *)
| 0x101000 => Some (4,
	Nop
)
(* 0x101004: MOVDQU XMM0,xmmword ptr [RSI] *)
| 0x101004 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Load (Var V_MEM64) (Var R_RSI) LittleE 16))
)
(* 0x101008: MOVUPS XMM0,XMM0 *)
| 0x101008 => Some (3,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Extract 127 0 (Var R_YMM0)))
)
(* 0x10100b: VMOVDQU XMM0,XMM0 *)
| 0x10100b => Some (4,
	Move R_YMM0 (Cast CAST_UNSIGNED 256 (Extract 127 0 (Var R_YMM0)))
)
(* 0x10100f: VMOVDQU YMM1,YMM0 *)
| 0x10100f => Some (4,
	Move R_YMM1 (Var R_YMM0)
)
(* 0x101013: MOV RCX,RDX *)
| 0x101013 => Some (3,
	Move R_RCX (Var R_RDX)
)
(* 0x101016: MOVSB.REP RDI,RSI *)
| 0x101016 => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RSI) $;
	Move (V_TEMP 5) (BinOp OP_PLUS (Var R_RSI) (Word 0x1 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 7) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 6))) $;
	Move R_RSI (BinOp OP_MINUS (Var (V_TEMP 5)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 8) (Load (Var V_MEM64) (Var (V_TEMP 4)) LittleE 1) $;
	Move (V_TEMP 9) (Var (V_TEMP 8)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 9)) LittleE 1))
)
(* 0x101018: BSF RDI,RDI *)
| 0x101018 => Some (4,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RDI (Unknown 64)) (Move R_RDI (Var (V_TEMP 2))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x10101c: JZ 0x0010102a *)
| 0x10101c => Some (2,
	If (BinOp OP_NEQ (Cast CAST_UNSIGNED 8 (Var R_ZF)) (Word 0x0 8)) (Jmp (Word 0x10102a 64)) (Nop)
)
(* 0x10101e: TZCNT RSI,RSI *)
| 0x10101e => Some (5,
	Move (V_TEMP 0) (Var R_RSI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x1 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_RSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 64)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_RSI (Var (V_TEMP 2)) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x101023: LZCNT RDI,RDI *)
| 0x101023 => Some (5,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8000000000000000 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 2)) (Word 0x0 64)) $;
	Move R_CF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_RDI (Var (V_TEMP 2)) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x101028: JMP 0x00101034 *)
| 0x101028 => Some (2,
	Jmp (Word 0x101034 64)
)
(* 0x10102a: MOV RCX,RDX *)
| 0x10102a => Some (3,
	Move R_RCX (Var R_RDX)
)
(* 0x10102d: STOSQ.REP RDI *)
| 0x10102d => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 8))
)
(* 0x101030: BSR RDI,RDI *)
| 0x101030 => Some (4,
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (Var (V_TEMP 0)) $;
	Move (V_TEMP 2) (Word 0x0 64) $;
	Rep (Word 0x40 64) (If (BinOp OP_AND (BinOp OP_LT (Var (V_TEMP 2)) (Word 0x40 64)) (BinOp OP_EQ (BinOp OP_AND (Var (V_TEMP 1)) (Word 0x8000000000000000 64)) (Word 0x0 64))) (Move (V_TEMP 2) (BinOp OP_PLUS (Var (V_TEMP 2)) (Word 0x1 64)) $;
	Move (V_TEMP 1) (BinOp OP_LSHIFT (Var (V_TEMP 1)) (Word 0x1 64))) Nop) $;
	Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) $;
	Move R_CF (Unknown 1) $;
	If (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0x0 64)) (Move R_RDI (Unknown 64)) (Move R_RDI (BinOp OP_MINUS (Word 0x3f 64) (Var (V_TEMP 2)))) $;
	Move R_OF (Unknown 1) $;
	Move R_SF (Unknown 1) $;
	Move R_AF (Unknown 1) $;
	Move R_PF (Unknown 1)
)
(* 0x101034: VZEROUPPER *)
| 0x101034 => Some (3,
	Move R_YMM0 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM0))) $;
	Move R_YMM1 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM1))) $;
	Move R_YMM2 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM2))) $;
	Move R_YMM3 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM3))) $;
	Move R_YMM4 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM4))) $;
	Move R_YMM5 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM5))) $;
	Move R_YMM6 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM6))) $;
	Move R_YMM7 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM7))) $;
	Move R_YMM8 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM8))) $;
	Move R_YMM9 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM9))) $;
	Move R_YMM10 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM10))) $;
	Move R_YMM11 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM11))) $;
	Move R_YMM12 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM12))) $;
	Move R_YMM13 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM13))) $;
	Move R_YMM14 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM14))) $;
	Move R_YMM15 (Concat (Word 0x0 128) (Extract 127 0 (Var R_YMM15)))
)
(* 0x101037: RET *)
| 0x101037 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e39_mixed_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

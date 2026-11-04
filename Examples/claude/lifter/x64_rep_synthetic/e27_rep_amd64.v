(* Exact REP MOVS/STOS instruction fragments, Ghidra 11.4.2 raw SLEIGH pcode.
Source: synthetic; ELF SHA256: d7a43cba073f6aced58af05e8d31498a0a31cdcaafcda8316f1507fee0d59234; image base: 0x100000.
Selection: rep_fixture; profile: strict.
All addresses global. Deliberately open program: fallthroughs are NOT selected.
Successful sequential completion only; no fault/restart/interrupt/atomicity model.
Rep snapshots entry RCX; original ordered iteration body repeats RCX times,
including zero. 64-bit modular addresses, DF +/- element width, sequential
load-before-store alias behavior; flags untouched. No comparison REP forms.
Typing only: no functional correctness or lifter soundness theorem. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e27_rep_amd64 : program := fun _ a => match a with
(* 0x101000: MOVSB.REP RDI,RSI *)
| 0x101000 => Some (2,
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
(* 0x101003: MOVSW.REP RDI,RSI *)
| 0x101003 => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x2 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x4 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RSI) $;
	Move (V_TEMP 5) (BinOp OP_PLUS (Var R_RSI) (Word 0x2 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 7) (BinOp OP_TIMES (Word 0x4 64) (Var (V_TEMP 6))) $;
	Move R_RSI (BinOp OP_MINUS (Var (V_TEMP 5)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 8) (Load (Var V_MEM64) (Var (V_TEMP 4)) LittleE 2) $;
	Move (V_TEMP 9) (Var (V_TEMP 8)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 9)) LittleE 2))
)
(* 0x101007: MOVSD.REP RDI,RSI *)
| 0x101007 => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x8 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RSI) $;
	Move (V_TEMP 5) (BinOp OP_PLUS (Var R_RSI) (Word 0x4 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 7) (BinOp OP_TIMES (Word 0x8 64) (Var (V_TEMP 6))) $;
	Move R_RSI (BinOp OP_MINUS (Var (V_TEMP 5)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 8) (Load (Var V_MEM64) (Var (V_TEMP 4)) LittleE 4) $;
	Move (V_TEMP 9) (Var (V_TEMP 8)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 9)) LittleE 4))
)
(* 0x10100a: MOVSQ.REP RDI,RSI *)
| 0x10100a => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RSI) $;
	Move (V_TEMP 5) (BinOp OP_PLUS (Var R_RSI) (Word 0x8 64)) $;
	Move (V_TEMP 6) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 7) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 6))) $;
	Move R_RSI (BinOp OP_MINUS (Var (V_TEMP 5)) (Var (V_TEMP 7))) $;
	Move (V_TEMP 8) (Load (Var V_MEM64) (Var (V_TEMP 4)) LittleE 8) $;
	Move (V_TEMP 9) (Var (V_TEMP 8)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 9)) LittleE 8))
)
(* 0x10100e: STOSB.REP RDI *)
| 0x10100e => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x101011: STOSW.REP RDI *)
| 0x101011 => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x2 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x4 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 15 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 2))
)
(* 0x101015: STOSD.REP RDI *)
| 0x101015 => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x4 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x8 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 31 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 4))
)
(* 0x101018: STOSQ.REP RDI *)
| 0x101018 => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 8))
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e27_rep_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

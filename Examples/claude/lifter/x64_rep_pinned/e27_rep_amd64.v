(* Exact REP MOVS/STOS instruction fragments, Ghidra 11.4.2 raw SLEIGH pcode.
Source: glibc; ELF SHA256: 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9; image base: 0x100000.
Selection: pinned_rep_sites; profile: strict.
All addresses global. Deliberately open program: fallthroughs are NOT selected.
Successful sequential completion only; no fault/restart/interrupt/atomicity model.
Rep snapshots entry RCX; original ordered iteration body repeats RCX times,
including zero. 64-bit modular addresses, DF +/- element width, sequential
load-before-store alias behavior; flags untouched. No comparison REP forms.
Typing only: no functional correctness or lifter soundness theorem. *)
Require Import Picinae_amd64 NArith.
Open Scope N.
Definition e27_rep_amd64 : program := fun _ a => match a with
(* 0x1a909e: STOSQ.REP RDI *)
| 0x1a909e => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 8))
)
(* 0x1aad40: STOSQ.REP RDI *)
| 0x1aad40 => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 8))
)
(* 0x1c463c: STOSQ.REP RDI *)
| 0x1c463c => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 8))
)
(* 0x1c46ec: STOSQ.REP RDI *)
| 0x1c46ec => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 8))
)
(* 0x1c479c: STOSQ.REP RDI *)
| 0x1c479c => Some (3,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x8 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x10 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Var R_RAX) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 8))
)
(* 0x1c48ff: MOVSB.REP RDI,RSI *)
| 0x1c48ff => Some (2,
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
(* 0x1c490d: MOVSB.REP RDI,RSI *)
| 0x1c490d => Some (2,
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
(* 0x1c4b98: MOVSB.REP RDI,RSI *)
| 0x1c4b98 => Some (2,
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
(* 0x1c4fc7: STOSB.REP RDI *)
| 0x1c4fc7 => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x1c50ba: STOSB.REP RDI *)
| 0x1c50ba => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x2a0ae4: MOVSB.REP RDI,RSI *)
| 0x2a0ae4 => Some (2,
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
(* 0x2a0b4a: MOVSB.REP RDI,RSI *)
| 0x2a0b4a => Some (2,
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
(* 0x2a0fce: STOSB.REP RDI *)
| 0x2a0fce => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x2a10ca: STOSB.REP RDI *)
| 0x2a10ca => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x2a6b7f: MOVSB.REP RDI,RSI *)
| 0x2a6b7f => Some (2,
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
(* 0x2a6bd5: MOVSB.REP RDI,RSI *)
| 0x2a6bd5 => Some (2,
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
(* 0x2a708e: STOSB.REP RDI *)
| 0x2a708e => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x2a713a: STOSB.REP RDI *)
| 0x2a713a => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x2a7f65: MOVSB.REP RDI,RSI *)
| 0x2a7f65 => Some (2,
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
(* 0x2a7fca: MOVSB.REP RDI,RSI *)
| 0x2a7fca => Some (2,
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
(* 0x2a87ce: STOSB.REP RDI *)
| 0x2a87ce => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x2a88ca: STOSB.REP RDI *)
| 0x2a88ca => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x2af12d: MOVSB.REP RDI,RSI *)
| 0x2af12d => Some (2,
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
(* 0x2af18c: MOVSB.REP RDI,RSI *)
| 0x2af18c => Some (2,
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
(* 0x2af9fe: STOSB.REP RDI *)
| 0x2af9fe => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
(* 0x2afaba: STOSB.REP RDI *)
| 0x2afaba => Some (2,
	Rep (Var R_RCX) (Move R_RCX (BinOp OP_MINUS (Var R_RCX) (Word 0x1 64)) $;
	Move (V_TEMP 0) (Var R_RDI) $;
	Move (V_TEMP 1) (BinOp OP_PLUS (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 2) (Cast CAST_UNSIGNED 64 (Cast CAST_UNSIGNED 8 (Var R_DF))) $;
	Move (V_TEMP 3) (BinOp OP_TIMES (Word 0x2 64) (Var (V_TEMP 2))) $;
	Move R_RDI (BinOp OP_MINUS (Var (V_TEMP 1)) (Var (V_TEMP 3))) $;
	Move (V_TEMP 4) (Extract 7 0 (Var R_RAX)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0)) (Var (V_TEMP 4)) LittleE 1))
)
| _ => None
end.
Theorem welltyped : welltyped_prog x64typctx e27_rep_amd64.
Proof. Picinae_typecheck. Qed.
Print Assumptions welltyped.

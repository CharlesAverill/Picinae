(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: wcpncpy
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition wcpncpy_amd64 : program := fun _ a => match a with

(* 0x00165dfa: PUSH R12 *)
(*    1465850: PUSH R12 *)
| 0x165dfa => Some (2,
	Move (V_TEMP 0x27c80) (Var R_R12) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165dfc: PUSH RBP *)
(*    1465852: PUSH RBP *)
| 0x165dfc => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBP) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165dfd: MOV RBP,RDX *)
(*    1465853: MOV RBP,RDX *)
| 0x165dfd => Some (3,
	Move R_RBP (Var R_RDX)
)

(* 0x00165e00: PUSH RBX *)
(*    1465856: PUSH RBX *)
| 0x165e00 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165e01: MOV RBX,RSI *)
(*    1465857: MOV RBX,RSI *)
| 0x165e01 => Some (3,
	Move R_RBX (Var R_RSI)
)

(* 0x00165e04: CALL 0x00134be0 *)
(*    1465860: CALL 0x00134be0 *)
| 0x165e04 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165e09 64)) LittleE 8) $;
	Jmp (Word 0x134be0 64)
)

(* 0x00165e09: MOV RSI,RBP *)
(*    1465865: MOV RSI,RBP *)
| 0x165e09 => Some (3,
	Move R_RSI (Var R_RBP)
)

(* 0x00165e0c: MOV RDI,RBX *)
(*    1465868: MOV RDI,RBX *)
| 0x165e0c => Some (3,
	Move R_RDI (Var R_RBX)
)

(* 0x00165e0f: MOV R12,RAX *)
(*    1465871: MOV R12,RAX *)
| 0x165e0f => Some (3,
	Move R_R12 (Var R_RAX)
)

(* 0x00165e12: CALL 0x00165fa5 *)
(*    1465874: CALL 0x00165fa5 *)
| 0x165e12 => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165e17 64)) LittleE 8) $;
	Jmp (Word 0x165fa5 64)
)

(* 0x00165e17: POP RBX *)
(*    1465879: POP RBX *)
| 0x165e17 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00165e18: POP RBP *)
(*    1465880: POP RBP *)
| 0x165e18 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBP (Var (V_TEMP 0x55200))
)

(* 0x00165e19: LEA RAX,[R12 + RAX*0x4] *)
(*    1465881: LEA RAX,[R12 + RAX*0x4] *)
| 0x165e19 => Some (4,
	Move (V_TEMP 0x4980) (BinOp OP_TIMES (Var R_RAX) (Word 0x4 64)) $;
	Move (V_TEMP 0x4a80) (BinOp OP_PLUS (Var R_R12) (Var (V_TEMP 0x4980))) $;
	Move R_RAX (Var (V_TEMP 0x4a80))
)

(* 0x00165e1d: POP R12 *)
(*    1465885: POP R12 *)
| 0x165e1d => Some (2,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_R12 (Var (V_TEMP 0x55200))
)

(* 0x00165e1f: RET *)
(*    1465887: RET *)
| 0x165e1f => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx wcpncpy_amd64.
Proof. Picinae_typecheck. Qed.

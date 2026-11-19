(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: ns_put32
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ns_put32_amd64 : program := fun _ a => match a with

(* 0x0015ab51: BSWAP EDI *)
(*    1420113: BSWAP EDI *)
| 0x15ab51 => Some (2,
	Move (V_TEMP 0x35100) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff000000 32)) $;
	Move (V_TEMP 0x35200) (BinOp OP_RSHIFT (Var (V_TEMP 0x35100)) (Word 0x18 32)) $;
	Move (V_TEMP 0x35280) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff0000 32)) $;
	Move (V_TEMP 0x35300) (BinOp OP_RSHIFT (Var (V_TEMP 0x35280)) (Word 0x8 32)) $;
	Move (V_TEMP 0x35200) (BinOp OP_OR (Var (V_TEMP 0x35200)) (Var (V_TEMP 0x35300))) $;
	Move (V_TEMP 0x35400) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff00 32)) $;
	Move (V_TEMP 0x35480) (BinOp OP_LSHIFT (Var (V_TEMP 0x35400)) (Word 0x8 32)) $;
	Move (V_TEMP 0x35200) (BinOp OP_OR (Var (V_TEMP 0x35200)) (Var (V_TEMP 0x35480))) $;
	Move (V_TEMP 0x35580) (BinOp OP_AND (Extract 31 0 (Var R_RDI)) (Word 0xff 32)) $;
	Move (V_TEMP 0x35600) (BinOp OP_LSHIFT (Var (V_TEMP 0x35580)) (Word 0x18 32)) $;
	Move R_RDI (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_OR (Var (V_TEMP 0x35200)) (Var (V_TEMP 0x35600)))) (Word 0 64)) (BinOp OP_AND (Var R_RDI) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RDI (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI)))
)

(* 0x0015ab53: MOV dword ptr [RSI],EDI *)
(*    1420115: MOV dword ptr [RSI],EDI *)
| 0x15ab53 => Some (2,
	Move (V_TEMP 0x6a00) (Extract 31 0 (Var R_RDI)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSI) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x6a00))) LittleE 4)
)

(* 0x0015ab55: RET *)
(*    1420117: RET *)
| 0x15ab55 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx ns_put32_amd64.
Proof. Picinae_typecheck. Qed.

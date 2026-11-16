(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: htonl
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition htonl_amd64 : program := fun _ a => match a with

(* 0x00159de7: MOV EAX,EDI *)
(*    1416679: MOV EAX,EDI *)
| 0x159de7 => Some (2,
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00159de9: BSWAP EAX *)
(*    1416681: BSWAP EAX *)
| 0x159de9 => Some (2,
	Move (V_TEMP 0x35100) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff000000 32)) $;
	Move (V_TEMP 0x35200) (BinOp OP_RSHIFT (Var (V_TEMP 0x35100)) (Word 0x18 32)) $;
	Move (V_TEMP 0x35280) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff0000 32)) $;
	Move (V_TEMP 0x35300) (BinOp OP_RSHIFT (Var (V_TEMP 0x35280)) (Word 0x8 32)) $;
	Move (V_TEMP 0x35200) (BinOp OP_OR (Var (V_TEMP 0x35200)) (Var (V_TEMP 0x35300))) $;
	Move (V_TEMP 0x35400) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff00 32)) $;
	Move (V_TEMP 0x35480) (BinOp OP_LSHIFT (Var (V_TEMP 0x35400)) (Word 0x8 32)) $;
	Move (V_TEMP 0x35200) (BinOp OP_OR (Var (V_TEMP 0x35200)) (Var (V_TEMP 0x35480))) $;
	Move (V_TEMP 0x35580) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x35600) (BinOp OP_LSHIFT (Var (V_TEMP 0x35580)) (Word 0x18 32)) $;
	Move R_RAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 64 (BinOp OP_OR (Var (V_TEMP 0x35200)) (Var (V_TEMP 0x35600)))) (Word 0 64)) (BinOp OP_AND (Var R_RAX) (Word 0xFFFFFFFF00000000 64))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00159deb: RET *)
(*    1416683: RET *)
| 0x159deb => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx htonl_amd64.
Proof. Picinae_typecheck. Qed.

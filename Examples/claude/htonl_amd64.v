(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: htonl
entry: 0x236610 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition htonl_amd64 : program := fun _ a => match a with

(* 0x00236610: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00236614: MOV EAX,EDI *)
(*          4: MOV EAX,EDI *)
| 0x4 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00236616: BSWAP EAX *)
(*          6: BSWAP EAX *)
| 0x6 => Some (2,
	Move (V_TEMP 0x35200) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff000000 32)) $;
	Move (V_TEMP 0x35300) (BinOp OP_RSHIFT (Var (V_TEMP 0x35200)) (Word 24 32)) $;
	Move (V_TEMP 0x35380) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff0000 32)) $;
	Move (V_TEMP 0x35400) (BinOp OP_RSHIFT (Var (V_TEMP 0x35380)) (Word 8 32)) $;
	Move (V_TEMP 0x35300) (BinOp OP_OR (Var (V_TEMP 0x35300)) (Var (V_TEMP 0x35400))) $;
	Move (V_TEMP 0x35500) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff00 32)) $;
	Move (V_TEMP 0x35580) (BinOp OP_LSHIFT (Var (V_TEMP 0x35500)) (Word 8 32)) $;
	Move (V_TEMP 0x35300) (BinOp OP_OR (Var (V_TEMP 0x35300)) (Var (V_TEMP 0x35580))) $;
	Move (V_TEMP 0x35680) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x35700) (BinOp OP_LSHIFT (Var (V_TEMP 0x35680)) (Word 24 32)) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (BinOp OP_OR (Var (V_TEMP 0x35300)) (Var (V_TEMP 0x35700)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00236618: RET *)
(*          8: RET *)
| 0x8 => Some (1,
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


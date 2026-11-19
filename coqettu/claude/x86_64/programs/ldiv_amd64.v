(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: ldiv
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ldiv_amd64 : program := fun _ a => match a with

(* 0x0016500a: MOV RAX,RDI *)
(*    1462282: MOV RAX,RDI *)
| 0x16500a => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x0016500d: CQO *)
(*    1462285: CQO *)
| 0x16500d => Some (2,
	Move (V_TEMP 0x3d780) (Cast CAST_SIGNED 128 (Var R_RAX)) $;
	Move R_RDX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x3d780)) (Word 64 128)))
)

(* 0x0016500f: IDIV RSI *)
(*    1462287: IDIV RSI *)
| 0x16500f => Some (3,
	Move (V_TEMP 0x49c80) (Cast CAST_SIGNED 128 (Var R_RSI)) $;
	Move (V_TEMP 0x49d00) (Cast CAST_UNSIGNED 128 (Var R_RDX)) $;
	Move (V_TEMP 0x49d80) (BinOp OP_LSHIFT (Var (V_TEMP 0x49d00)) (Word 0x40 128)) $;
	Move (V_TEMP 0x49e00) (Cast CAST_UNSIGNED 128 (Var R_RAX)) $;
	Move (V_TEMP 0x49f00) (BinOp OP_OR (Var (V_TEMP 0x49d80)) (Var (V_TEMP 0x49e00))) $;
	Move (V_TEMP 0x4a000) (BinOp OP_SDIVIDE (Var (V_TEMP 0x49f00)) (Var (V_TEMP 0x49c80))) $;
	Move R_RAX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4a000)) (Word 0 128))) $;
	Move (V_TEMP 0x4a180) (BinOp OP_SMOD (Var (V_TEMP 0x49f00)) (Var (V_TEMP 0x49c80))) $;
	Move R_RDX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4a180)) (Word 0 128)))
)

(* 0x00165012: RET *)
(*    1462290: RET *)
| 0x165012 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx ldiv_amd64.
Proof. Picinae_typecheck. Qed.

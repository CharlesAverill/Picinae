(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: ldiv
entry: 0x145e20 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition ldiv_amd64 : program := fun _ a => match a with

(* 0x00145e20: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00145e24: MOV RAX,RDI *)
(*          4: MOV RAX,RDI *)
| 0x4 => Some (3,
	Move R_RAX (Var R_RDI)
)

(* 0x00145e27: CQO *)
(*          7: CQO *)
| 0x7 => Some (2,
	Move (V_TEMP 0x3d880) (Cast CAST_SIGNED 128 (Var R_RAX)) $;
	Move R_RDX (Extract 127 64 (Var (V_TEMP 0x3d880)))
)

(* 0x00145e29: IDIV RSI *)
(*          9: IDIV RSI *)
| 0x9 => Some (3,
	Move (V_TEMP 0x49d80) (Cast CAST_SIGNED 128 (Var R_RSI)) $;
	Move (V_TEMP 0x49e00) (Cast CAST_UNSIGNED 128 (Var R_RDX)) $;
	Move (V_TEMP 0x49e80) (BinOp OP_LSHIFT (Var (V_TEMP 0x49e00)) (Word 64 128)) $;
	Move (V_TEMP 0x49f00) (Cast CAST_UNSIGNED 128 (Var R_RAX)) $;
	Move (V_TEMP 0x4a000) (BinOp OP_OR (Var (V_TEMP 0x49e80)) (Var (V_TEMP 0x49f00))) $;
	Move (V_TEMP 0x4a100) (BinOp OP_SDIVIDE (Var (V_TEMP 0x4a000)) (Var (V_TEMP 0x49d80))) $;
	Move R_RAX (Extract 63 0 (Var (V_TEMP 0x4a100))) $;
	Move (V_TEMP 0x4a280) (BinOp OP_SMOD (Var (V_TEMP 0x4a000)) (Var (V_TEMP 0x49d80))) $;
	Move R_RDX (Extract 63 0 (Var (V_TEMP 0x4a280)))
)

(* 0x00145e2c: RET *)
(*         12: RET *)
| 0xc => Some (1,
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


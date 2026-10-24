(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: htons
entry: 0x236620 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition htons_amd64 : program := fun _ a => match a with

(* 0x00236620: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00236624: MOV EAX,EDI *)
(*          4: MOV EAX,EDI *)
| 0x4 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00236626: ROL AX,0x8 *)
(*          6: ROL AX,0x8 *)
| 0x6 => Some (4,
	Move (V_TEMP 0x62d80) (BinOp OP_AND (Word 0x8 32) (Word 0xf 32)) $;
	Move (V_TEMP 0x62e00) (Ite (BinOp OP_LT (Var (V_TEMP 0x62d80)) (Word 16 32)) (BinOp OP_LSHIFT (Extract 15 0 (Var R_RAX)) (Cast CAST_LOW 16 (Var (V_TEMP 0x62d80)))) (BinOp OP_LSHIFT (Extract 15 0 (Var R_RAX)) (Word 16 16))) $;
	Move (V_TEMP 0x62e80) (BinOp OP_MINUS (Word 0x10 32) (Var (V_TEMP 0x62d80))) $;
	Move (V_TEMP 0x62f00) (Ite (BinOp OP_LT (Var (V_TEMP 0x62e80)) (Word 16 32)) (BinOp OP_RSHIFT (Extract 15 0 (Var R_RAX)) (Cast CAST_LOW 16 (Var (V_TEMP 0x62e80)))) (BinOp OP_RSHIFT (Extract 15 0 (Var R_RAX)) (Word 16 16))) $;
	Move R_RAX (Concat (Extract 63 16 (Var R_RAX)) (BinOp OP_OR (Var (V_TEMP 0x62e00)) (Var (V_TEMP 0x62f00)))) $;
	Move (V_TEMP 0x63000) (BinOp OP_AND (Word 0x8 8) (Word 0x1f 8)) $;
	Move (V_TEMP 0x2d400) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x63000)) (Word 0x0 8))) $;
	Move (V_TEMP 0x2d480) (BinOp OP_AND (Extract 15 0 (Var R_RAX)) (Word 0x1 16)) $;
	Move (V_TEMP 0x2d580) (Cast CAST_UNSIGNED 8 (BinOp OP_NEQ (Var (V_TEMP 0x2d480)) (Word 0x0 16))) $;
	Move (V_TEMP 0x2d600) (BinOp OP_XOR (Var (V_TEMP 0x2d400)) (Word 1 8)) $;
	Move (V_TEMP 0x2d680) (BinOp OP_AND (Var (V_TEMP 0x2d600)) (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x2d700) (BinOp OP_AND (Var (V_TEMP 0x2d400)) (Var (V_TEMP 0x2d580))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2d680)) (Var (V_TEMP 0x2d700)))) $;
	Move (V_TEMP 0x2d880) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 0x63000)) (Word 0x1 8))) $;
	Move (V_TEMP 0x2d900) (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Extract 15 0 (Var R_RAX)) (Word 0x0 16))) $;
	Move (V_TEMP 0x2da00) (BinOp OP_XOR (Cast CAST_UNSIGNED 8 (Var R_CF)) (Var (V_TEMP 0x2d900))) $;
	Move (V_TEMP 0x2da80) (BinOp OP_XOR (Var (V_TEMP 0x2d880)) (Word 1 8)) $;
	Move (V_TEMP 0x2db00) (BinOp OP_AND (Var (V_TEMP 0x2da80)) (Cast CAST_UNSIGNED 8 (Var R_OF))) $;
	Move (V_TEMP 0x2db80) (BinOp OP_AND (Var (V_TEMP 0x2d880)) (Var (V_TEMP 0x2da00))) $;
	Move R_OF (Cast CAST_LOW 1 (BinOp OP_OR (Var (V_TEMP 0x2db00)) (Var (V_TEMP 0x2db80))))
)

(* 0x0023662a: RET *)
(*         10: RET *)
| 0xa => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx htons_amd64.
Proof. Picinae_typecheck. Qed.


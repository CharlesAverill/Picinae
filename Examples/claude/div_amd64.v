(* Automatically generated with pcode2coq
arch: amd64
file: libc.so.6
function: div
entry: 0x145e00 (lifted with entry rebased to 0)
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition div_amd64 : program := fun _ a => match a with

(* 0x00145e00: ENDBR64 *)
(*          0: ENDBR64 *)
| 0x0 => Some (4,
	Nop
)

(* 0x00145e04: MOV EAX,EDI *)
(*          4: MOV EAX,EDI *)
| 0x4 => Some (2,
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00145e06: CDQ *)
(*          6: CDQ *)
| 0x6 => Some (1,
	Move (V_TEMP 0x3d700) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Extract 63 32 (Var (V_TEMP 0x3d700)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00145e07: IDIV ESI *)
(*          7: IDIV ESI *)
| 0x7 => Some (2,
	Move (V_TEMP 0x49700) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RSI))) $;
	Move (V_TEMP 0x49780) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move (V_TEMP 0x49800) (BinOp OP_LSHIFT (Var (V_TEMP 0x49780)) (Word 32 64)) $;
	Move (V_TEMP 0x49880) (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x49980) (BinOp OP_OR (Var (V_TEMP 0x49800)) (Var (V_TEMP 0x49880))) $;
	Move (V_TEMP 0x49a80) (BinOp OP_SDIVIDE (Var (V_TEMP 0x49980)) (Var (V_TEMP 0x49700))) $;
	Move R_RAX (Concat (Extract 63 32 (Var R_RAX)) (Extract 31 0 (Var (V_TEMP 0x49a80)))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x49c00) (BinOp OP_SMOD (Var (V_TEMP 0x49980)) (Var (V_TEMP 0x49700))) $;
	Move R_RDX (Concat (Extract 63 32 (Var R_RDX)) (Extract 31 0 (Var (V_TEMP 0x49c00)))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00145e09: MOVD XMM0,EAX *)
(*          9: MOVD XMM0,EAX *)
| 0x9 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Cast CAST_UNSIGNED 128 (Extract 31 0 (Var R_RAX))))
)

(* 0x00145e0d: MOVD XMM1,EDX *)
(*         13: MOVD XMM1,EDX *)
| 0xd => Some (4,
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Cast CAST_UNSIGNED 128 (Extract 31 0 (Var R_RDX))))
)

(* 0x00145e11: PUNPCKLDQ XMM0,XMM1 *)
(*         17: PUNPCKLDQ XMM0,XMM1 *)
| 0x11 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (Extract 63 32 (Var R_YMM1)) (Extract 95 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (Extract 63 32 (Var R_YMM0)) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (Extract 31 0 (Var R_YMM1)) (Extract 31 0 (Var R_YMM0))))
)

(* 0x00145e15: MOVQ RAX,XMM0 *)
(*         21: MOVQ RAX,XMM0 *)
| 0x15 => Some (5,
	Move R_RAX (Extract 63 0 (Extract 127 0 (Var R_YMM0)))
)

(* 0x00145e1a: RET *)
(*         26: RET *)
| 0x1a => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx div_amd64.
Proof. Picinae_typecheck. Qed.


(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: copysignf at 0x141810
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition copysignf_amd64 : program := fun _ a => match a with

(* ---- copysignf ---- *)

(* 0x00141810: ENDBR64 *)
(*    1316880: ENDBR64 *)
| 0x141810 => Some (4,
	Nop
)

(* 0x00141814: MOVSS XMM3,dword ptr [0x002cc880] *)
(*    1316884: MOVSS XMM3,dword ptr [0x002cc880] *)
| 0x141814 => Some (8,
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (Load (Var V_MEM64) (Word 0x2cc880 64) LittleE 4)) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (Word 0x0 32) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (Word 0x0 32) (Extract 63 0 (Var R_YMM3)))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (Word 0x0 32) (Extract 95 0 (Var R_YMM3))))
)

(* 0x0014181c: ANDPS XMM0,XMM3 *)
(*    1316892: ANDPS XMM0,XMM3 *)
| 0x14181c => Some (3,
	Move R_YMM0 (Concat (Extract 255 32 (Var R_YMM0)) (BinOp OP_AND (Extract 31 0 (Var R_YMM0)) (Extract 31 0 (Var R_YMM3)))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (Concat (BinOp OP_AND (Extract 63 32 (Var R_YMM0)) (Extract 63 32 (Var R_YMM3))) (Extract 31 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 96 (Var R_YMM0)) (Concat (BinOp OP_AND (Extract 95 64 (Var R_YMM0)) (Extract 95 64 (Var R_YMM3))) (Extract 63 0 (Var R_YMM0)))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_AND (Extract 127 96 (Var R_YMM0)) (Extract 127 96 (Var R_YMM3))) (Extract 95 0 (Var R_YMM0))))
)

(* 0x0014181f: ANDNPS XMM3,XMM1 *)
(*    1316895: ANDNPS XMM3,XMM1 *)
| 0x14181f => Some (3,
	Move (V_TEMP 0x7ec00) (UnOp OP_NOT (Extract 31 0 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 32 (Var R_YMM3)) (BinOp OP_AND (Var (V_TEMP 0x7ec00)) (Extract 31 0 (Var R_YMM1)))) $;
	Move (V_TEMP 0x7ed00) (UnOp OP_NOT (Extract 63 32 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 64 (Var R_YMM3)) (Concat (BinOp OP_AND (Var (V_TEMP 0x7ed00)) (Extract 63 32 (Var R_YMM1))) (Extract 31 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0x7ee00) (UnOp OP_NOT (Extract 95 64 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 96 (Var R_YMM3)) (Concat (BinOp OP_AND (Var (V_TEMP 0x7ee00)) (Extract 95 64 (Var R_YMM1))) (Extract 63 0 (Var R_YMM3)))) $;
	Move (V_TEMP 0x7ef00) (UnOp OP_NOT (Extract 127 96 (Var R_YMM3))) $;
	Move R_YMM3 (Concat (Extract 255 128 (Var R_YMM3)) (Concat (BinOp OP_AND (Var (V_TEMP 0x7ef00)) (Extract 127 96 (Var R_YMM1))) (Extract 95 0 (Var R_YMM3))))
)

(* 0x00141822: ORPS XMM0,XMM3 *)
(*    1316898: ORPS XMM0,XMM3 *)
| 0x141822 => Some (3,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (BinOp OP_OR (Extract 127 0 (Var R_YMM0)) (Extract 127 0 (Var R_YMM3))))
)

(* 0x00141825: RET *)
(*    1316901: RET *)
| 0x141825 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx copysignf_amd64.
Proof. Picinae_typecheck. Qed.

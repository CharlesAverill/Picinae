(* Automatically generated with pcode2coq (multi-function, global addressing)
arch: amd64
file: libc.so.6
function: copysign at 0x141420
*)

Require Import Picinae_amd64.
Require Import NArith.
Open Scope N.

Definition copysign_amd64 : program := fun _ a => match a with

(* ---- copysign ---- *)

(* 0x00141420: ENDBR64 *)
(*    1315872: ENDBR64 *)
| 0x141420 => Some (4,
	Nop
)

(* 0x00141424: ANDPD XMM0,xmmword ptr [0x002e2090] *)
(*    1315876: ANDPD XMM0,xmmword ptr [0x002e2090] *)
| 0x141424 => Some (8,
	Move (V_TEMP 0x7d600) (Load (Var V_MEM64) (Word 0x2e2090 64) LittleE 16) $;
	Move (V_TEMP 0x7d680) (Extract 63 0 (Var (V_TEMP 0x7d600))) $;
	Move R_YMM0 (Concat (Extract 255 64 (Var R_YMM0)) (BinOp OP_AND (Extract 63 0 (Var R_YMM0)) (Var (V_TEMP 0x7d680)))) $;
	Move (V_TEMP 0x7d780) (Extract 127 64 (Var (V_TEMP 0x7d600))) $;
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (Concat (BinOp OP_AND (Extract 127 64 (Var R_YMM0)) (Var (V_TEMP 0x7d780))) (Extract 63 0 (Var R_YMM0))))
)

(* 0x0014142c: ANDPD XMM1,xmmword ptr [0x002e2080] *)
(*    1315884: ANDPD XMM1,xmmword ptr [0x002e2080] *)
| 0x14142c => Some (8,
	Move (V_TEMP 0x7d600) (Load (Var V_MEM64) (Word 0x2e2080 64) LittleE 16) $;
	Move (V_TEMP 0x7d680) (Extract 63 0 (Var (V_TEMP 0x7d600))) $;
	Move R_YMM1 (Concat (Extract 255 64 (Var R_YMM1)) (BinOp OP_AND (Extract 63 0 (Var R_YMM1)) (Var (V_TEMP 0x7d680)))) $;
	Move (V_TEMP 0x7d780) (Extract 127 64 (Var (V_TEMP 0x7d600))) $;
	Move R_YMM1 (Concat (Extract 255 128 (Var R_YMM1)) (Concat (BinOp OP_AND (Extract 127 64 (Var R_YMM1)) (Var (V_TEMP 0x7d780))) (Extract 63 0 (Var R_YMM1))))
)

(* 0x00141434: ORPD XMM0,XMM1 *)
(*    1315892: ORPD XMM0,XMM1 *)
| 0x141434 => Some (4,
	Move R_YMM0 (Concat (Extract 255 128 (Var R_YMM0)) (BinOp OP_OR (Extract 127 0 (Var R_YMM0)) (Extract 127 0 (Var R_YMM1))))
)

(* 0x00141438: RET *)
(*    1315896: RET *)
| 0x141438 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

Theorem welltyped: welltyped_prog x64typctx copysign_amd64.
Proof. Picinae_typecheck. Qed.

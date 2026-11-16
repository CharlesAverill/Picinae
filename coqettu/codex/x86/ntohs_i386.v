(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: ntohs
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ntohs_i386 : program := fun _ a => match a with

(* 0x00069efe: MOV EAX,dword ptr [ESP + 0x4] *)
(*     433918: MOV EAX,dword ptr [ESP + 0x4] *)
| 0x69efe => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x4 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x00069f02: ROL AX,0x8 *)
(*     433922: ROL AX,0x8 *)
| 0x69f02 => Some (4,
	Move (V_TEMP 0x4d680) (BinOp OP_AND (Word 0x8 32) (Word 0xf 32)) $;
	Move (V_TEMP 0x4d700) (BinOp OP_LSHIFT (Extract 15 0 (Var R_EAX)) (Cast CAST_LOW 16 (Var (V_TEMP 0x4d680)))) $;
	Move (V_TEMP 0x4d780) (BinOp OP_MINUS (Word 0x10 32) (Var (V_TEMP 0x4d680))) $;
	Move (V_TEMP 0x4d800) (BinOp OP_RSHIFT (Extract 15 0 (Var R_EAX)) (Cast CAST_LOW 16 (Var (V_TEMP 0x4d780)))) $;
	Move R_EAX (BinOp OP_OR (BinOp OP_LSHIFT (Cast CAST_UNSIGNED 32 (BinOp OP_OR (Var (V_TEMP 0x4d700)) (Var (V_TEMP 0x4d800)))) (Word 0 32)) (BinOp OP_AND (Var R_EAX) (Word 0xFFFF0000 32))) $;
	Move (V_TEMP 0x4d900) (BinOp OP_AND (Word 0x8 8) (Word 0x1f 8)) $;
	Move (V_TEMP 0x25d80) (BinOp OP_NEQ (Var (V_TEMP 0x4d900)) (Word 0x0 8)) $;
	Move (V_TEMP 0x25e00) (BinOp OP_AND (Extract 15 0 (Var R_EAX)) (Word 0x1 16)) $;
	Move (V_TEMP 0x25f00) (BinOp OP_NEQ (Var (V_TEMP 0x25e00)) (Word 0x0 16)) $;
	Move (V_TEMP 0x25f80) (UnOp OP_NOT (Var (V_TEMP 0x25d80))) $;
	Move (V_TEMP 0x26000) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x25f80)) (Var R_CF))) $;
	Move (V_TEMP 0x26080) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x25d80)) (Var (V_TEMP 0x25f00)))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x26000))) (Cast CAST_LOW 1 (Var (V_TEMP 0x26080)))))) $;
	Move (V_TEMP 0x26200) (BinOp OP_EQ (Var (V_TEMP 0x4d900)) (Word 0x1 8)) $;
	Move (V_TEMP 0x26280) (BinOp OP_SLT (Extract 15 0 (Var R_EAX)) (Word 0x0 16)) $;
	Move (V_TEMP 0x26380) (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Var R_CF) (Var (V_TEMP 0x26280)))) $;
	Move (V_TEMP 0x26400) (UnOp OP_NOT (Var (V_TEMP 0x26200))) $;
	Move (V_TEMP 0x26480) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x26400)) (Var R_OF))) $;
	Move (V_TEMP 0x26500) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x26200)) (Cast CAST_LOW 1 (Var (V_TEMP 0x26380))))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x26480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x26500))))))
)

(* 0x00069f06: RET *)
(*     433926: RET *)
| 0x69f06 => Some (1,
	Move R_EIP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Jmp (Var R_EIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x86typctx ntohs_i386.
Proof. Picinae_typecheck. Qed.

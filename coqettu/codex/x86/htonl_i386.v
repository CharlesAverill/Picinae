(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: htonl
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition htonl_i386 : program := fun _ a => match a with

(* 0x00068b92: MOV EAX,dword ptr [ESP + 0x4] *)
(*     428946: MOV EAX,dword ptr [ESP + 0x4] *)
| 0x68b92 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x4 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x00068b96: BSWAP EAX *)
(*     428950: BSWAP EAX *)
| 0x68b96 => Some (2,
	Move (V_TEMP 0x2d000) (BinOp OP_AND (Var R_EAX) (Word 0xff000000 32)) $;
	Move (V_TEMP 0x2d100) (BinOp OP_RSHIFT (Var (V_TEMP 0x2d000)) (Word 0x18 32)) $;
	Move (V_TEMP 0x2d180) (BinOp OP_AND (Var R_EAX) (Word 0xff0000 32)) $;
	Move (V_TEMP 0x2d200) (BinOp OP_RSHIFT (Var (V_TEMP 0x2d180)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2d100) (BinOp OP_OR (Var (V_TEMP 0x2d100)) (Var (V_TEMP 0x2d200))) $;
	Move (V_TEMP 0x2d300) (BinOp OP_AND (Var R_EAX) (Word 0xff00 32)) $;
	Move (V_TEMP 0x2d380) (BinOp OP_LSHIFT (Var (V_TEMP 0x2d300)) (Word 0x8 32)) $;
	Move (V_TEMP 0x2d100) (BinOp OP_OR (Var (V_TEMP 0x2d100)) (Var (V_TEMP 0x2d380))) $;
	Move (V_TEMP 0x2d480) (BinOp OP_AND (Var R_EAX) (Word 0xff 32)) $;
	Move (V_TEMP 0x2d500) (BinOp OP_LSHIFT (Var (V_TEMP 0x2d480)) (Word 0x18 32)) $;
	Move R_EAX (BinOp OP_OR (Var (V_TEMP 0x2d100)) (Var (V_TEMP 0x2d500)))
)

(* 0x00068b98: RET *)
(*     428952: RET *)
| 0x68b98 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx htonl_i386.
Proof. Picinae_typecheck. Qed.

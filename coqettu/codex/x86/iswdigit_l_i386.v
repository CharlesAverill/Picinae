(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: iswdigit_l
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition iswdigit_l_i386 : program := fun _ a => match a with

(* 0x0004f366: PUSH EBX *)
(*     324454: PUSH EBX *)
| 0x4f366 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0004f367: CALL 0x0004a842 *)
(*     324455: CALL 0x0004a842 *)
| 0x4f367 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x4f36c 32)) LittleE 4) $;
	Jmp (Word 0x4a842 32)
)

(* 0x0004f36c: ADD EBX,0x65c30 *)
(*     324460: ADD EBX,0x65c30 *)
| 0x4f36c => Some (6,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EBX) (Word 0x65c30 32)) (Var R_EBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EBX) (Word 0x65c30 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x65c30 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EBX (BinOp OP_PLUS (Var R_EBX) (Word 0x65c30 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EBX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EBX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EBX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f372: SUB ESP,0x14 *)
(*     324466: SUB ESP,0x14 *)
| 0x4f372 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_ESP) (Word 0x14 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0x14 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0x14 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x14 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x14 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f375: PUSH dword ptr [ESP + 0x1c] *)
(*     324469: PUSH dword ptr [ESP + 0x1c] *)
| 0x4f375 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x1c 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move (V_TEMP 0x20a80) (Var (V_TEMP 0xb900)) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0004f379: CALL 0x0004f355 *)
(*     324473: CALL 0x0004f355 *)
| 0x4f379 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x4f37e 32)) LittleE 4) $;
	Jmp (Word 0x4f355 32)
)

(* 0x0004f37e: ADD ESP,0x18 *)
(*     324478: ADD ESP,0x18 *)
| 0x4f37e => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_ESP) (Word 0x18 32)) (Var R_ESP))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_ESP) (Word 0x18 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x18 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x18 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f381: POP EBX *)
(*     324481: POP EBX *)
| 0x4f381 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x0004f382: RET *)
(*     324482: RET *)
| 0x4f382 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx iswdigit_l_i386.
Proof. Picinae_typecheck. Qed.

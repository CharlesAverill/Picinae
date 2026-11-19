(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: tolower_l
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition tolower_l_i386 : program := fun _ a => match a with

(* 0x0004f646: PUSH EBX *)
(*     325190: PUSH EBX *)
| 0x4f646 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0004f647: CALL 0x0004a842 *)
(*     325191: CALL 0x0004a842 *)
| 0x4f647 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x4f64c 32)) LittleE 4) $;
	Jmp (Word 0x4a842 32)
)

(* 0x0004f64c: ADD EBX,0x65950 *)
(*     325196: ADD EBX,0x65950 *)
| 0x4f64c => Some (6,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EBX) (Word 0x65950 32)) (Var R_EBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EBX) (Word 0x65950 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x65950 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EBX (BinOp OP_PLUS (Var R_EBX) (Word 0x65950 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EBX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EBX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EBX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0004f652: SUB ESP,0x14 *)
(*     325202: SUB ESP,0x14 *)
| 0x4f652 => Some (3,
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

(* 0x0004f655: PUSH dword ptr [ESP + 0x1c] *)
(*     325205: PUSH dword ptr [ESP + 0x1c] *)
| 0x4f655 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x1c 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move (V_TEMP 0x20a80) (Var (V_TEMP 0xb900)) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0004f659: CALL 0x0004f635 *)
(*     325209: CALL 0x0004f635 *)
| 0x4f659 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x4f65e 32)) LittleE 4) $;
	Jmp (Word 0x4f635 32)
)

(* 0x0004f65e: ADD ESP,0x18 *)
(*     325214: ADD ESP,0x18 *)
| 0x4f65e => Some (3,
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

(* 0x0004f661: POP EBX *)
(*     325217: POP EBX *)
| 0x4f661 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x0004f662: RET *)
(*     325218: RET *)
| 0x4f662 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx tolower_l_i386.
Proof. Picinae_typecheck. Qed.

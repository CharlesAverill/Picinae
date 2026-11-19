(* Codex-local i386 GS-base alias: segment_adapter.py + pcode2coq_codex.py.
   Exact 32-bit register0x114: Ghidra GS_OFFSET = Picinae R_GS_BASE. *)
(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: strcoll
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcoll_i386 : program := fun _ a => match a with

(* 0x00055300: PUSH EBX *)
(*     348928: PUSH EBX *)
| 0x55300 => Some (1,
	Move (V_TEMP 0x20a80) (Var R_EBX) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00055301: CALL 0x0004a842 *)
(*     348929: CALL 0x0004a842 *)
| 0x55301 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x55306 32)) LittleE 4) $;
	Jmp (Word 0x4a842 32)
)

(* 0x00055306: ADD EBX,0x5fc96 *)
(*     348934: ADD EBX,0x5fc96 *)
| 0x55306 => Some (6,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_EBX) (Word 0x5fc96 32)) (Var R_EBX))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_EBX) (Word 0x5fc96 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_EBX) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x5fc96 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_EBX (BinOp OP_PLUS (Var R_EBX) (Word 0x5fc96 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_EBX) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_EBX) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_EBX) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x0005530c: MOV EAX,GS:[0x0] *)
(*     348940: MOV EAX,GS:[0x0] *)
| 0x5530c => Some (6,
	Move (V_TEMP 0x9000) (BinOp OP_PLUS (Var R_GS_BASE) (Word 0x0 32)) $;
	Move (V_TEMP 0x9080) (Load (Var V_MEM32) (Var (V_TEMP 0x9000)) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0x9080))
)

(* 0x00055312: SUB ESP,0xc *)
(*     348946: SUB ESP,0xc *)
| 0x55312 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var R_ESP) (Word 0xc 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_ESP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0xc 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0xc 32)) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_ESP) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_ESP) (Word 0x0 32))) $;
	Move (V_TEMP 0x24c00) (BinOp OP_AND (Var R_ESP) (Word 0xff 32)) $;
	Move (V_TEMP 0x24c80) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x24c00)))) $;
	Move (V_TEMP 0x24d00) (BinOp OP_AND (Var (V_TEMP 0x24c80)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x24d00)) (Word 0x0 8)))
)

(* 0x00055315: PUSH dword ptr [EAX + 0x60] *)
(*     348949: PUSH dword ptr [EAX + 0x60] *)
| 0x55315 => Some (3,
	Move (V_TEMP 0x3300) (BinOp OP_PLUS (Var R_EAX) (Word 0x60 32)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3300)) LittleE 4) $;
	Move (V_TEMP 0x20a80) (Var (V_TEMP 0xb900)) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00055318: PUSH dword ptr [ESP + 0x1c] *)
(*     348952: PUSH dword ptr [ESP + 0x1c] *)
| 0x55318 => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x1c 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move (V_TEMP 0x20a80) (Var (V_TEMP 0xb900)) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x0005531c: PUSH dword ptr [ESP + 0x1c] *)
(*     348956: PUSH dword ptr [ESP + 0x1c] *)
| 0x5531c => Some (4,
	Move (V_TEMP 0x3b00) (BinOp OP_PLUS (Word 0x1c 32) (Var R_ESP)) $;
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var (V_TEMP 0x3b00)) LittleE 4) $;
	Move (V_TEMP 0x20a80) (Var (V_TEMP 0xb900)) $;
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x20a80))) LittleE 4)
)

(* 0x00055320: CALL 0x000552df *)
(*     348960: CALL 0x000552df *)
| 0x55320 => Some (5,
	Move R_ESP (BinOp OP_MINUS (Var R_ESP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_ESP) (Cast CAST_UNSIGNED 32 (Word 0x55325 32)) LittleE 4) $;
	Jmp (Word 0x552df 32)
)

(* 0x00055325: ADD ESP,0x18 *)
(*     348965: ADD ESP,0x18 *)
| 0x55325 => Some (3,
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

(* 0x00055328: POP EBX *)
(*     348968: POP EBX *)
| 0x55328 => Some (1,
	Move (V_TEMP 0x43980) (Word 0x0 32) $;
	Move (V_TEMP 0x43980) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Move R_EBX (Var (V_TEMP 0x43980))
)

(* 0x00055329: RET *)
(*     348969: RET *)
| 0x55329 => Some (1,
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

Theorem welltyped: welltyped_prog x86typctx strcoll_i386.
Proof. Picinae_typecheck. Qed.

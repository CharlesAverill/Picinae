(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: memcmp
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition memcmp_armv7 : program := fun _ a => match a with

(* 0x0005b0b2: cbz r2,0x0005b0ce *)
(*     372914: cbz r2,0x0005b0ce *)
| 0x5b0b2 => Some (2,
	Move (V_TEMP 0xa6380) (BinOp OP_EQ (Var R_R2) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6380))) (
		Jmp (Word 0x5b0ce 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b0b4: ldrb.w r12,[r0,#0x0] *)
(*     372916: ldrb.w r12,[r0,#0x0] *)
| 0x5b0b4 => Some (4,
	Move (V_TEMP 0xa1a80) (BinOp OP_PLUS (Var R_R0) (Word 0x0 32)) $;
	Move (V_TEMP 0xa8f00) (Load (Var V_MEM32) (Var (V_TEMP 0xa1a80)) LittleE 1) $;
	Move R_R12 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa8f00)))
)

(* 0x0005b0b8: ldrb r3,[r1,#0x0] *)
(*     372920: ldrb r3,[r1,#0x0] *)
| 0x5b0b8 => Some (2,
	Move (V_TEMP 0xa2880) (BinOp OP_PLUS (Var R_R1) (Word 0x0 32)) $;
	Move (V_TEMP 0xa7980) (Load (Var V_MEM32) (Var (V_TEMP 0xa2880)) LittleE 1) $;
	Move R_R3 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa7980)))
)

(* 0x0005b0ba: adds r0,#0x1 *)
(*     372922: adds r0,#0x1 *)
| 0x5b0ba => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Word 0x1 32)) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Word 0x1 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b0bc: cmp r12,r3 *)
(*     372924: cmp r12,r3 *)
| 0x5b0bc => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R3) (Var R_R12))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var R_R3)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var R_R3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa7100) (BinOp OP_MINUS (Var R_R12) (Var R_R3)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa7100)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa7100)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b0be: add.w r1,r1,#0x1 *)
(*     372926: add.w r1,r1,#0x1 *)
| 0x5b0be => Some (4,
	Move (V_TEMP 0x97780) (Word 0x1 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R1) (Var (V_TEMP 0x97780))) (Var R_R1))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R1) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R1 (BinOp OP_PLUS (Var R_R1) (Var (V_TEMP 0x97780))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32)))
)

(* 0x0005b0c2: add.w r2,r2,#0xffffffff *)
(*     372930: add.w r2,r2,#0xffffffff *)
| 0x5b0c2 => Some (4,
	Move (V_TEMP 0x97900) (Word 0xffffffff 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R2) (Var (V_TEMP 0x97900))) (Var R_R2))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R2) (Var (V_TEMP 0x97900))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97900)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_PLUS (Var R_R2) (Var (V_TEMP 0x97900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32)))
)

(* 0x0005b0c6: beq 0x0005b0b2 *)
(*     372934: beq 0x0005b0b2 *)
| 0x5b0c6 => Some (2,
	Move (V_TEMP 0x93a00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93a00))) (
		Jmp (Word 0x5b0b2 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b0c8: sub.w r0,r12,r3 *)
(*     372936: sub.w r0,r12,r3 *)
| 0x5b0c8 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd4680) (Var R_R3) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R12))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005b0cc: bx lr *)
(*     372940: bx lr *)
| 0x5b0cc => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x0005b0ce: mov r0,r2 *)
(*     372942: mov r0,r2 *)
| 0x5b0ce => Some (2,
	Move R_R0 (Var R_R2)
)

(* 0x0005b0d0: bx lr *)
(*     372944: bx lr *)
| 0x5b0d0 => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx memcmp_armv7.
Proof. Picinae_typecheck. Qed.

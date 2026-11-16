(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: strnlen
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strnlen_armv7 : program := fun _ a => match a with

(* 0x0005baa4: mov r2,r1 *)
(*     375460: mov r2,r1 *)
| 0x5baa4 => Some (2,
	Move R_R2 (Var R_R1)
)

(* 0x0005baa6: push {r4,lr} *)
(*     375462: push {r4,lr} *)
| 0x5baa6 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R4)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0005baa8: movs r1,#0x0 *)
(*     375464: movs r1,#0x0 *)
| 0x5baa8 => Some (2,
	Move R_R1 (Word 0x0 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005baaa: sub sp,#0x8 *)
(*     375466: sub sp,#0x8 *)
| 0x5baaa => Some (2,
	Move (V_TEMP 0x97380) (Word 0x8 32) $;
	Move R_SP (BinOp OP_MINUS (Var R_SP) (Var (V_TEMP 0x97380)))
)

(* 0x0005baac: mov r4,r0 *)
(*     375468: mov r4,r0 *)
| 0x5baac => Some (2,
	Move R_R4 (Var R_R0)
)

(* 0x0005baae: str r2,[sp,#0x4] *)
(*     375470: str r2,[sp,#0x4] *)
| 0x5baae => Some (2,
	Move (V_TEMP 0xa2b00) (BinOp OP_PLUS (Var R_SP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2b00)) (Cast CAST_UNSIGNED 32 (Var R_R2)) LittleE 4)
)

(* 0x0005bab0: bl 0x0005b042 *)
(*     375472: bl 0x0005b042 *)
| 0x5bab0 => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x5bab4 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x5b042 32)
)

(* 0x0005bab4: cbz r0,0x0005babc *)
(*     375476: cbz r0,0x0005babc *)
| 0x5bab4 => Some (2,
	Move (V_TEMP 0xa6380) (BinOp OP_EQ (Var R_R0) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6380))) (
		Jmp (Word 0x5babc 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005bab6: subs r0,r0,r4 *)
(*     375478: subs r0,r0,r4 *)
| 0x5bab6 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R4) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var R_R4)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var R_R4)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R4) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Var R_R0) (Var R_R4)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005bab8: add sp,#0x8 *)
(*     375480: add sp,#0x8 *)
| 0x5bab8 => Some (2,
	Move (V_TEMP 0x97380) (Word 0x8 32) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x97380)))
)

(* 0x0005baba: pop {r4,pc} *)
(*     375482: pop {r4,pc} *)
| 0x5baba => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_R4 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_PC (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_SP (Var R_MULT_ADDR) $;
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_PC) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_PC) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x0005babc: ldr r0,[sp,#0x4] *)
(*     375484: ldr r0,[sp,#0x4] *)
| 0x5babc => Some (2,
	Move (V_TEMP 0xa2b00) (BinOp OP_PLUS (Var R_SP) (Word 0x4 32)) $;
	Move R_R0 (Load (Var V_MEM32) (Var (V_TEMP 0xa2b00)) LittleE 4)
)

(* 0x0005babe: b 0x0005bab8 *)
(*     375486: b 0x0005bab8 *)
| 0x5babe => Some (2,
	Jmp (Word 0x5bab8 32)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx strnlen_armv7.
Proof. Picinae_typecheck. Qed.

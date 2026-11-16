(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: cfsetspeed
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition cfsetspeed_armv7 : program := fun _ a => match a with

(* 0x0005c5fc: push {r4,lr} *)
(*     378364: push {r4,lr} *)
| 0x5c5fc => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R4)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0005c5fe: sub sp,#0x8 *)
(*     378366: sub sp,#0x8 *)
| 0x5c5fe => Some (2,
	Move (V_TEMP 0x97380) (Word 0x8 32) $;
	Move R_SP (BinOp OP_MINUS (Var R_SP) (Var (V_TEMP 0x97380)))
)

(* 0x0005c600: mov r4,r0 *)
(*     378368: mov r4,r0 *)
| 0x5c600 => Some (2,
	Move R_R4 (Var R_R0)
)

(* 0x0005c602: bl 0x0005c59a *)
(*     378370: bl 0x0005c59a *)
| 0x5c602 => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x5c606 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x5c59a 32)
)

(* 0x0005c606: mov r1,r0 *)
(*     378374: mov r1,r0 *)
| 0x5c606 => Some (2,
	Move R_R1 (Var R_R0)
)

(* 0x0005c608: cbz r0,0x0005c610 *)
(*     378376: cbz r0,0x0005c610 *)
| 0x5c608 => Some (2,
	Move (V_TEMP 0xa6380) (BinOp OP_EQ (Var R_R0) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6380))) (
		Jmp (Word 0x5c610 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005c60a: mov r0,r1 *)
(*     378378: mov r0,r1 *)
| 0x5c60a => Some (2,
	Move R_R0 (Var R_R1)
)

(* 0x0005c60c: add sp,#0x8 *)
(*     378380: add sp,#0x8 *)
| 0x5c60c => Some (2,
	Move (V_TEMP 0x97380) (Word 0x8 32) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x97380)))
)

(* 0x0005c60e: pop {r4,pc} *)
(*     378382: pop {r4,pc} *)
| 0x5c60e => Some (2,
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

(* 0x0005c610: str r0,[sp,#0x4] *)
(*     378384: str r0,[sp,#0x4] *)
| 0x5c610 => Some (2,
	Move (V_TEMP 0xa2b00) (BinOp OP_PLUS (Var R_SP) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2b00)) (Cast CAST_UNSIGNED 32 (Var R_R0)) LittleE 4)
)

(* 0x0005c612: mov r0,r4 *)
(*     378386: mov r0,r4 *)
| 0x5c612 => Some (2,
	Move R_R0 (Var R_R4)
)

(* 0x0005c614: bl 0x0005c5cc *)
(*     378388: bl 0x0005c5cc *)
| 0x5c614 => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x5c618 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x5c5cc 32)
)

(* 0x0005c618: ldr r1,[sp,#0x4] *)
(*     378392: ldr r1,[sp,#0x4] *)
| 0x5c618 => Some (2,
	Move (V_TEMP 0xa2b00) (BinOp OP_PLUS (Var R_SP) (Word 0x4 32)) $;
	Move R_R1 (Load (Var V_MEM32) (Var (V_TEMP 0xa2b00)) LittleE 4)
)

(* 0x0005c61a: b 0x0005c60a *)
(*     378394: b 0x0005c60a *)
| 0x5c61a => Some (2,
	Jmp (Word 0x5c60a 32)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx cfsetspeed_armv7.
Proof. Picinae_typecheck. Qed.

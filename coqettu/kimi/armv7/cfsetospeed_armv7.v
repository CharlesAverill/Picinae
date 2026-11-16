(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: cfsetospeed
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition cfsetospeed_armv7 : program := fun _ a => match a with

(* 0x0005c59a: movw r2,#0xeff0 *)
(*     378266: movw r2,#0xeff0 *)
| 0x5c59a => Some (4,
	Move R_R2 (Cast CAST_UNSIGNED 32 (Word 0xeff0 16)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32)))
)

(* 0x0005c59e: movt r2,#0xffff *)
(*     378270: movt r2,#0xffff *)
| 0x5c59e => Some (4,
	Move (V_TEMP 0xadb00) (Cast CAST_UNSIGNED 32 (Word 0xffff 16)) $;
	Move (V_TEMP 0xadb80) (BinOp OP_LSHIFT (Var (V_TEMP 0xadb00)) (Word 0x10 32)) $;
	Move (V_TEMP 0xadc00) (BinOp OP_AND (Var R_R2) (Word 0xffff 32)) $;
	Move R_R2 (BinOp OP_OR (Var (V_TEMP 0xadb80)) (Var (V_TEMP 0xadc00)))
)

(* 0x0005c5a2: push {r3,lr} *)
(*     378274: push {r3,lr} *)
| 0x5c5a2 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R3)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0005c5a4: ands.w r3,r1,r2 *)
(*     378276: ands.w r3,r1,r2 *)
| 0x5c5a4 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_R3 (BinOp OP_AND (Var R_R1) (Var R_R2)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005c5a8: bne 0x0005c5bc *)
(*     378280: bne 0x0005c5bc *)
| 0x5c5a8 => Some (2,
	Move (V_TEMP 0x93b00) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93b00))) (
		Jmp (Word 0x5c5bc 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005c5aa: mov r12,r0 *)
(*     378282: mov r12,r0 *)
| 0x5c5aa => Some (2,
	Move R_R12 (Var R_R0)
)

(* 0x0005c5ac: mov r0,r3 *)
(*     378284: mov r0,r3 *)
| 0x5c5ac => Some (2,
	Move R_R0 (Var R_R3)
)

(* 0x0005c5ae: ldr.w r3,[r12,#0x8] *)
(*     378286: ldr.w r3,[r12,#0x8] *)
| 0x5c5ae => Some (4,
	Move (V_TEMP 0xa1a80) (BinOp OP_PLUS (Var R_R12) (Word 0x8 32)) $;
	Move R_R3 (Load (Var V_MEM32) (Var (V_TEMP 0xa1a80)) LittleE 4)
)

(* 0x0005c5b2: ands r3,r2 *)
(*     378290: ands r3,r2 *)
| 0x5c5b2 => Some (2,
	Move R_R3 (BinOp OP_AND (Var R_R3) (Var R_R2)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005c5b4: orrs r3,r1 *)
(*     378292: orrs r3,r1 *)
| 0x5c5b4 => Some (2,
	Move R_R3 (BinOp OP_OR (Var R_R3) (Var R_R1)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005c5b6: str.w r3,[r12,#0x8] *)
(*     378294: str.w r3,[r12,#0x8] *)
| 0x5c5b6 => Some (4,
	Move (V_TEMP 0xa1a80) (BinOp OP_PLUS (Var R_R12) (Word 0x8 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa1a80)) (Cast CAST_UNSIGNED 32 (Var R_R3)) LittleE 4)
)

(* 0x0005c5ba: pop {r3,pc} *)
(*     378298: pop {r3,pc} *)
| 0x5c5ba => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_R3 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
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

(* 0x0005c5bc: bl 0x0004e00e *)
(*     378300: bl 0x0004e00e *)
| 0x5c5bc => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x5c5c0 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x4e00e 32)
)

(* 0x0005c5c0: movs r2,#0x16 *)
(*     378304: movs r2,#0x16 *)
| 0x5c5c0 => Some (2,
	Move R_R2 (Word 0x16 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005c5c2: mov r3,r0 *)
(*     378306: mov r3,r0 *)
| 0x5c5c2 => Some (2,
	Move R_R3 (Var R_R0)
)

(* 0x0005c5c4: mov.w r0,#0xffffffff *)
(*     378308: mov.w r0,#0xffffffff *)
| 0x5c5c4 => Some (4,
	Move (V_TEMP 0x97900) (Word 0xffffffff 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_R0 (Var (V_TEMP 0x97900)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005c5c8: str r2,[r3,#0x0] *)
(*     378312: str r2,[r3,#0x0] *)
| 0x5c5c8 => Some (2,
	Move (V_TEMP 0xa2680) (BinOp OP_PLUS (Var R_R3) (Word 0x0 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2680)) (Cast CAST_UNSIGNED 32 (Var R_R2)) LittleE 4)
)

(* 0x0005c5ca: b 0x0005c5ba *)
(*     378314: b 0x0005c5ba *)
| 0x5c5ca => Some (2,
	Jmp (Word 0x5c5ba 32)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx cfsetospeed_armv7.
Proof. Picinae_typecheck. Qed.

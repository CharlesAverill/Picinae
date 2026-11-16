(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: cfsetispeed
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition cfsetispeed_armv7 : program := fun _ a => match a with

(* 0x0005c5cc: mov r2,r0 *)
(*     378316: mov r2,r0 *)
| 0x5c5cc => Some (2,
	Move R_R2 (Var R_R0)
)

(* 0x0005c5ce: bic r0,r1,#0x1000 *)
(*     378318: bic r0,r1,#0x1000 *)
| 0x5c5ce => Some (4,
	Move (V_TEMP 0x97b80) (Word 0x1000 32) $;
	Move (V_TEMP 0x97c80) (BinOp OP_RSHIFT (Var (V_TEMP 0x97b80)) (Word 0x1f 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x97c80)) (Word 0 32))) $;
	Move (V_TEMP 0xa5700) (UnOp OP_NOT (Var (V_TEMP 0x97b80))) $;
	Move R_R0 (BinOp OP_AND (Var R_R1) (Var (V_TEMP 0xa5700))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005c5d2: bic r0,r0,#0xf *)
(*     378322: bic r0,r0,#0xf *)
| 0x5c5d2 => Some (4,
	Move (V_TEMP 0x97780) (Word 0xf 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xa5700) (UnOp OP_NOT (Var (V_TEMP 0x97780))) $;
	Move R_R0 (BinOp OP_AND (Var R_R0) (Var (V_TEMP 0xa5700))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005c5d6: push {r3,lr} *)
(*     378326: push {r3,lr} *)
| 0x5c5d6 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R3)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0005c5d8: cbnz r0,0x0005c5ec *)
(*     378328: cbnz r0,0x0005c5ec *)
| 0x5c5d8 => Some (2,
	Move (V_TEMP 0xa6280) (BinOp OP_NEQ (Var R_R0) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6280))) (
		Jmp (Word 0x5c5ec 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005c5da: ldr r3,[r2,#0x8] *)
(*     378330: ldr r3,[r2,#0x8] *)
| 0x5c5da => Some (2,
	Move (V_TEMP 0xa2680) (BinOp OP_PLUS (Var R_R2) (Word 0x8 32)) $;
	Move R_R3 (Load (Var V_MEM32) (Var (V_TEMP 0xa2680)) LittleE 4)
)

(* 0x0005c5dc: bic r3,r3,#0x10000000 *)
(*     378332: bic r3,r3,#0x10000000 *)
| 0x5c5dc => Some (4,
	Move (V_TEMP 0x97980) (Word 0x10000000 32) $;
	Move (V_TEMP 0x97a80) (BinOp OP_RSHIFT (Var (V_TEMP 0x97980)) (Word 0x1f 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x97a80)) (Word 0 32))) $;
	Move (V_TEMP 0xa5700) (UnOp OP_NOT (Var (V_TEMP 0x97980))) $;
	Move R_R3 (BinOp OP_AND (Var R_R3) (Var (V_TEMP 0xa5700))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0005c5e0: bic r3,r3,#0xf0000 *)
(*     378336: bic r3,r3,#0xf0000 *)
| 0x5c5e0 => Some (4,
	Move (V_TEMP 0x97b80) (Word 0xf0000 32) $;
	Move (V_TEMP 0x97c80) (BinOp OP_RSHIFT (Var (V_TEMP 0x97b80)) (Word 0x1f 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x97c80)) (Word 0 32))) $;
	Move (V_TEMP 0xa5700) (UnOp OP_NOT (Var (V_TEMP 0x97b80))) $;
	Move R_R3 (BinOp OP_AND (Var R_R3) (Var (V_TEMP 0xa5700))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0005c5e4: orr.w r3,r3,r1, lsl #0x10 *)
(*     378340: orr.w r3,r3,r1, lsl #0x10 *)
| 0x5c5e4 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x10 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x10 32)) $;
	Move R_R3 (BinOp OP_OR (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0005c5e8: str r3,[r2,#0x8] *)
(*     378344: str r3,[r2,#0x8] *)
| 0x5c5e8 => Some (2,
	Move (V_TEMP 0xa2680) (BinOp OP_PLUS (Var R_R2) (Word 0x8 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2680)) (Cast CAST_UNSIGNED 32 (Var R_R3)) LittleE 4)
)

(* 0x0005c5ea: pop {r3,pc} *)
(*     378346: pop {r3,pc} *)
| 0x5c5ea => Some (2,
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

(* 0x0005c5ec: bl 0x0004e00e *)
(*     378348: bl 0x0004e00e *)
| 0x5c5ec => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x5c5f0 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x4e00e 32)
)

(* 0x0005c5f0: movs r2,#0x16 *)
(*     378352: movs r2,#0x16 *)
| 0x5c5f0 => Some (2,
	Move R_R2 (Word 0x16 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005c5f2: mov r3,r0 *)
(*     378354: mov r3,r0 *)
| 0x5c5f2 => Some (2,
	Move R_R3 (Var R_R0)
)

(* 0x0005c5f4: mov.w r0,#0xffffffff *)
(*     378356: mov.w r0,#0xffffffff *)
| 0x5c5f4 => Some (4,
	Move (V_TEMP 0x97900) (Word 0xffffffff 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_R0 (Var (V_TEMP 0x97900)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005c5f8: str r2,[r3,#0x0] *)
(*     378360: str r2,[r3,#0x0] *)
| 0x5c5f8 => Some (2,
	Move (V_TEMP 0xa2680) (BinOp OP_PLUS (Var R_R3) (Word 0x0 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2680)) (Cast CAST_UNSIGNED 32 (Var R_R2)) LittleE 4)
)

(* 0x0005c5fa: b 0x0005c5ea *)
(*     378362: b 0x0005c5ea *)
| 0x5c5fa => Some (2,
	Jmp (Word 0x5c5ea 32)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx cfsetispeed_armv7.
Proof. Picinae_typecheck. Qed.

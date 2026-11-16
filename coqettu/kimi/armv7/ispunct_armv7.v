(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: ispunct
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ispunct_armv7 : program := fun _ a => match a with

(* 0x0004d9d6: push {r3,lr} *)
(*     317910: push {r3,lr} *)
| 0x4d9d6 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R3)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0004d9d8: sub.w r3,r0,#0x21 *)
(*     317912: sub.w r3,r0,#0x21 *)
| 0x4d9d8 => Some (4,
	Move (V_TEMP 0x97780) (Word 0x21 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x97780)) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97780))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0004d9dc: cmp r3,#0x5d *)
(*     317916: cmp r3,#0x5d *)
| 0x4d9dc => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x5d 32) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Word 0x5d 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Word 0x5d 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x5d 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R3) (Word 0x5d 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0004d9de: it hi *)
(*     317918: it hi *)
| 0x4d9de => Some (2,
	Move (V_TEMP 0x96280) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0x96380) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var R_CF) (Var (V_TEMP 0x96280))))
)

(* 0x0004d9e0: mov.hi r0,#0x0 *)
(*     317920: mov.hi r0,#0x0 *)
| 0x4d9e0 => Some (2,
	Move (V_TEMP 0xa00) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0xb00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var R_CF) (Var (V_TEMP 0xa00)))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0xb00))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x4d9e2 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (Word 0x0 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0004d9e2: bls 0x0004d9e6 *)
(*     317922: bls 0x0004d9e6 *)
| 0x4d9e2 => Some (2,
	Move (V_TEMP 0x94300) (UnOp OP_NOT (Var R_CF)) $;
	Move (V_TEMP 0x94400) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var (V_TEMP 0x94300)) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x94400))) (
		Jmp (Word 0x4d9e6 32)
	) (* else *) (
		Nop
	)
)

(* 0x0004d9e4: pop {r3,pc} *)
(*     317924: pop {r3,pc} *)
| 0x4d9e4 => Some (2,
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

(* 0x0004d9e6: bl 0x0004d936 *)
(*     317926: bl 0x0004d936 *)
| 0x4d9e6 => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x4d9ea 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x4d936 32)
)

(* 0x0004d9ea: clz r0,r0 *)
(*     317930: clz r0,r0 *)
| 0x4d9ea => Some (4,
	Move R_R0 (Cast CAST_UNSIGNED 32 (BinOp OP_MINUS (Word 32 32) (UnOp OP_BITWIDTH (Var R_R0))))
)

(* 0x0004d9ee: lsrs r0,r0,#0x5 *)
(*     317934: lsrs r0,r0,#0x5 *)
| 0x4d9ee => Some (2,
	Move (V_TEMP 0xacd80) (Word 0x5 32) $;
	Move (V_TEMP 0xac800) (BinOp OP_MINUS (Var (V_TEMP 0xacd80)) (Word 0x1 32)) $;
	Move (V_TEMP 0xac880) (BinOp OP_RSHIFT (Var R_R0) (Var (V_TEMP 0xac800))) $;
	Move (V_TEMP 0xac980) (BinOp OP_AND (Var (V_TEMP 0xac880)) (Word 0x1 32)) $;
	Move (V_TEMP 0xaca00) (BinOp OP_EQ (Var (V_TEMP 0xacd80)) (Word 0x0 32)) $;
	Move (V_TEMP 0xaca80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xaca00)) (Var R_CF))) $;
	Move (V_TEMP 0xacb00) (BinOp OP_NEQ (Var (V_TEMP 0xacd80)) (Word 0x0 32)) $;
	Move (V_TEMP 0xacb80) (BinOp OP_NEQ (Var (V_TEMP 0xac980)) (Word 0x0 32)) $;
	Move (V_TEMP 0xacc00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xacb00)) (Var (V_TEMP 0xacb80)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0xaca80))) (Cast CAST_LOW 1 (Var (V_TEMP 0xacc00)))))) $;
	Move R_R0 (BinOp OP_RSHIFT (Var R_R0) (Word 0x5 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0004d9f0: b 0x0004d9e4 *)
(*     317936: b 0x0004d9e4 *)
| 0x4d9f0 => Some (2,
	Jmp (Word 0x4d9e4 32)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx ispunct_armv7.
Proof. Picinae_typecheck. Qed.

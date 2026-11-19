(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: FUN_000306fc
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition FUN_000306fc_armv7 : program := fun _ a => match a with

(* 0x000306fc: cmp r1,#0x0 *)
(*     198396: cmp r1,#0x0 *)
| 0x306fc => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x0 32) (Var R_R1))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000306fe: beq 0x000306ea *)
(*     198398: beq 0x000306ea *)
| 0x306fe => Some (2,
	Move (V_TEMP 0x93a00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93a00))) (
		Jmp (Word 0x306ea 32)
	) (* else *) (
		Nop
	)
)

(* 0x00030700: push {r0,r1,lr} *)
(*     198400: push {r0,r1,lr} *)
| 0x30700 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R1)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R0)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x00030702: bl 0x0003046e *)
(*     198402: bl 0x0003046e *)
| 0x30702 => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x30706 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x3046e 32)
)

(* 0x00030706: pop.w {r1,r2,lr} *)
(*     198406: pop.w {r1,r2,lr} *)
| 0x30706 => Some (4,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_R1 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_R2 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_LR (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0003070a: mul r3,r2,r0 *)
(*     198410: mul r3,r2,r0 *)
| 0x3070a => Some (4,
	Move R_R3 (BinOp OP_TIMES (Var R_R2) (Var R_R0))
)

(* 0x0003070e: sub.w r1,r1,r3 *)
(*     198414: sub.w r1,r1,r3 *)
| 0x3070e => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd4680) (Var R_R3) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R1))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R1 (BinOp OP_MINUS (Var R_R1) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32)))
)

(* 0x00030712: bx lr *)
(*     198418: bx lr *)
| 0x30712 => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x00030468: cmp r1,#0x0 *)
(*     197736: cmp r1,#0x0 *)
| 0x30468 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x0 32) (Var R_R1))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0003046a: beq.w 0x000306ea *)
(*     197738: beq.w 0x000306ea *)
| 0x3046a => Some (4,
	Move (V_TEMP 0x94a80) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x94a80))) (
		Jmp (Word 0x306ea 32)
	) (* else *) (
		Nop
	)
)

(* 0x000306ea: cmp r0,#0x0 *)
(*     198378: cmp r0,#0x0 *)
| 0x306ea => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x0 32) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000306ec: it gt *)
(*     198380: it gt *)
| 0x306ec => Some (2,
	Move (V_TEMP 0x96780) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0x96800) (BinOp OP_EQ (Var R_NF) (Var R_VF)) $;
	Move (V_TEMP 0x96900) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0x96780)) (Var (V_TEMP 0x96800))))
)

(* 0x000306ee: mvn.gt r0,#0x80000000 *)
(*     198382: mvn.gt r0,#0x80000000 *)
| 0x306ee => Some (4,
	Move (V_TEMP 0x97980) (Word 0x80000000 32) $;
	Move (V_TEMP 0x97a80) (BinOp OP_RSHIFT (Var (V_TEMP 0x97980)) (Word 0x1f 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x97a80)) (Word 0 32))) $;
	Move (V_TEMP 0xf00) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0xf80) (BinOp OP_EQ (Var R_NF) (Var R_VF)) $;
	Move (V_TEMP 0x1080) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xf00)) (Var (V_TEMP 0xf80)))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x1080))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306f2 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (UnOp OP_NOT (Var (V_TEMP 0x97980))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306f2: it lt *)
(*     198386: it lt *)
| 0x306f2 => Some (2,
	Move (V_TEMP 0x96700) (BinOp OP_EQ (Var R_NF) (Var R_VF))
)

(* 0x000306f4: mov.lt.w r0,#0x80000000 *)
(*     198388: mov.lt.w r0,#0x80000000 *)
| 0x306f4 => Some (4,
	Move (V_TEMP 0x97980) (Word 0x80000000 32) $;
	Move (V_TEMP 0x97a80) (BinOp OP_RSHIFT (Var (V_TEMP 0x97980)) (Word 0x1f 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x97a80)) (Word 0 32))) $;
	Move (V_TEMP 0xe80) (BinOp OP_NEQ (Var R_NF) (Var R_VF)) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0xe80))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306f8 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (Var (V_TEMP 0x97980)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306f8: b.w 0x0004c944 *)
(*     198392: b.w 0x0004c944 *)
| 0x306f8 => Some (4,
	Jmp (Word 0x4c944 32)
)

(* 0x0004c914: cbnz r3,0x0004c92c *)
(*     313620: cbnz r3,0x0004c92c *)
| 0x4c914 => Some (2,
	Move (V_TEMP 0xa6280) (BinOp OP_NEQ (Var R_R3) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6280))) (
		Jmp (Word 0x4c92c 32)
	) (* else *) (
		Nop
	)
)

(* 0x0004c916: cbnz r2,0x0004c92c *)
(*     313622: cbnz r2,0x0004c92c *)
| 0x4c916 => Some (2,
	Move (V_TEMP 0xa6280) (BinOp OP_NEQ (Var R_R2) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6280))) (
		Jmp (Word 0x4c92c 32)
	) (* else *) (
		Nop
	)
)

(* 0x0004c918: cmp r1,#0x0 *)
(*     313624: cmp r1,#0x0 *)
| 0x4c918 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x0 32) (Var R_R1))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R1) (Word 0x0 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0004c91a: it eq *)
(*     313626: it eq *)
| 0x4c91a => Some (2,
	Move (V_TEMP 0x95b00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0004c91c: cmp.eq r0,#0x0 *)
(*     313628: cmp.eq r0,#0x0 *)
| 0x4c91c => Some (2,
	Move (V_TEMP 0x280) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x280))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x4c91e 32)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x0 32) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R0) (Word 0x0 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0004c91e: itt ne *)
(*     313630: itt ne *)
| 0x4c91e => Some (2,
	Move (V_TEMP 0x95c00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0004c920: mov.ne.w r1,#0xffffffff *)
(*     313632: mov.ne.w r1,#0xffffffff *)
| 0x4c920 => Some (4,
	Move (V_TEMP 0x97900) (Word 0xffffffff 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x380) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1300) (UnOp OP_NOT (Var (V_TEMP 0x380))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1300))) (
		Jmp (Word 0x4c924 32)
	) (* else *) (
		Nop
	) $;
	Move R_R1 (Var (V_TEMP 0x97900)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32)))
)

(* 0x0004c924: mov.ne.w r0,#0xffffffff *)
(*     313636: mov.ne.w r0,#0xffffffff *)
| 0x4c924 => Some (4,
	Move (V_TEMP 0x97900) (Word 0xffffffff 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x380) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x380))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x4c928 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (Var (V_TEMP 0x97900)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0004c928: b.w 0x0004c944 *)
(*     313640: b.w 0x0004c944 *)
| 0x4c928 => Some (4,
	Jmp (Word 0x4c944 32)
)

(* 0x0004c92c: sub.w r12,sp,#0x8 *)
(*     313644: sub.w r12,sp,#0x8 *)
| 0x4c92c => Some (4,
	Move (V_TEMP 0x97780) (Word 0x8 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x97780)) (Var R_SP))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_SP) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_SP) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R12 (BinOp OP_MINUS (Var R_SP) (Var (V_TEMP 0x97780))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R12) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R12) (Word 0x0 32)))
)

(* 0x0004c930: strd r12,lr,[sp,#-0x10]! *)
(*     313648: strd r12,lr,[sp,#-0x10]! *)
| 0x4c930 => Some (4,
	Move (V_TEMP 0xa2380) (BinOp OP_MINUS (Var R_SP) (Word 0x10 32)) $;
	Move R_SP (Var (V_TEMP 0xa2380)) $;
	Move (V_TEMP 0xd2f80) (Var (V_TEMP 0xa2380)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xd2f80)) (Cast CAST_UNSIGNED 32 (Var R_R12)) LittleE 4) $;
	Move (V_TEMP 0xd2f80) (BinOp OP_PLUS (Var (V_TEMP 0xd2f80)) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xd2f80)) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4)
)

(* 0x0004c934: bl 0x0004ccb8 *)
(*     313652: bl 0x0004ccb8 *)
| 0x4c934 => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x4c938 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x4ccb8 32)
)

(* 0x0004c938: ldr.w lr,[sp,#0x4] *)
(*     313656: ldr.w lr,[sp,#0x4] *)
| 0x4c938 => Some (4,
	Move (V_TEMP 0xa1a80) (BinOp OP_PLUS (Var R_SP) (Word 0x4 32)) $;
	Move R_LR (Load (Var V_MEM32) (Var (V_TEMP 0xa1a80)) LittleE 4)
)

(* 0x0004c93c: ldrd r2,r3,[sp,#0x8] *)
(*     313660: ldrd r2,r3,[sp,#0x8] *)
| 0x4c93c => Some (4,
	Move (V_TEMP 0xa2480) (BinOp OP_PLUS (Var R_SP) (Word 0x8 32)) $;
	Move R_R2 (Load (Var V_MEM32) (Var (V_TEMP 0xa2480)) LittleE 4) $;
	Move (V_TEMP 0xa9900) (BinOp OP_PLUS (Var (V_TEMP 0xa2480)) (Word 0x4 32)) $;
	Move R_R3 (Load (Var V_MEM32) (Var (V_TEMP 0xa9900)) LittleE 4)
)

(* 0x0004c940: add sp,#0x10 *)
(*     313664: add sp,#0x10 *)
| 0x4c940 => Some (2,
	Move (V_TEMP 0x97380) (Word 0x10 32) $;
	Move R_SP (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 0x97380)))
)

(* 0x0004c942: bx lr *)
(*     313666: bx lr *)
| 0x4c942 => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x0004c944: push {r1,lr} *)
(*     313668: push {r1,lr} *)
| 0x4c944 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R1)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0004c946: mov.w r0,#0x8 *)
(*     313670: mov.w r0,#0x8 *)
| 0x4c946 => Some (4,
	Move (V_TEMP 0x97780) (Word 0x8 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_R0 (Var (V_TEMP 0x97780)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0004c94a: bl 0x000571f0 *)
(*     313674: bl 0x000571f0 *)
| 0x4c94a => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x4c94e 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x571f0 32)
)

(* 0x0004c94e: pop {r1,pc} *)
(*     313678: pop {r1,pc} *)
| 0x4c94e => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_R1 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
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

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx FUN_000306fc_armv7.
Proof. Picinae_typecheck. Qed.

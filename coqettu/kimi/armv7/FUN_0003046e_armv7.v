(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: FUN_0003046e
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition FUN_0003046e_armv7 : program := fun _ a => match a with

(* 0x0003046e: eor.w r12,r0,r1 *)
(*     197742: eor.w r12,r0,r1 *)
| 0x3046e => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_R12 (BinOp OP_XOR (Var R_R0) (Var R_R1)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R12) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R12) (Word 0x0 32)))
)

(* 0x00030472: it mi *)
(*     197746: it mi *)
| 0x30472 => Some (2,
	Move (V_TEMP 0x95f00) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x00030474: rsb.mi r1,r1 *)
(*     197748: rsb.mi r1,r1 *)
| 0x30474 => Some (2,
	Move (V_TEMP 0x680) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x680))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30476 32)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R1)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R1 (BinOp OP_MINUS (Word 0x0 32) (Var R_R1)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32)))
)

(* 0x00030476: subs r2,r1,#0x1 *)
(*     197750: subs r2,r1,#0x1 *)
| 0x30476 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x1 32) (Var R_R1))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R1) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_MINUS (Var R_R1) (Word 0x1 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030478: beq.w 0x000306ba *)
(*     197752: beq.w 0x000306ba *)
| 0x30478 => Some (4,
	Move (V_TEMP 0x94a80) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x94a80))) (
		Jmp (Word 0x306ba 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003047c: movs r3,r0 *)
(*     197756: movs r3,r0 *)
| 0x3047c => Some (2,
	Move R_R3 (Var R_R0) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0003047e: it mi *)
(*     197758: it mi *)
| 0x3047e => Some (2,
	Move (V_TEMP 0x95f00) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x00030480: rsb.mi r3,r0 *)
(*     197760: rsb.mi r3,r0 *)
| 0x30480 => Some (2,
	Move (V_TEMP 0x680) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x680))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30482 32)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030482: cmp r3,r1 *)
(*     197762: cmp r3,r1 *)
| 0x30482 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R1) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var R_R1)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var R_R1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa7000) (BinOp OP_MINUS (Var R_R3) (Var R_R1)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa7000)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa7000)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030484: bls.w 0x000306c4 *)
(*     197764: bls.w 0x000306c4 *)
| 0x30484 => Some (4,
	Move (V_TEMP 0x95380) (UnOp OP_NOT (Var R_CF)) $;
	Move (V_TEMP 0x95480) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var (V_TEMP 0x95380)) (Var R_ZF))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x95480))) (
		Jmp (Word 0x306c4 32)
	) (* else *) (
		Nop
	)
)

(* 0x00030488: tst r1,r2 *)
(*     197768: tst r1,r2 *)
| 0x30488 => Some (2,
	Move (V_TEMP 0xd9280) (BinOp OP_AND (Var R_R1) (Var R_R2)) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xd9280)) (Word 0x0 32))) $;
	Move R_NF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xd9280)) (Word 0x0 32)))
)

(* 0x0003048a: beq.w 0x000306d4 *)
(*     197770: beq.w 0x000306d4 *)
| 0x3048a => Some (4,
	Move (V_TEMP 0x94a80) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x94a80))) (
		Jmp (Word 0x306d4 32)
	) (* else *) (
		Nop
	)
)

(* 0x0003048e: clz r2,r3 *)
(*     197774: clz r2,r3 *)
| 0x3048e => Some (4,
	Move R_R2 (Cast CAST_UNSIGNED 32 (BinOp OP_MINUS (Word 32 32) (UnOp OP_BITWIDTH (Var R_R3))))
)

(* 0x00030492: clz r0,r1 *)
(*     197778: clz r0,r1 *)
| 0x30492 => Some (4,
	Move R_R0 (Cast CAST_UNSIGNED 32 (BinOp OP_MINUS (Word 32 32) (UnOp OP_BITWIDTH (Var R_R1))))
)

(* 0x00030496: sub.w r2,r0,r2 *)
(*     197782: sub.w r2,r0,r2 *)
| 0x30496 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd4680) (Var R_R2) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32)))
)

(* 0x0003049a: rsb.w r2,r2,#0x1f *)
(*     197786: rsb.w r2,r2,#0x1f *)
| 0x3049a => Some (4,
	Move (V_TEMP 0x97780) (Word 0x1f 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R2) (Var (V_TEMP 0x97780)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x97780)) (Var R_R2)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x97780)) (Var R_R2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_MINUS (Var (V_TEMP 0x97780)) (Var R_R2)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32)))
)

(* 0x0003049e: adr r0,[0x304b0] *)
(*     197790: adr r0,[0x304b0] *)
| 0x3049e => Some (2,
	Move R_R0 (Word 0x304b0 32)
)

(* 0x000304a0: add.w r2,r0,r2, lsl #0x4 *)
(*     197792: add.w r2,r0,r2, lsl #0x4 *)
| 0x304a0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x4 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R2) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R2) (Word 0x4 32)) $;
	Move (V_TEMP 0xa3c00) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3c00))) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3c00))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xa3c00)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3c00))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32)))
)

(* 0x000304a4: mov.w r0,#0x0 *)
(*     197796: mov.w r0,#0x0 *)
| 0x304a4 => Some (4,
	Move (V_TEMP 0x97780) (Word 0x0 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_R0 (Var (V_TEMP 0x97780)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000304a8: mov pc,r2 *)
(*     197800: mov pc,r2 *)
| 0x304a8 => Some (2,
	Move (V_TEMP 0x96d00) (BinOp OP_PLUS (Word 0x304a8 32) (Word 0x4 32)) $;
	Move R_PC (Var R_R2) $;
	Jmp (Var R_PC)
)

(* 0x000304b0: cmp.w r3,r1, lsl #0x1f *)
(*     197808: cmp.w r3,r1, lsl #0x1f *)
| 0x304b0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1f 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000304b4: nop *)
(*     197812: nop *)
| 0x304b4 => Some (2,
	Nop
)

(* 0x000304b6: adc.w r0,r0,r0 *)
(*     197814: adc.w r0,r0,r0 *)
| 0x304b6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000304ba: it cs *)
(*     197818: it cs *)
| 0x304ba => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000304bc: sub.cs.w r3,r3,r1, lsl #0x1f *)
(*     197820: sub.cs.w r3,r3,r1, lsl #0x1f *)
| 0x304bc => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x304c0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1f 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1f 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000304c0: cmp.w r3,r1, lsl #0x1e *)
(*     197824: cmp.w r3,r1, lsl #0x1e *)
| 0x304c0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1e 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1e 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000304c4: nop *)
(*     197828: nop *)
| 0x304c4 => Some (2,
	Nop
)

(* 0x000304c6: adc.w r0,r0,r0 *)
(*     197830: adc.w r0,r0,r0 *)
| 0x304c6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000304ca: it cs *)
(*     197834: it cs *)
| 0x304ca => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000304cc: sub.cs.w r3,r3,r1, lsl #0x1e *)
(*     197836: sub.cs.w r3,r3,r1, lsl #0x1e *)
| 0x304cc => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x304d0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1e 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1e 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000304d0: cmp.w r3,r1, lsl #0x1d *)
(*     197840: cmp.w r3,r1, lsl #0x1d *)
| 0x304d0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1d 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1d 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000304d4: nop *)
(*     197844: nop *)
| 0x304d4 => Some (2,
	Nop
)

(* 0x000304d6: adc.w r0,r0,r0 *)
(*     197846: adc.w r0,r0,r0 *)
| 0x304d6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000304da: it cs *)
(*     197850: it cs *)
| 0x304da => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000304dc: sub.cs.w r3,r3,r1, lsl #0x1d *)
(*     197852: sub.cs.w r3,r3,r1, lsl #0x1d *)
| 0x304dc => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x304e0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1d 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1d 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000304e0: cmp.w r3,r1, lsl #0x1c *)
(*     197856: cmp.w r3,r1, lsl #0x1c *)
| 0x304e0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1c 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1c 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000304e4: nop *)
(*     197860: nop *)
| 0x304e4 => Some (2,
	Nop
)

(* 0x000304e6: adc.w r0,r0,r0 *)
(*     197862: adc.w r0,r0,r0 *)
| 0x304e6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000304ea: it cs *)
(*     197866: it cs *)
| 0x304ea => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000304ec: sub.cs.w r3,r3,r1, lsl #0x1c *)
(*     197868: sub.cs.w r3,r3,r1, lsl #0x1c *)
| 0x304ec => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x304f0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1c 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1c 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000304f0: cmp.w r3,r1, lsl #0x1b *)
(*     197872: cmp.w r3,r1, lsl #0x1b *)
| 0x304f0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1b 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1b 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000304f4: nop *)
(*     197876: nop *)
| 0x304f4 => Some (2,
	Nop
)

(* 0x000304f6: adc.w r0,r0,r0 *)
(*     197878: adc.w r0,r0,r0 *)
| 0x304f6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000304fa: it cs *)
(*     197882: it cs *)
| 0x304fa => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000304fc: sub.cs.w r3,r3,r1, lsl #0x1b *)
(*     197884: sub.cs.w r3,r3,r1, lsl #0x1b *)
| 0x304fc => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30500 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1b 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1b 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030500: cmp.w r3,r1, lsl #0x1a *)
(*     197888: cmp.w r3,r1, lsl #0x1a *)
| 0x30500 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1a 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1a 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030504: nop *)
(*     197892: nop *)
| 0x30504 => Some (2,
	Nop
)

(* 0x00030506: adc.w r0,r0,r0 *)
(*     197894: adc.w r0,r0,r0 *)
| 0x30506 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003050a: it cs *)
(*     197898: it cs *)
| 0x3050a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003050c: sub.cs.w r3,r3,r1, lsl #0x1a *)
(*     197900: sub.cs.w r3,r3,r1, lsl #0x1a *)
| 0x3050c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30510 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1a 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1a 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030510: cmp.w r3,r1, lsl #0x19 *)
(*     197904: cmp.w r3,r1, lsl #0x19 *)
| 0x30510 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x19 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x19 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030514: nop *)
(*     197908: nop *)
| 0x30514 => Some (2,
	Nop
)

(* 0x00030516: adc.w r0,r0,r0 *)
(*     197910: adc.w r0,r0,r0 *)
| 0x30516 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003051a: it cs *)
(*     197914: it cs *)
| 0x3051a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003051c: sub.cs.w r3,r3,r1, lsl #0x19 *)
(*     197916: sub.cs.w r3,r3,r1, lsl #0x19 *)
| 0x3051c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30520 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x19 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x19 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030520: cmp.w r3,r1, lsl #0x18 *)
(*     197920: cmp.w r3,r1, lsl #0x18 *)
| 0x30520 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x18 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x18 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030524: nop *)
(*     197924: nop *)
| 0x30524 => Some (2,
	Nop
)

(* 0x00030526: adc.w r0,r0,r0 *)
(*     197926: adc.w r0,r0,r0 *)
| 0x30526 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003052a: it cs *)
(*     197930: it cs *)
| 0x3052a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003052c: sub.cs.w r3,r3,r1, lsl #0x18 *)
(*     197932: sub.cs.w r3,r3,r1, lsl #0x18 *)
| 0x3052c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30530 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x18 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x18 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030530: cmp.w r3,r1, lsl #0x17 *)
(*     197936: cmp.w r3,r1, lsl #0x17 *)
| 0x30530 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x17 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x17 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030534: nop *)
(*     197940: nop *)
| 0x30534 => Some (2,
	Nop
)

(* 0x00030536: adc.w r0,r0,r0 *)
(*     197942: adc.w r0,r0,r0 *)
| 0x30536 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003053a: it cs *)
(*     197946: it cs *)
| 0x3053a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003053c: sub.cs.w r3,r3,r1, lsl #0x17 *)
(*     197948: sub.cs.w r3,r3,r1, lsl #0x17 *)
| 0x3053c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30540 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x17 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x17 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030540: cmp.w r3,r1, lsl #0x16 *)
(*     197952: cmp.w r3,r1, lsl #0x16 *)
| 0x30540 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x16 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x16 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030544: nop *)
(*     197956: nop *)
| 0x30544 => Some (2,
	Nop
)

(* 0x00030546: adc.w r0,r0,r0 *)
(*     197958: adc.w r0,r0,r0 *)
| 0x30546 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003054a: it cs *)
(*     197962: it cs *)
| 0x3054a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003054c: sub.cs.w r3,r3,r1, lsl #0x16 *)
(*     197964: sub.cs.w r3,r3,r1, lsl #0x16 *)
| 0x3054c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30550 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x16 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x16 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030550: cmp.w r3,r1, lsl #0x15 *)
(*     197968: cmp.w r3,r1, lsl #0x15 *)
| 0x30550 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x15 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x15 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030554: nop *)
(*     197972: nop *)
| 0x30554 => Some (2,
	Nop
)

(* 0x00030556: adc.w r0,r0,r0 *)
(*     197974: adc.w r0,r0,r0 *)
| 0x30556 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003055a: it cs *)
(*     197978: it cs *)
| 0x3055a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003055c: sub.cs.w r3,r3,r1, lsl #0x15 *)
(*     197980: sub.cs.w r3,r3,r1, lsl #0x15 *)
| 0x3055c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30560 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x15 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x15 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030560: cmp.w r3,r1, lsl #0x14 *)
(*     197984: cmp.w r3,r1, lsl #0x14 *)
| 0x30560 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x14 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x14 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030564: nop *)
(*     197988: nop *)
| 0x30564 => Some (2,
	Nop
)

(* 0x00030566: adc.w r0,r0,r0 *)
(*     197990: adc.w r0,r0,r0 *)
| 0x30566 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003056a: it cs *)
(*     197994: it cs *)
| 0x3056a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003056c: sub.cs.w r3,r3,r1, lsl #0x14 *)
(*     197996: sub.cs.w r3,r3,r1, lsl #0x14 *)
| 0x3056c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30570 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x14 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x14 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030570: cmp.w r3,r1, lsl #0x13 *)
(*     198000: cmp.w r3,r1, lsl #0x13 *)
| 0x30570 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x13 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x13 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030574: nop *)
(*     198004: nop *)
| 0x30574 => Some (2,
	Nop
)

(* 0x00030576: adc.w r0,r0,r0 *)
(*     198006: adc.w r0,r0,r0 *)
| 0x30576 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003057a: it cs *)
(*     198010: it cs *)
| 0x3057a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003057c: sub.cs.w r3,r3,r1, lsl #0x13 *)
(*     198012: sub.cs.w r3,r3,r1, lsl #0x13 *)
| 0x3057c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30580 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x13 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x13 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030580: cmp.w r3,r1, lsl #0x12 *)
(*     198016: cmp.w r3,r1, lsl #0x12 *)
| 0x30580 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x12 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x12 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030584: nop *)
(*     198020: nop *)
| 0x30584 => Some (2,
	Nop
)

(* 0x00030586: adc.w r0,r0,r0 *)
(*     198022: adc.w r0,r0,r0 *)
| 0x30586 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003058a: it cs *)
(*     198026: it cs *)
| 0x3058a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003058c: sub.cs.w r3,r3,r1, lsl #0x12 *)
(*     198028: sub.cs.w r3,r3,r1, lsl #0x12 *)
| 0x3058c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30590 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x12 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x12 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030590: cmp.w r3,r1, lsl #0x11 *)
(*     198032: cmp.w r3,r1, lsl #0x11 *)
| 0x30590 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x11 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x11 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030594: nop *)
(*     198036: nop *)
| 0x30594 => Some (2,
	Nop
)

(* 0x00030596: adc.w r0,r0,r0 *)
(*     198038: adc.w r0,r0,r0 *)
| 0x30596 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003059a: it cs *)
(*     198042: it cs *)
| 0x3059a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003059c: sub.cs.w r3,r3,r1, lsl #0x11 *)
(*     198044: sub.cs.w r3,r3,r1, lsl #0x11 *)
| 0x3059c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x305a0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x11 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x11 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000305a0: cmp.w r3,r1, lsl #0x10 *)
(*     198048: cmp.w r3,r1, lsl #0x10 *)
| 0x305a0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x10 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x10 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000305a4: nop *)
(*     198052: nop *)
| 0x305a4 => Some (2,
	Nop
)

(* 0x000305a6: adc.w r0,r0,r0 *)
(*     198054: adc.w r0,r0,r0 *)
| 0x305a6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000305aa: it cs *)
(*     198058: it cs *)
| 0x305aa => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000305ac: sub.cs.w r3,r3,r1, lsl #0x10 *)
(*     198060: sub.cs.w r3,r3,r1, lsl #0x10 *)
| 0x305ac => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x305b0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x10 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x10 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000305b0: cmp.w r3,r1, lsl #0xf *)
(*     198064: cmp.w r3,r1, lsl #0xf *)
| 0x305b0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xf 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xf 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000305b4: nop *)
(*     198068: nop *)
| 0x305b4 => Some (2,
	Nop
)

(* 0x000305b6: adc.w r0,r0,r0 *)
(*     198070: adc.w r0,r0,r0 *)
| 0x305b6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000305ba: it cs *)
(*     198074: it cs *)
| 0x305ba => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000305bc: sub.cs.w r3,r3,r1, lsl #0xf *)
(*     198076: sub.cs.w r3,r3,r1, lsl #0xf *)
| 0x305bc => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x305c0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xf 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xf 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000305c0: cmp.w r3,r1, lsl #0xe *)
(*     198080: cmp.w r3,r1, lsl #0xe *)
| 0x305c0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xe 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xe 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000305c4: nop *)
(*     198084: nop *)
| 0x305c4 => Some (2,
	Nop
)

(* 0x000305c6: adc.w r0,r0,r0 *)
(*     198086: adc.w r0,r0,r0 *)
| 0x305c6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000305ca: it cs *)
(*     198090: it cs *)
| 0x305ca => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000305cc: sub.cs.w r3,r3,r1, lsl #0xe *)
(*     198092: sub.cs.w r3,r3,r1, lsl #0xe *)
| 0x305cc => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x305d0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xe 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xe 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000305d0: cmp.w r3,r1, lsl #0xd *)
(*     198096: cmp.w r3,r1, lsl #0xd *)
| 0x305d0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xd 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xd 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000305d4: nop *)
(*     198100: nop *)
| 0x305d4 => Some (2,
	Nop
)

(* 0x000305d6: adc.w r0,r0,r0 *)
(*     198102: adc.w r0,r0,r0 *)
| 0x305d6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000305da: it cs *)
(*     198106: it cs *)
| 0x305da => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000305dc: sub.cs.w r3,r3,r1, lsl #0xd *)
(*     198108: sub.cs.w r3,r3,r1, lsl #0xd *)
| 0x305dc => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x305e0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xd 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xd 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000305e0: cmp.w r3,r1, lsl #0xc *)
(*     198112: cmp.w r3,r1, lsl #0xc *)
| 0x305e0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xc 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xc 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000305e4: nop *)
(*     198116: nop *)
| 0x305e4 => Some (2,
	Nop
)

(* 0x000305e6: adc.w r0,r0,r0 *)
(*     198118: adc.w r0,r0,r0 *)
| 0x305e6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000305ea: it cs *)
(*     198122: it cs *)
| 0x305ea => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000305ec: sub.cs.w r3,r3,r1, lsl #0xc *)
(*     198124: sub.cs.w r3,r3,r1, lsl #0xc *)
| 0x305ec => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x305f0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xc 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xc 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000305f0: cmp.w r3,r1, lsl #0xb *)
(*     198128: cmp.w r3,r1, lsl #0xb *)
| 0x305f0 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xb 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xb 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000305f4: nop *)
(*     198132: nop *)
| 0x305f4 => Some (2,
	Nop
)

(* 0x000305f6: adc.w r0,r0,r0 *)
(*     198134: adc.w r0,r0,r0 *)
| 0x305f6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000305fa: it cs *)
(*     198138: it cs *)
| 0x305fa => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000305fc: sub.cs.w r3,r3,r1, lsl #0xb *)
(*     198140: sub.cs.w r3,r3,r1, lsl #0xb *)
| 0x305fc => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30600 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xb 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xb 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030600: cmp.w r3,r1, lsl #0xa *)
(*     198144: cmp.w r3,r1, lsl #0xa *)
| 0x30600 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xa 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xa 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030604: nop *)
(*     198148: nop *)
| 0x30604 => Some (2,
	Nop
)

(* 0x00030606: adc.w r0,r0,r0 *)
(*     198150: adc.w r0,r0,r0 *)
| 0x30606 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003060a: it cs *)
(*     198154: it cs *)
| 0x3060a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003060c: sub.cs.w r3,r3,r1, lsl #0xa *)
(*     198156: sub.cs.w r3,r3,r1, lsl #0xa *)
| 0x3060c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30610 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0xa 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0xa 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030610: cmp.w r3,r1, lsl #0x9 *)
(*     198160: cmp.w r3,r1, lsl #0x9 *)
| 0x30610 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x9 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x9 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030614: nop *)
(*     198164: nop *)
| 0x30614 => Some (2,
	Nop
)

(* 0x00030616: adc.w r0,r0,r0 *)
(*     198166: adc.w r0,r0,r0 *)
| 0x30616 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003061a: it cs *)
(*     198170: it cs *)
| 0x3061a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003061c: sub.cs.w r3,r3,r1, lsl #0x9 *)
(*     198172: sub.cs.w r3,r3,r1, lsl #0x9 *)
| 0x3061c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30620 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x9 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x9 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030620: cmp.w r3,r1, lsl #0x8 *)
(*     198176: cmp.w r3,r1, lsl #0x8 *)
| 0x30620 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x8 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x8 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030624: nop *)
(*     198180: nop *)
| 0x30624 => Some (2,
	Nop
)

(* 0x00030626: adc.w r0,r0,r0 *)
(*     198182: adc.w r0,r0,r0 *)
| 0x30626 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003062a: it cs *)
(*     198186: it cs *)
| 0x3062a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003062c: sub.cs.w r3,r3,r1, lsl #0x8 *)
(*     198188: sub.cs.w r3,r3,r1, lsl #0x8 *)
| 0x3062c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30630 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x8 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x8 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030630: cmp.w r3,r1, lsl #0x7 *)
(*     198192: cmp.w r3,r1, lsl #0x7 *)
| 0x30630 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x7 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x7 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030634: nop *)
(*     198196: nop *)
| 0x30634 => Some (2,
	Nop
)

(* 0x00030636: adc.w r0,r0,r0 *)
(*     198198: adc.w r0,r0,r0 *)
| 0x30636 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003063a: it cs *)
(*     198202: it cs *)
| 0x3063a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003063c: sub.cs.w r3,r3,r1, lsl #0x7 *)
(*     198204: sub.cs.w r3,r3,r1, lsl #0x7 *)
| 0x3063c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30640 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x7 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x7 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030640: cmp.w r3,r1, lsl #0x6 *)
(*     198208: cmp.w r3,r1, lsl #0x6 *)
| 0x30640 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x6 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x6 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030644: nop *)
(*     198212: nop *)
| 0x30644 => Some (2,
	Nop
)

(* 0x00030646: adc.w r0,r0,r0 *)
(*     198214: adc.w r0,r0,r0 *)
| 0x30646 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003064a: it cs *)
(*     198218: it cs *)
| 0x3064a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003064c: sub.cs.w r3,r3,r1, lsl #0x6 *)
(*     198220: sub.cs.w r3,r3,r1, lsl #0x6 *)
| 0x3064c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30650 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x6 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x6 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030650: cmp.w r3,r1, lsl #0x5 *)
(*     198224: cmp.w r3,r1, lsl #0x5 *)
| 0x30650 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x5 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x5 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030654: nop *)
(*     198228: nop *)
| 0x30654 => Some (2,
	Nop
)

(* 0x00030656: adc.w r0,r0,r0 *)
(*     198230: adc.w r0,r0,r0 *)
| 0x30656 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003065a: it cs *)
(*     198234: it cs *)
| 0x3065a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003065c: sub.cs.w r3,r3,r1, lsl #0x5 *)
(*     198236: sub.cs.w r3,r3,r1, lsl #0x5 *)
| 0x3065c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30660 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x5 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x5 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030660: cmp.w r3,r1, lsl #0x4 *)
(*     198240: cmp.w r3,r1, lsl #0x4 *)
| 0x30660 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x4 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x4 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030664: nop *)
(*     198244: nop *)
| 0x30664 => Some (2,
	Nop
)

(* 0x00030666: adc.w r0,r0,r0 *)
(*     198246: adc.w r0,r0,r0 *)
| 0x30666 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003066a: it cs *)
(*     198250: it cs *)
| 0x3066a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003066c: sub.cs.w r3,r3,r1, lsl #0x4 *)
(*     198252: sub.cs.w r3,r3,r1, lsl #0x4 *)
| 0x3066c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30670 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x4 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x4 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030670: cmp.w r3,r1, lsl #0x3 *)
(*     198256: cmp.w r3,r1, lsl #0x3 *)
| 0x30670 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x3 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x3 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030674: nop *)
(*     198260: nop *)
| 0x30674 => Some (2,
	Nop
)

(* 0x00030676: adc.w r0,r0,r0 *)
(*     198262: adc.w r0,r0,r0 *)
| 0x30676 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003067a: it cs *)
(*     198266: it cs *)
| 0x3067a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003067c: sub.cs.w r3,r3,r1, lsl #0x3 *)
(*     198268: sub.cs.w r3,r3,r1, lsl #0x3 *)
| 0x3067c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30680 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x3 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x3 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030680: cmp.w r3,r1, lsl #0x2 *)
(*     198272: cmp.w r3,r1, lsl #0x2 *)
| 0x30680 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x2 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x2 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030684: nop *)
(*     198276: nop *)
| 0x30684 => Some (2,
	Nop
)

(* 0x00030686: adc.w r0,r0,r0 *)
(*     198278: adc.w r0,r0,r0 *)
| 0x30686 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003068a: it cs *)
(*     198282: it cs *)
| 0x3068a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003068c: sub.cs.w r3,r3,r1, lsl #0x2 *)
(*     198284: sub.cs.w r3,r3,r1, lsl #0x2 *)
| 0x3068c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x30690 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x2 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x2 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x00030690: cmp.w r3,r1, lsl #0x1 *)
(*     198288: cmp.w r3,r1, lsl #0x1 *)
| 0x30690 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1 32)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x98280)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x98280)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0x98280))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x00030694: nop *)
(*     198292: nop *)
| 0x30694 => Some (2,
	Nop
)

(* 0x00030696: adc.w r0,r0,r0 *)
(*     198294: adc.w r0,r0,r0 *)
| 0x30696 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0003069a: it cs *)
(*     198298: it cs *)
| 0x3069a => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x0003069c: sub.cs.w r3,r3,r1, lsl #0x1 *)
(*     198300: sub.cs.w r3,r3,r1, lsl #0x1 *)
| 0x3069c => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306a0 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x1 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x1 32)) $;
	Move (V_TEMP 0xd4680) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000306a0: cmp.w r3,r1 *)
(*     198304: cmp.w r3,r1 *)
| 0x306a0 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R1) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var R_R1)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var R_R1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6f00) (BinOp OP_MINUS (Var R_R3) (Var R_R1)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6f00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000306a4: nop *)
(*     198308: nop *)
| 0x306a4 => Some (2,
	Nop
)

(* 0x000306a6: adc.w r0,r0,r0 *)
(*     198310: adc.w r0,r0,r0 *)
| 0x306a6 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x91300) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0x91400) (BinOp OP_PLUS (Var R_R0) (Var R_R0)) $;
	Move (V_TEMP 0x91480) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Var R_R0))) $;
	Move (V_TEMP 0x91500) (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Var (V_TEMP 0x91400)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0x91480))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91500)))))) $;
	Move (V_TEMP 0x91600) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R0) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 0x91680) (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var (V_TEMP 0x91400)) (Var (V_TEMP 0x91300))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91400)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x91300)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_XOR (Cast CAST_LOW 1 (Var (V_TEMP 0x91600))) (Cast CAST_LOW 1 (Var (V_TEMP 0x91680)))))) $;
	Move (V_TEMP 0xa3800) (Cast CAST_UNSIGNED 32 (Var R_CF)) $;
	Move (V_TEMP 0xa3900) (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3800))) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var (V_TEMP 0xa3900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306aa: it cs *)
(*     198314: it cs *)
| 0x306aa => Some (2,
	Move (V_TEMP 0x95d00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000306ac: sub.cs.w r3,r3,r1 *)
(*     198316: sub.cs.w r3,r3,r1 *)
| 0x306ac => Some (4,
	Move (V_TEMP 0x480) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x480))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306b0 32)
	) (* else *) (
		Nop
	) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd4680) (Var R_R1) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x000306b0: cmp.w r12,#0x0 *)
(*     198320: cmp.w r12,#0x0 *)
| 0x306b0 => Some (4,
	Move (V_TEMP 0x97780) (Word 0x0 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x97780)) (Var R_R12))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6e00) (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97780))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6e00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6e00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000306b4: it mi *)
(*     198324: it mi *)
| 0x306b4 => Some (2,
	Move (V_TEMP 0x95f00) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000306b6: rsb.mi r0,r0 *)
(*     198326: rsb.mi r0,r0 *)
| 0x306b6 => Some (2,
	Move (V_TEMP 0x680) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x680))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306b8 32)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306b8: bx lr *)
(*     198328: bx lr *)
| 0x306b8 => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x000306ba: teq.w r12,r0 *)
(*     198330: teq.w r12,r0 *)
| 0x306ba => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd9580) (BinOp OP_XOR (Var R_R12) (Var R_R0)) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xd9580)) (Word 0x0 32))) $;
	Move R_NF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xd9580)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF)))
)

(* 0x000306be: it mi *)
(*     198334: it mi *)
| 0x306be => Some (2,
	Move (V_TEMP 0x95f00) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000306c0: rsb.mi r0,r0 *)
(*     198336: rsb.mi r0,r0 *)
| 0x306c0 => Some (2,
	Move (V_TEMP 0x680) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x680))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306c2 32)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306c2: bx lr *)
(*     198338: bx lr *)
| 0x306c2 => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x000306c4: it cc *)
(*     198340: it cc *)
| 0x306c4 => Some (2,
	Move (V_TEMP 0x95e00) (BinOp OP_NEQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000306c6: mov.cc r0,#0x0 *)
(*     198342: mov.cc r0,#0x0 *)
| 0x306c6 => Some (2,
	Move (V_TEMP 0x580) (BinOp OP_EQ (Var R_CF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x580))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306c8 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (Word 0x0 32) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306c8: itt eq *)
(*     198344: itt eq *)
| 0x306c8 => Some (2,
	Move (V_TEMP 0x95b00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000306ca: asr.eq.w r0,r12, asr #0x1f *)
(*     198346: asr.eq.w r0,r12, asr #0x1f *)
| 0x306ca => Some (4,
	Move (V_TEMP 0x280) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1300) (UnOp OP_NOT (Var (V_TEMP 0x280))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1300))) (
		Jmp (Word 0x306ce 32)
	) (* else *) (
		Nop
	) $;
	Move (V_TEMP 0x98b00) (BinOp OP_MINUS (Word 0x1f 32) (Word 0x1 32)) $;
	Move (V_TEMP 0x98b80) (BinOp OP_RSHIFT (Var R_R12) (Var (V_TEMP 0x98b00))) $;
	Move (V_TEMP 0x98c80) (BinOp OP_AND (Var (V_TEMP 0x98b80)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98c80)) (Word 0 32))) $;
	Move (V_TEMP 0x98e00) (BinOp OP_ARSHIFT (Var R_R12) (Word 0x1f 32)) $;
	Move R_R0 (Var (V_TEMP 0x98e00)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306ce: orr.eq r0,r0,#0x1 *)
(*     198350: orr.eq r0,r0,#0x1 *)
| 0x306ce => Some (4,
	Move (V_TEMP 0x97780) (Word 0x1 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0x280) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x280))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306d2 32)
	) (* else *) (
		Nop
	) $;
	Move R_R0 (BinOp OP_OR (Var R_R0) (Var (V_TEMP 0x97780))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306d2: bx lr *)
(*     198354: bx lr *)
| 0x306d2 => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x000306d4: clz r2,r1 *)
(*     198356: clz r2,r1 *)
| 0x306d4 => Some (4,
	Move R_R2 (Cast CAST_UNSIGNED 32 (BinOp OP_MINUS (Word 32 32) (UnOp OP_BITWIDTH (Var R_R1))))
)

(* 0x000306d8: rsb.w r2,r2,#0x1f *)
(*     198360: rsb.w r2,r2,#0x1f *)
| 0x306d8 => Some (4,
	Move (V_TEMP 0x97780) (Word 0x1f 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R2) (Var (V_TEMP 0x97780)))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x97780)) (Var R_R2)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x97780)) (Var R_R2)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_MINUS (Var (V_TEMP 0x97780)) (Var R_R2)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32)))
)

(* 0x000306dc: cmp.w r12,#0x0 *)
(*     198364: cmp.w r12,#0x0 *)
| 0x306dc => Some (4,
	Move (V_TEMP 0x97780) (Word 0x0 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x97780)) (Var R_R12))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6e00) (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97780))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6e00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6e00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x000306e0: lsr.w r0,r3,r2 *)
(*     198368: lsr.w r0,r3,r2 *)
| 0x306e0 => Some (4,
	Move (V_TEMP 0xad380) (BinOp OP_AND (Var R_R2) (Word 0xff 32)) $;
	Move (V_TEMP 0xac800) (BinOp OP_MINUS (Var (V_TEMP 0xad380)) (Word 0x1 32)) $;
	Move (V_TEMP 0xac880) (BinOp OP_RSHIFT (Var R_R3) (Var (V_TEMP 0xac800))) $;
	Move (V_TEMP 0xac980) (BinOp OP_AND (Var (V_TEMP 0xac880)) (Word 0x1 32)) $;
	Move (V_TEMP 0xaca00) (BinOp OP_EQ (Var (V_TEMP 0xad380)) (Word 0x0 32)) $;
	Move (V_TEMP 0xaca80) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xaca00)) (Var R_CF))) $;
	Move (V_TEMP 0xacb00) (BinOp OP_NEQ (Var (V_TEMP 0xad380)) (Word 0x0 32)) $;
	Move (V_TEMP 0xacb80) (BinOp OP_NEQ (Var (V_TEMP 0xac980)) (Word 0x0 32)) $;
	Move (V_TEMP 0xacc00) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xacb00)) (Var (V_TEMP 0xacb80)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0xaca80))) (Cast CAST_LOW 1 (Var (V_TEMP 0xacc00)))))) $;
	Move R_R0 (BinOp OP_RSHIFT (Var R_R3) (Var (V_TEMP 0xad380))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306e4: it mi *)
(*     198372: it mi *)
| 0x306e4 => Some (2,
	Move (V_TEMP 0x95f00) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8)))
)

(* 0x000306e6: rsb.mi r0,r0 *)
(*     198374: rsb.mi r0,r0 *)
| 0x306e6 => Some (2,
	Move (V_TEMP 0x680) (BinOp OP_NEQ (Var R_NF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	Move (V_TEMP 0x1380) (UnOp OP_NOT (Var (V_TEMP 0x680))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x1380))) (
		Jmp (Word 0x306e8 32)
	) (* else *) (
		Nop
	) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Word 0x0 32) (Var R_R0)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x000306e8: bx lr *)
(*     198376: bx lr *)
| 0x306e8 => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx FUN_0003046e_armv7.
Proof. Picinae_typecheck. Qed.

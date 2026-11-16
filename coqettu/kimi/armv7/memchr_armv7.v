(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: memchr
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition memchr_armv7 : program := fun _ a => match a with

(* 0x0005b042: push {r4,r5,r6,r7,lr} *)
(*     372802: push {r4,r5,r6,r7,lr} *)
| 0x5b042 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R7)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R6)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R5)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R4)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0005b044: uxtb r1,r1 *)
(*     372804: uxtb r1,r1 *)
| 0x5b044 => Some (2,
	Move (V_TEMP 0xe5d80) (Cast CAST_LOW 8 (BinOp OP_RSHIFT (Var R_R1) (Word 0 32))) $;
	Move R_R1 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xe5d80)))
)

(* 0x0005b046: b 0x0005b04c *)
(*     372806: b 0x0005b04c *)
| 0x5b046 => Some (2,
	Jmp (Word 0x5b04c 32)
)

(* 0x0005b048: adds r0,#0x1 *)
(*     372808: adds r0,#0x1 *)
| 0x5b048 => Some (2,
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

(* 0x0005b04a: subs r2,#0x1 *)
(*     372810: subs r2,#0x1 *)
| 0x5b04a => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x1 32) (Var R_R2))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R2) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R2) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_MINUS (Var R_R2) (Word 0x1 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b04c: lsls r3,r0,#0x1e *)
(*     372812: lsls r3,r0,#0x1e *)
| 0x5b04c => Some (2,
	Move (V_TEMP 0xac100) (BinOp OP_MINUS (Word 0x1e 32) (Word 0x1 32)) $;
	Move (V_TEMP 0xac180) (BinOp OP_LSHIFT (Var R_R0) (Var (V_TEMP 0xac100))) $;
	Move (V_TEMP 0xac280) (BinOp OP_AND (Var (V_TEMP 0xac180)) (Word 0x80000000 32)) $;
	Move (V_TEMP 0xac300) (BinOp OP_EQ (Word 0x1e 32) (Word 0x0 32)) $;
	Move (V_TEMP 0xac380) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xac300)) (Var R_CF))) $;
	Move (V_TEMP 0xac400) (BinOp OP_NEQ (Word 0x1e 32) (Word 0x0 32)) $;
	Move (V_TEMP 0xac480) (BinOp OP_NEQ (Var (V_TEMP 0xac280)) (Word 0x0 32)) $;
	Move (V_TEMP 0xac500) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xac400)) (Var (V_TEMP 0xac480)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0xac380))) (Cast CAST_LOW 1 (Var (V_TEMP 0xac500)))))) $;
	Move R_R3 (BinOp OP_LSHIFT (Var R_R0) (Word 0x1e 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005b04e: mov r7,r0 *)
(*     372814: mov r7,r0 *)
| 0x5b04e => Some (2,
	Move R_R7 (Var R_R0)
)

(* 0x0005b050: beq 0x0005b0a8 *)
(*     372816: beq 0x0005b0a8 *)
| 0x5b050 => Some (2,
	Move (V_TEMP 0x93a00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93a00))) (
		Jmp (Word 0x5b0a8 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b052: cbz r2,0x0005b090 *)
(*     372818: cbz r2,0x0005b090 *)
| 0x5b052 => Some (2,
	Move (V_TEMP 0xa6380) (BinOp OP_EQ (Var R_R2) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6380))) (
		Jmp (Word 0x5b090 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b054: ldrb.w r12,[r0,#0x0] *)
(*     372820: ldrb.w r12,[r0,#0x0] *)
| 0x5b054 => Some (4,
	Move (V_TEMP 0xa1a80) (BinOp OP_PLUS (Var R_R0) (Word 0x0 32)) $;
	Move (V_TEMP 0xa8f00) (Load (Var V_MEM32) (Var (V_TEMP 0xa1a80)) LittleE 1) $;
	Move R_R12 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa8f00)))
)

(* 0x0005b058: cmp r12,r1 *)
(*     372824: cmp r12,r1 *)
| 0x5b058 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R1) (Var R_R12))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var R_R1)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var R_R1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa7100) (BinOp OP_MINUS (Var R_R12) (Var R_R1)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa7100)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa7100)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b05a: bne 0x0005b048 *)
(*     372826: bne 0x0005b048 *)
| 0x5b05a => Some (2,
	Move (V_TEMP 0x93b00) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93b00))) (
		Jmp (Word 0x5b048 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b05c: ldrb r3,[r0,#0x0] *)
(*     372828: ldrb r3,[r0,#0x0] *)
| 0x5b05c => Some (2,
	Move (V_TEMP 0xa2880) (BinOp OP_PLUS (Var R_R0) (Word 0x0 32)) $;
	Move (V_TEMP 0xa7980) (Load (Var V_MEM32) (Var (V_TEMP 0xa2880)) LittleE 1) $;
	Move R_R3 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa7980)))
)

(* 0x0005b05e: cmp r3,r1 *)
(*     372830: cmp r3,r1 *)
| 0x5b05e => Some (2,
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

(* 0x0005b060: beq 0x0005b090 *)
(*     372832: beq 0x0005b090 *)
| 0x5b060 => Some (2,
	Move (V_TEMP 0x93a00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93a00))) (
		Jmp (Word 0x5b090 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b062: add.w r3,r1,r1, lsl #0x8 *)
(*     372834: add.w r3,r1,r1, lsl #0x8 *)
| 0x5b062 => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x8 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R1) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R1) (Word 0x8 32)) $;
	Move (V_TEMP 0xa3c00) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R1) (Var (V_TEMP 0xa3c00))) (Var R_R1))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R1) (Var (V_TEMP 0xa3c00))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xa3c00)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_PLUS (Var R_R1) (Var (V_TEMP 0xa3c00))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0005b066: bic r4,r2,#0x3 *)
(*     372838: bic r4,r2,#0x3 *)
| 0x5b066 => Some (4,
	Move (V_TEMP 0x97780) (Word 0x3 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xa5700) (UnOp OP_NOT (Var (V_TEMP 0x97780))) $;
	Move R_R4 (BinOp OP_AND (Var R_R2) (Var (V_TEMP 0xa5700))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R4) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R4) (Word 0x0 32)))
)

(* 0x0005b06a: add.w r3,r3,r3, lsl #0x10 *)
(*     372842: add.w r3,r3,r3, lsl #0x10 *)
| 0x5b06a => Some (4,
	Move (V_TEMP 0x97f80) (BinOp OP_MINUS (Word 0x20 32) (Word 0x10 32)) $;
	Move (V_TEMP 0x98000) (BinOp OP_RSHIFT (Var R_R3) (Var (V_TEMP 0x97f80))) $;
	Move (V_TEMP 0x98100) (BinOp OP_AND (Var (V_TEMP 0x98000)) (Word 0x1 32)) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (BinOp OP_RSHIFT (Var (V_TEMP 0x98100)) (Word 0 32))) $;
	Move (V_TEMP 0x98280) (BinOp OP_LSHIFT (Var R_R3) (Word 0x10 32)) $;
	Move (V_TEMP 0xa3c00) (Var (V_TEMP 0x98280)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0xa3c00))) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0xa3c00))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xa3c00)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0xa3c00))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0005b06e: add r4,r0 *)
(*     372846: add r4,r0 *)
| 0x5b06e => Some (2,
	Move R_R4 (BinOp OP_PLUS (Var R_R4) (Var R_R0))
)

(* 0x0005b070: adds r6,r2,r0 *)
(*     372848: adds r6,r2,r0 *)
| 0x5b070 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R2) (Var R_R0)) (Var R_R2))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R2) (Var R_R0)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R6 (BinOp OP_PLUS (Var R_R2) (Var R_R0)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R6) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R6) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b072: cmp r0,r4 *)
(*     372850: cmp r0,r4 *)
| 0x5b072 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R4) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var R_R4)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var R_R4)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R4) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa7000) (BinOp OP_MINUS (Var R_R0) (Var R_R4)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa7000)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa7000)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b074: mov r7,r0 *)
(*     372852: mov r7,r0 *)
| 0x5b074 => Some (2,
	Move R_R7 (Var R_R0)
)

(* 0x0005b076: beq 0x0005b08e *)
(*     372854: beq 0x0005b08e *)
| 0x5b076 => Some (2,
	Move (V_TEMP 0x93a00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93a00))) (
		Jmp (Word 0x5b08e 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b078: ldr.w r2,[r0],#0x4 *)
(*     372856: ldr.w r2,[r0],#0x4 *)
| 0x5b078 => Some (4,
	Move (V_TEMP 0xa1c00) (Var R_R0) $;
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Word 0x4 32)) $;
	Move R_R2 (Load (Var V_MEM32) (Var (V_TEMP 0xa1c00)) LittleE 4)
)

(* 0x0005b07c: eor.w r12,r3,r2 *)
(*     372860: eor.w r12,r3,r2 *)
| 0x5b07c => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_R12 (BinOp OP_XOR (Var R_R3) (Var R_R2)) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R12) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R12) (Word 0x0 32)))
)

(* 0x0005b080: sub.w lr,r12,#0x1010101 *)
(*     372864: sub.w lr,r12,#0x1010101 *)
| 0x5b080 => Some (4,
	Move (V_TEMP 0x97900) (Word 0x1010101 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x97900)) (Var R_R12))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97900))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97900))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97900)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_LR (BinOp OP_MINUS (Var R_R12) (Var (V_TEMP 0x97900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_LR) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_LR) (Word 0x0 32)))
)

(* 0x0005b084: bic.w r12,lr,r12 *)
(*     372868: bic.w r12,lr,r12 *)
| 0x5b084 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xa5800) (UnOp OP_NOT (Var R_R12)) $;
	Move R_R12 (BinOp OP_AND (Var R_LR) (Var (V_TEMP 0xa5800))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R12) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R12) (Word 0x0 32)))
)

(* 0x0005b088: tst r12,#0x80808080 *)
(*     372872: tst r12,#0x80808080 *)
| 0x5b088 => Some (4,
	Move (V_TEMP 0x97900) (Word 0x80808080 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd9680) (BinOp OP_AND (Var R_R12) (Var (V_TEMP 0x97900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xd9680)) (Word 0x0 32))) $;
	Move R_NF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xd9680)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF)))
)

(* 0x0005b08c: beq 0x0005b072 *)
(*     372876: beq 0x0005b072 *)
| 0x5b08c => Some (2,
	Move (V_TEMP 0x93a00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93a00))) (
		Jmp (Word 0x5b072 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b08e: subs r2,r6,r7 *)
(*     372878: subs r2,r6,r7 *)
| 0x5b08e => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R7) (Var R_R6))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R6) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R6) (Var R_R7)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R6) (Var R_R7)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R7) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_MINUS (Var R_R6) (Var R_R7)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b090: mov r3,r7 *)
(*     372880: mov r3,r7 *)
| 0x5b090 => Some (2,
	Move R_R3 (Var R_R7)
)

(* 0x0005b092: cbz r2,0x0005b0ae *)
(*     372882: cbz r2,0x0005b0ae *)
| 0x5b092 => Some (2,
	Move (V_TEMP 0xa6380) (BinOp OP_EQ (Var R_R2) (Word 0x0 32)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xa6380))) (
		Jmp (Word 0x5b0ae 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b094: ldrb.w r12,[r3,#0x0] *)
(*     372884: ldrb.w r12,[r3,#0x0] *)
| 0x5b094 => Some (4,
	Move (V_TEMP 0xa1a80) (BinOp OP_PLUS (Var R_R3) (Word 0x0 32)) $;
	Move (V_TEMP 0xa8f00) (Load (Var V_MEM32) (Var (V_TEMP 0xa1a80)) LittleE 1) $;
	Move R_R12 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa8f00)))
)

(* 0x0005b098: mov r0,r3 *)
(*     372888: mov r0,r3 *)
| 0x5b098 => Some (2,
	Move R_R0 (Var R_R3)
)

(* 0x0005b09a: cmp r12,r1 *)
(*     372890: cmp r12,r1 *)
| 0x5b09a => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var R_R1) (Var R_R12))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R12) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var R_R1)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R12) (Var R_R1)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R1) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa7100) (BinOp OP_MINUS (Var R_R12) (Var R_R1)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa7100)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa7100)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b09c: add.w r2,r2,#0xffffffff *)
(*     372892: add.w r2,r2,#0xffffffff *)
| 0x5b09c => Some (4,
	Move (V_TEMP 0x97900) (Word 0xffffffff 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R2) (Var (V_TEMP 0x97900))) (Var R_R2))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R2) (Var (V_TEMP 0x97900))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97900)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_PLUS (Var R_R2) (Var (V_TEMP 0x97900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32)))
)

(* 0x0005b0a0: add.w r3,r3,#0x1 *)
(*     372896: add.w r3,r3,#0x1 *)
| 0x5b0a0 => Some (4,
	Move (V_TEMP 0x97780) (Word 0x1 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0x97780))) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0x97780))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0005b0a4: bne 0x0005b092 *)
(*     372900: bne 0x0005b092 *)
| 0x5b0a4 => Some (2,
	Move (V_TEMP 0x93b00) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93b00))) (
		Jmp (Word 0x5b092 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b0a6: b 0x0005b0b0 *)
(*     372902: b 0x0005b0b0 *)
| 0x5b0a6 => Some (2,
	Jmp (Word 0x5b0b0 32)
)

(* 0x0005b0a8: cmp r2,#0x0 *)
(*     372904: cmp r2,#0x0 *)
| 0x5b0a8 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Word 0x0 32) (Var R_R2))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R2) (Word 0x0 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R2) (Word 0x0 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x0 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0xa6d00) (BinOp OP_MINUS (Var R_R2) (Word 0x0 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xa6d00)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b0aa: bne 0x0005b05c *)
(*     372906: bne 0x0005b05c *)
| 0x5b0aa => Some (2,
	Move (V_TEMP 0x93b00) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93b00))) (
		Jmp (Word 0x5b05c 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b0ac: b 0x0005b090 *)
(*     372908: b 0x0005b090 *)
| 0x5b0ac => Some (2,
	Jmp (Word 0x5b090 32)
)

(* 0x0005b0ae: mov r0,r2 *)
(*     372910: mov r0,r2 *)
| 0x5b0ae => Some (2,
	Move R_R0 (Var R_R2)
)

(* 0x0005b0b0: pop {r4,r5,r6,r7,pc} *)
(*     372912: pop {r4,r5,r6,r7,pc} *)
| 0x5b0b0 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_R4 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_R5 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_R6 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_R7 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
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

Theorem welltyped: welltyped_prog arm7typctx memchr_armv7.
Proof. Picinae_typecheck. Qed.

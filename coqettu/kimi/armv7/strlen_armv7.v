(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: strlen
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strlen_armv7 : program := fun _ a => match a with

(* 0x0005b962: mov r12,r0 *)
(*     375138: mov r12,r0 *)
| 0x5b962 => Some (2,
	Move R_R12 (Var R_R0)
)

(* 0x0005b964: mov r3,r0 *)
(*     375140: mov r3,r0 *)
| 0x5b964 => Some (2,
	Move R_R3 (Var R_R0)
)

(* 0x0005b966: lsls r2,r3,#0x1e *)
(*     375142: lsls r2,r3,#0x1e *)
| 0x5b966 => Some (2,
	Move (V_TEMP 0xac100) (BinOp OP_MINUS (Word 0x1e 32) (Word 0x1 32)) $;
	Move (V_TEMP 0xac180) (BinOp OP_LSHIFT (Var R_R3) (Var (V_TEMP 0xac100))) $;
	Move (V_TEMP 0xac280) (BinOp OP_AND (Var (V_TEMP 0xac180)) (Word 0x80000000 32)) $;
	Move (V_TEMP 0xac300) (BinOp OP_EQ (Word 0x1e 32) (Word 0x0 32)) $;
	Move (V_TEMP 0xac380) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xac300)) (Var R_CF))) $;
	Move (V_TEMP 0xac400) (BinOp OP_NEQ (Word 0x1e 32) (Word 0x0 32)) $;
	Move (V_TEMP 0xac480) (BinOp OP_NEQ (Var (V_TEMP 0xac280)) (Word 0x0 32)) $;
	Move (V_TEMP 0xac500) (Cast CAST_UNSIGNED 8 (BinOp OP_AND (Var (V_TEMP 0xac400)) (Var (V_TEMP 0xac480)))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Cast CAST_LOW 1 (Var (V_TEMP 0xac380))) (Cast CAST_LOW 1 (Var (V_TEMP 0xac500)))))) $;
	Move R_R2 (BinOp OP_LSHIFT (Var R_R3) (Word 0x1e 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF)))
)

(* 0x0005b968: beq 0x0005b97a *)
(*     375144: beq 0x0005b97a *)
| 0x5b968 => Some (2,
	Move (V_TEMP 0x93a00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93a00))) (
		Jmp (Word 0x5b97a 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b96a: mov r2,r3 *)
(*     375146: mov r2,r3 *)
| 0x5b96a => Some (2,
	Move R_R2 (Var R_R3)
)

(* 0x0005b96c: ldrb r1,[r2,#0x0] *)
(*     375148: ldrb r1,[r2,#0x0] *)
| 0x5b96c => Some (2,
	Move (V_TEMP 0xa2880) (BinOp OP_PLUS (Var R_R2) (Word 0x0 32)) $;
	Move (V_TEMP 0xa7980) (Load (Var V_MEM32) (Var (V_TEMP 0xa2880)) LittleE 1) $;
	Move R_R1 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa7980)))
)

(* 0x0005b96e: adds r3,#0x1 *)
(*     375150: adds r3,#0x1 *)
| 0x5b96e => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R3) (Word 0x1 32)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R3) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_PLUS (Var R_R3) (Word 0x1 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b970: cmp r1,#0x0 *)
(*     375152: cmp r1,#0x0 *)
| 0x5b970 => Some (2,
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

(* 0x0005b972: bne 0x0005b966 *)
(*     375154: bne 0x0005b966 *)
| 0x5b972 => Some (2,
	Move (V_TEMP 0x93b00) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93b00))) (
		Jmp (Word 0x5b966 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b974: sub.w r0,r2,r12 *)
(*     375156: sub.w r0,r2,r12 *)
| 0x5b974 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd4680) (Var R_R12) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R2))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R2) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R2) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Var R_R2) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005b978: bx lr *)
(*     375160: bx lr *)
| 0x5b978 => Some (2,
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_LR) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_LR) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

(* 0x0005b97a: ldr r0,[r3,#0x0] *)
(*     375162: ldr r0,[r3,#0x0] *)
| 0x5b97a => Some (2,
	Move (V_TEMP 0xa2680) (BinOp OP_PLUS (Var R_R3) (Word 0x0 32)) $;
	Move R_R0 (Load (Var V_MEM32) (Var (V_TEMP 0xa2680)) LittleE 4)
)

(* 0x0005b97c: mov r2,r3 *)
(*     375164: mov r2,r3 *)
| 0x5b97c => Some (2,
	Move R_R2 (Var R_R3)
)

(* 0x0005b97e: sub.w r1,r0,#0x1010101 *)
(*     375166: sub.w r1,r0,#0x1010101 *)
| 0x5b97e => Some (4,
	Move (V_TEMP 0x97900) (Word 0x1010101 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0x97900)) (Var R_R0))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R0) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97900))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97900))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97900)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R1 (BinOp OP_MINUS (Var R_R0) (Var (V_TEMP 0x97900))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32)))
)

(* 0x0005b982: bic.w r1,r1,r0 *)
(*     375170: bic.w r1,r1,r0 *)
| 0x5b982 => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xa5800) (UnOp OP_NOT (Var R_R0)) $;
	Move R_R1 (BinOp OP_AND (Var R_R1) (Var (V_TEMP 0xa5800))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_VF))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R1) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R1) (Word 0x0 32)))
)

(* 0x0005b986: tst r1,#0x80808080 *)
(*     375174: tst r1,#0x80808080 *)
| 0x5b986 => Some (4,
	Move (V_TEMP 0x97900) (Word 0x80808080 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd9680) (BinOp OP_AND (Var R_R1) (Var (V_TEMP 0x97900))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0xd9680)) (Word 0x0 32))) $;
	Move R_NF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0xd9680)) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_SHIFTCF)))
)

(* 0x0005b98a: add.w r3,r3,#0x4 *)
(*     375178: add.w r3,r3,#0x4 *)
| 0x5b98a => Some (4,
	Move (V_TEMP 0x97780) (Word 0x4 32) $;
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0x97780))) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0x97780))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x97780)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R3 (BinOp OP_PLUS (Var R_R3) (Var (V_TEMP 0x97780))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R3) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R3) (Word 0x0 32)))
)

(* 0x0005b98e: beq 0x0005b97a *)
(*     375182: beq 0x0005b97a *)
| 0x5b98e => Some (2,
	Move (V_TEMP 0x93a00) (BinOp OP_NEQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93a00))) (
		Jmp (Word 0x5b97a 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b990: mov r3,r2 *)
(*     375184: mov r3,r2 *)
| 0x5b990 => Some (2,
	Move R_R3 (Var R_R2)
)

(* 0x0005b992: ldrb r1,[r3,#0x0] *)
(*     375186: ldrb r1,[r3,#0x0] *)
| 0x5b992 => Some (2,
	Move (V_TEMP 0xa2880) (BinOp OP_PLUS (Var R_R3) (Word 0x0 32)) $;
	Move (V_TEMP 0xa7980) (Load (Var V_MEM32) (Var (V_TEMP 0xa2880)) LittleE 1) $;
	Move R_R1 (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0xa7980)))
)

(* 0x0005b994: adds r2,#0x1 *)
(*     375188: adds r2,#0x1 *)
| 0x5b994 => Some (2,
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LT (BinOp OP_PLUS (Var R_R2) (Word 0x1 32)) (Var R_R2))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_R2) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R2) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R2 (BinOp OP_PLUS (Var R_R2) (Word 0x1 32)) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R2) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R2) (Word 0x0 32))) $;
	Move R_CF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPCF))) $;
	Move R_ZF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPZF))) $;
	Move R_NF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPNF))) $;
	Move R_VF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_TMPVF)))
)

(* 0x0005b996: cmp r1,#0x0 *)
(*     375190: cmp r1,#0x0 *)
| 0x5b996 => Some (2,
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

(* 0x0005b998: bne 0x0005b990 *)
(*     375192: bne 0x0005b990 *)
| 0x5b998 => Some (2,
	Move (V_TEMP 0x93b00) (BinOp OP_EQ (Var R_ZF) (Cast CAST_LOW 1 (Word 0x0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x93b00))) (
		Jmp (Word 0x5b990 32)
	) (* else *) (
		Nop
	)
)

(* 0x0005b99a: sub.w r0,r3,r12 *)
(*     375194: sub.w r0,r3,r12 *)
| 0x5b99a => Some (4,
	Move R_SHIFTCF (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_CF))) $;
	Move (V_TEMP 0xd4680) (Var R_R12) $;
	Move R_TMPCF (Cast CAST_LOW 1 (BinOp OP_LE (Var (V_TEMP 0xd4680)) (Var R_R3))) $;
	Move R_TMPVF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_R3) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0xd4680)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_R0 (BinOp OP_MINUS (Var R_R3) (Var (V_TEMP 0xd4680))) $;
	Move R_TMPNF (Cast CAST_LOW 1 (BinOp OP_SLT (Var R_R0) (Word 0x0 32))) $;
	Move R_TMPZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var R_R0) (Word 0x0 32)))
)

(* 0x0005b99e: bx lr *)
(*     375198: bx lr *)
| 0x5b99e => Some (2,
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

Theorem welltyped: welltyped_prog arm7typctx strlen_armv7.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq *)

(* '--commentout' flag was used. Be careful in your proofs if you are reasoning about anything affected by the commented-out registers/instructions. *)

Require Import Picinae_armv8_pcode.
Require Import NArith.
Open Scope N.

Definition musl_armv8_a_strspn_armv8 : program := fun _ a => match a with

(* 0x41300000: adrp x2, 0x41300000 1093664768 *)
| 0x41300000 => Some (4,
	Move R_X2 (Word 0x41300000 64)
)

(* 0x41300004: add x2, x2, #0xb0 *)
| 0x41300004 => Some (4,
	Move (V_TEMP 73344) (Word 176 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 73344))) (Var R_X2))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 73344))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X2) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 73344)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 73600) (BinOp OP_PLUS (Var R_X2) (Var (V_TEMP 73344))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_X2 (Var (V_TEMP 73600))
)

(* 0x41300008: sub sp, sp, #0x20 *)
| 0x41300008 => Some (4,
	Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 32 64))
)

(* 0x4130000c: mov x3, sp *)
| 0x4130000c => Some (4,
	Move R_X3 (Var R_SP)
)

(* 0x41300010: ld1 {v0.16B, v1.16B}, [x2] *)
| 0x41300010 => Some (4,
	(* Move R_TMP_LDXN (Var R_X2) *)
	Nop $;
	(* Move R_Z0 (Concat (Cast CAST_HIGH 248 (Var R_Z0)) (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1)) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_H0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_S0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_S0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_D0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_D0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_D0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_D0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q0 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Z1 (Concat (Cast CAST_HIGH 248 (Var R_Z1)) (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1)) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_H1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_S1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_S1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_D1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_D1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_D1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_D1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move R_Q1 (Load (Var V_MEM64) (Var R_TMP_LDXN) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop
)

(* 0x41300014: ldrb w2, [x1] *)
| 0x41300014 => Some (4,
	Move (V_TEMP 26240) (Var R_X1) $;
	Move (V_TEMP 167680) (Load (Var V_MEM64) (Var (V_TEMP 26240)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 167680)))
)

(* 0x41300018: st1 {v0.16B, v1.16B}, [x3] *)
| 0x41300018 => Some (4,
	(* Move R_TMP_LDXN (Var R_X3) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Extract 7 0 (Var R_Z0)) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_H0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_S0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_S0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_D0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_D0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_D0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_D0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q0) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Extract 7 0 (Var R_Z1)) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_H1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_S1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_S1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_D1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_D1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_D1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_D1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop $;
	(* Move V_MEM64 (Store (Var V_MEM64) (Var R_TMP_LDXN) (Var R_Q1) LittleE 1) *)
	Nop $;
	(* Move R_TMP_LDXN (BinOp OP_PLUS (Var R_TMP_LDXN) (Word 1 64)) *)
	Nop
)

(* 0x4130001c: cbz w2, 0x4130009c *)
| 0x4130001c => Some (4,
	Move (V_TEMP 102144) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0 32))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 102144))) (
		Jmp (Word 1093664924 64)
	) (* else *) (
		Nop
	)
)

(* 0x41300020: ldrb w4, [x1, #0x1] *)
| 0x41300020 => Some (4,
	Move (V_TEMP 25088) (BinOp OP_PLUS (Var R_X1) (Word 1 64)) $;
	Move (V_TEMP 167680) (Load (Var V_MEM64) (Var (V_TEMP 25088)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 167680)))
)

(* 0x41300024: cbz w4, 0x4130006c *)
| 0x41300024 => Some (4,
	Move (V_TEMP 102144) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_X4)) (Word 0 32))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 102144))) (
		Jmp (Word 1093664876 64)
	) (* else *) (
		Nop
	)
)

(* 0x41300028: mov x6, #0x1 *)
| 1093664808 => Some (4,
	Move R_X6 (Word 1 64)
)

(* 0x4130002c: ldrb w2, [x1] *)
| 1093664812 => Some (4,
	Move (V_TEMP 26240) (Var R_X1) $;
	Move (V_TEMP 167680) (Load (Var V_MEM64) (Var (V_TEMP 26240)) LittleE 1) $;
	Move R_X2 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 167680)))
)

(* 0x41300030: cbz w2, 0x41300094 *)
| 1093664816 => Some (4,
	Move (V_TEMP 102144) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_X2)) (Word 0 32))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 102144))) (
		Jmp (Word 1093664916 64)
	) (* else *) (
		Nop
	)
)

(* 0x41300034: ubfx x4, x2, #0x6, #0x2 *)
| 1093664820 => Some (4,
	Move (V_TEMP 282112) (Var R_X2) $;
	Move (V_TEMP 282240) (BinOp OP_RSHIFT (Var (V_TEMP 282112)) (Word 6 64)) $;
	Move (V_TEMP 282368) (BinOp OP_MINUS (Word 64 64) (Word 6 64)) $;
	Move (V_TEMP 282496) (BinOp OP_LSHIFT (Var (V_TEMP 282112)) (Var (V_TEMP 282368))) $;
	Move (V_TEMP 282624) (BinOp OP_OR (Var (V_TEMP 282240)) (Var (V_TEMP 282496))) $;
	Move (V_TEMP 282880) (BinOp OP_AND (Var (V_TEMP 282624)) (Word 18158513697557839875 64)) $;
	Move R_X4 (BinOp OP_AND (Var (V_TEMP 282880)) (Word 3 64))
)

(* 0x41300038: add x1, x1, #0x1 *)
| 1093664824 => Some (4,
	Move (V_TEMP 73344) (Word 1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 73344)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 73600) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_X1 (Var (V_TEMP 73600))
)

(* 0x4130003c: lsl x2, x6, x2 *)
| 1093664828 => Some (4,
	Move (V_TEMP 177920) (BinOp OP_AND (Var R_X2) (Word 63 64)) $;
	Move R_X2 (BinOp OP_LSHIFT (Var R_X6) (Var (V_TEMP 177920)))
)

(* 0x41300040: ldr x5, [x3, x4, LSL #0x3] *)
| 1093664832 => Some (4,
	Move (V_TEMP 23040) (Var R_X4) $;
	Move (V_TEMP 28928) (Var (V_TEMP 23040)) $;
	Move (V_TEMP 28928) (BinOp OP_LSHIFT (Var (V_TEMP 28928)) (Word 3 64)) $;
	Move (V_TEMP 30080) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 28928))) $;
	Move R_X5 (Load (Var V_MEM64) (Var (V_TEMP 30080)) LittleE 8)
)

(* 0x41300044: orr x2, x2, x5 *)
| 1093664836 => Some (4,
	Move R_X2 (BinOp OP_OR (Var R_X2) (Var R_X5))
)

(* 0x41300048: str x2, [x3, x4, LSL #0x3] *)
| 1093664840 => Some (4,
	Move (V_TEMP 252032) (Var R_X2) $;
	Move (V_TEMP 23040) (Var R_X4) $;
	Move (V_TEMP 28928) (Var (V_TEMP 23040)) $;
	Move (V_TEMP 28928) (BinOp OP_LSHIFT (Var (V_TEMP 28928)) (Word 3 64)) $;
	Move (V_TEMP 30080) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 28928))) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 30080)) (Var (V_TEMP 252032)) LittleE 8)
)

(* 0x4130004c: b 0x4130002c *)
| 1093664844 => Some (4,
	Jmp (Word 1093664812 64)
)

(* 0x41300050: add x1, x1, #0x1 *)
| 1093664848 => Some (4,
	Move (V_TEMP 73344) (Word 1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 73344)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 73600) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_X1 (Var (V_TEMP 73600))
)

(* 0x41300054: ldrb w3, [x1] *)
| 1093664852 => Some (4,
	Move (V_TEMP 26240) (Var R_X1) $;
	Move (V_TEMP 167680) (Load (Var V_MEM64) (Var (V_TEMP 26240)) LittleE 1) $;
	Move R_X3 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 167680)))
)

(* 0x41300058: cmp w3, w2 *)
| 1093664856 => Some (4,
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LE (Extract 31 0 (Var R_X2)) (Extract 31 0 (Var R_X3)))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X3)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X2))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 31 32)) (Word 1 32))) (Word 1 32)))) $;
	Move (V_TEMP 136448) (BinOp OP_MINUS (Extract 31 0 (Var R_X3)) (Extract 31 0 (Var R_X2))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 136448)) (Word 0 32))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 136448)) (Word 0 32))) $;
	Move R_NG (Var R_TMPNG) $;
	Move R_ZR (Var R_TMPZR) $;
	Move R_CY (Var R_TMPCY) $;
	Move R_OV (Var R_TMPOV)
)

(* 0x4130005c: b.eq 0x41300050 *)
| 1093664860 => Some (4,
	If (Cast CAST_LOW 1 (Var R_ZR)) (
		Jmp (Word 1093664848 64)
	) (* else *) (
		Nop
	)
)

(* 0x41300060: sub x0, x1, x0 *)
| 1093664864 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X1) (Var R_X0))
)

(* 0x41300064: add sp, sp, #0x20 *)
| 1093664868 => Some (4,
	Move (V_TEMP 73344) (Word 32 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 73344))) (Var R_SP))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 73344))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_SP) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 73344)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 73600) (BinOp OP_PLUS (Var R_SP) (Var (V_TEMP 73344))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_SP (Var (V_TEMP 73600))
)

(* 0x41300068: ret  *)
| 1093664872 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x4130006c: mov x1, x0 *)
| 1093664876 => Some (4,
	Move R_X1 (Var R_X0)
)

(* 0x41300070: b 0x41300054 *)
| 1093664880 => Some (4,
	Jmp (Word 1093664852 64)
)

(* 0x41300074: add x1, x1, #0x1 *)
| 1093664884 => Some (4,
	Move (V_TEMP 73344) (Word 1 64) $;
	Move R_TMPCY (Cast CAST_UNSIGNED 8 (BinOp OP_LT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) (Var R_X1))) $;
	Move R_TMPOV (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var R_X1) (Word 63 64)) (Word 1 64)) (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 73344)) (Word 63 64)) (Word 1 64))) (Word 1 64)))) $;
	Move (V_TEMP 73600) (BinOp OP_PLUS (Var R_X1) (Var (V_TEMP 73344))) $;
	Move R_TMPNG (Cast CAST_UNSIGNED 8 (BinOp OP_SLT (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_TMPZR (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 73600)) (Word 0 64))) $;
	Move R_X1 (Var (V_TEMP 73600))
)

(* 0x41300078: ldrb w4, [x1] *)
| 1093664888 => Some (4,
	Move (V_TEMP 26240) (Var R_X1) $;
	Move (V_TEMP 167680) (Load (Var V_MEM64) (Var (V_TEMP 26240)) LittleE 1) $;
	Move R_X4 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 167680)))
)

(* 0x4130007c: cbz w4, 0x41300060 *)
| 1093664892 => Some (4,
	Move (V_TEMP 102144) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Extract 31 0 (Var R_X4)) (Word 0 32))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 102144))) (
		Jmp (Word 1093664864 64)
	) (* else *) (
		Nop
	)
)

(* 0x41300080: ubfx x2, x4, #0x6, #0x2 *)
| 1093664896 => Some (4,
	Move (V_TEMP 282112) (Var R_X4) $;
	Move (V_TEMP 282240) (BinOp OP_RSHIFT (Var (V_TEMP 282112)) (Word 6 64)) $;
	Move (V_TEMP 282368) (BinOp OP_MINUS (Word 64 64) (Word 6 64)) $;
	Move (V_TEMP 282496) (BinOp OP_LSHIFT (Var (V_TEMP 282112)) (Var (V_TEMP 282368))) $;
	Move (V_TEMP 282624) (BinOp OP_OR (Var (V_TEMP 282240)) (Var (V_TEMP 282496))) $;
	Move (V_TEMP 282880) (BinOp OP_AND (Var (V_TEMP 282624)) (Word 18158513697557839875 64)) $;
	Move R_X2 (BinOp OP_AND (Var (V_TEMP 282880)) (Word 3 64))
)

(* 0x41300084: ldr x2, [x3, x2, LSL #0x3] *)
| 1093664900 => Some (4,
	Move (V_TEMP 23040) (Var R_X2) $;
	Move (V_TEMP 28928) (Var (V_TEMP 23040)) $;
	Move (V_TEMP 28928) (BinOp OP_LSHIFT (Var (V_TEMP 28928)) (Word 3 64)) $;
	Move (V_TEMP 30080) (BinOp OP_PLUS (Var R_X3) (Var (V_TEMP 28928))) $;
	Move R_X2 (Load (Var V_MEM64) (Var (V_TEMP 30080)) LittleE 8)
)

(* 0x41300088: lsr x2, x2, x4 *)
| 1093664904 => Some (4,
	Move (V_TEMP 180224) (BinOp OP_AND (Var R_X4) (Word 63 64)) $;
	Move R_X2 (BinOp OP_RSHIFT (Var R_X2) (Var (V_TEMP 180224)))
)

(* 0x4130008c: tbnz w2, #0x0, 0x41300074 *)
| 1093664908 => Some (4,
	Move (V_TEMP 100608) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X2)) (Word 0 32)) $;
	Move (V_TEMP 100736) (BinOp OP_AND (Var (V_TEMP 100608)) (Word 1 32)) $;
	Move (V_TEMP 100992) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 100736)) (Word 0 32))) $;
	Move (V_TEMP 273408) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var (V_TEMP 100992)) (Word 0 8))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 273408))) (
		Jmp (Word 1093664884 64)
	) (* else *) (
		Nop
	)
)

(* 0x41300090: b 0x41300060 *)
| 1093664912 => Some (4,
	Jmp (Word 1093664864 64)
)

(* 0x41300094: mov x1, x0 *)
| 1093664916 => Some (4,
	Move R_X1 (Var R_X0)
)

(* 0x41300098: b 0x41300078 *)
| 1093664920 => Some (4,
	Jmp (Word 1093664888 64)
)

(* 0x4130009c: mov x0, #0x0 *)
| 1093664924 => Some (4,
	Move R_X0 (Word 0 64)
)

(* 0x413000a0: b 0x41300064 *)
| 1093664928 => Some (4,
	Jmp (Word 1093664868 64)
)

| _ => None
end.

Theorem welltyped: welltyped_prog arm8typctx musl_armv8_a_strspn_armv8.
Proof. Picinae_typecheck. Qed.

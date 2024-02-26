(* Automatically generated with pcode2coq *)

Require Import Picinae_ebpf_pcode.
Require Import NArith.
Open Scope N.

Definition arith_bpf : program := fun _ a => match a with

(* 0x00100000: MOV R1,0x0 *)
| 0 => Some (8,
	Move R_R1 (Word 0 64)
)

(* 0x00100008: MOV R3,0x0 *)
| 8 => Some (8,
	Move R_R3 (Word 0 64)
)

(* 0x00100010: MOV R4,R2 *)
| 16 => Some (8,
	Move R_R4 (Var R_R2)
)

(* 0x00100018: ADD R4,R1 *)
| 24 => Some (8,
	Move R_R4 (BinOp OP_PLUS (Var R_R4) (Var R_R1))
)

(* 0x00100020: LDXW R0,[R4 + 0x0] *)
| 32 => Some (8,
	Move (V_TEMP 15872) (BinOp OP_PLUS (Var R_R4) (Word 0 64)) $;
	Move R_R0 (Load (Var V_MEM64) (Cast CAST_LOW 64 (Var (V_TEMP 15872))) LittleE 8)
)

(* 0x00100028: ADD R0,R3 *)
| 40 => Some (8,
	Move R_R0 (BinOp OP_PLUS (Var R_R0) (Var R_R3))
)

(* 0x00100030: ADD R1,0x4 *)
| 48 => Some (8,
	Move R_R1 (BinOp OP_PLUS (Var R_R1) (Word 4 64))
)

(* 0x00100038: MOV R3,R0 *)
| 56 => Some (8,
	Move R_R3 (Var R_R0)
)

(* 0x00100040: JEQ R1,0x400,0x00100050 *)
| 64 => Some (8,
	Move (V_TEMP 32512) (Cast CAST_UNSIGNED 8 (BinOp OP_EQ (Var R_R1) (Word 1024 64))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 32512))) (
		Jmp (Word 80 64)
	) (* else *) (
		Nop
	)
)

(* 0x00100048: JA 0x00100010 *)
| 72 => Some (8,
	Jmp (Word 16 64)
)

(* 0x00100050: STXW [R2 + 0x0],R0 *)
| 80 => Some (8,
	Move (V_TEMP 17408) (BinOp OP_PLUS (Var R_R2) (Word 0 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 17408)) (Cast CAST_LOW 32 (Var R_R0)) LittleE 4)
)

(* 0x00100058: EXIT *)
| 88 => Some (8,
	Move (V_TEMP 38528) (Load (Var V_MEM64) (Cast CAST_LOW 64 (Var R_R10)) LittleE 8) $;
	Jmp (Var (V_TEMP 38528))
)

| _ => None
end.

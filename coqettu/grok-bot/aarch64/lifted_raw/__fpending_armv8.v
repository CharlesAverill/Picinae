(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __fpending
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __fpending_armv8 : program := fun _ a => match a with

(* 0x00153984: ldr x1,[x0, #0x20] *)
(*    1390980: ldr x1,[x0, #0x20] *)
| 0x153984 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00153988: cbz x1,0x0015399c *)
(*    1390984: cbz x1,0x0015399c *)
| 0x153988 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x15399c 64)
	) (* else *) (
		Nop
	)
)

(* 0x0015398c: ldr x1,[x0, #0x28] *)
(*    1390988: ldr x1,[x0, #0x28] *)
| 0x15398c => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x28 64)) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00153990: ldr x0,[x0, #0x38] *)
(*    1390992: ldr x0,[x0, #0x38] *)
| 0x153990 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x38 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x00153994: sub x0,x1,x0 *)
(*    1390996: sub x0,x1,x0 *)
| 0x153994 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X1) (Var R_X0))
)

(* 0x00153998: ret *)
(*    1391000: ret *)
| 0x153998 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x0015399c: mov x0,#0x0 *)
(*    1391004: mov x0,#0x0 *)
| 0x15399c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001539a0: b 0x00153998 *)
(*    1391008: b 0x00153998 *)
| 0x1539a0 => Some (4,
	Jmp (Word 0x153998 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __fpending_armv8.
Proof. Picinae_typecheck. Qed.

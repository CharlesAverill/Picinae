(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __freadahead
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __freadahead_armv8 : program := fun _ a => match a with

(* 0x001539bc: ldr x1,[x0, #0x10] *)
(*    1391036: ldr x1,[x0, #0x10] *)
| 0x1539bc => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x10 64)) $;
	Move R_X1 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x001539c0: cbz x1,0x001539d0 *)
(*    1391040: cbz x1,0x001539d0 *)
| 0x1539c0 => Some (4,
	Move (V_TEMP 0x18b00) (BinOp OP_EQ (Var R_X1) (Word 0x0 64)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0x18b00))) (
		Jmp (Word 0x1539d0 64)
	) (* else *) (
		Nop
	)
)

(* 0x001539c4: ldr x0,[x0, #0x8] *)
(*    1391044: ldr x0,[x0, #0x8] *)
| 0x1539c4 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move R_X0 (Load (Var V_MEM64) (Var (V_TEMP 0x6100)) LittleE 8)
)

(* 0x001539c8: sub x0,x1,x0 *)
(*    1391048: sub x0,x1,x0 *)
| 0x1539c8 => Some (4,
	Move R_X0 (BinOp OP_MINUS (Var R_X1) (Var R_X0))
)

(* 0x001539cc: ret *)
(*    1391052: ret *)
| 0x1539cc => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

(* 0x001539d0: mov x0,#0x0 *)
(*    1391056: mov x0,#0x0 *)
| 0x1539d0 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001539d4: b 0x001539cc *)
(*    1391060: b 0x001539cc *)
| 0x1539d4 => Some (4,
	Jmp (Word 0x1539cc 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __freadahead_armv8.
Proof. Picinae_typecheck. Qed.

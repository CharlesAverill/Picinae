(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: srand
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition srand_armv8 : program := fun _ a => match a with

(* 0x00147efc: adrp x1,0x1c2000 *)
(*    1343228: adrp x1,0x1c2000 *)
| 0x147efc => Some (4,
	Move R_X1 (Word 0x1c2000 64)
)

(* 0x00147f00: sub w0,w0,#0x1 *)
(*    1343232: sub w0,w0,#0x1 *)
| 0x147f00 => Some (4,
	Move (V_TEMP 0x3c580) (BinOp OP_MINUS (Extract 31 0 (Var R_X0)) (Word 0x1 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x3c580)))
)

(* 0x00147f04: str x0,[x1, #0x598] *)
(*    1343236: str x0,[x1, #0x598] *)
| 0x147f04 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X1) (Word 0x598 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var R_X0)) LittleE 8)
)

(* 0x00147f08: ret *)
(*    1343240: ret *)
| 0x147f08 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *               Static Memory Hypotheses                  *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx srand_armv8.
Proof. Picinae_typecheck. Qed.

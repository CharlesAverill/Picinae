(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: setprotoent
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition setprotoent_armv8 : program := fun _ a => match a with

(* 0x001443d8: adrp x0,0x1c2000 *)
(*    1328088: adrp x0,0x1c2000 *)
| 0x1443d8 => Some (4,
	Move R_X0 (Word 0x1c2000 64)
)

(* 0x001443dc: str wzr,[x0, #0xed4] *)
(*    1328092: str wzr,[x0, #0xed4] *)
| 0x1443dc => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0xed4 64)) $;
	Move (V_TEMP 0x300) (Word 0x0 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6000)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x300))) LittleE 4)
)

(* 0x001443e0: ret *)
(*    1328096: ret *)
| 0x1443e0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx setprotoent_armv8.
Proof. Picinae_typecheck. Qed.

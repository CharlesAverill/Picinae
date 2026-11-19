(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __fseterr
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __fseterr_armv8 : program := fun _ a => match a with

(* 0x00153a0c: ldr w1,[x0] *)
(*    1391116: ldr w1,[x0] *)
| 0x153a0c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00153a10: orr w1,w1,#0x20 *)
(*    1391120: orr w1,w1,#0x20 *)
| 0x153a10 => Some (4,
	Move (V_TEMP 0x2cd00) (BinOp OP_OR (Extract 31 0 (Var R_X1)) (Word 0x20 32)) $;
	Move R_X1 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2cd00)))
)

(* 0x00153a14: str w1,[x0] *)
(*    1391124: str w1,[x0] *)
| 0x153a14 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x00153a18: ret *)
(*    1391128: ret *)
| 0x153a18 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx __fseterr_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_attr_setschedpolicy
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_attr_setschedpolicy_armv8 : program := fun _ a => match a with

(* 0x001611a8: str w1,[x0, #0x20] *)
(*    1446312: str w1,[x0, #0x20] *)
| 0x1611a8 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x20 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6000)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x001611ac: mov w0,#0x0 *)
(*    1446316: mov w0,#0x0 *)
| 0x1611ac => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x001611b0: ret *)
(*    1446320: ret *)
| 0x1611b0 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_attr_setschedpolicy_armv8.
Proof. Picinae_typecheck. Qed.

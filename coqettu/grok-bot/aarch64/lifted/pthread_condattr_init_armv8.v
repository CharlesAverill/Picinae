(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_condattr_init
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_condattr_init_armv8 : program := fun _ a => match a with

(* 0x00162478: str wzr,[x0] *)
(*    1451128: str wzr,[x0] *)
| 0x162478 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x300) (Word 0x0 32) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Var (V_TEMP 0x300))) LittleE 4)
)

(* 0x0016247c: mov w0,#0x0 *)
(*    1451132: mov w0,#0x0 *)
| 0x16247c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00162480: ret *)
(*    1451136: ret *)
| 0x162480 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_condattr_init_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_rwlockattr_init
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_rwlockattr_init_armv8 : program := fun _ a => match a with

(* 0x00164260: str xzr,[x0] *)
(*    1458784: str xzr,[x0] *)
| 0x164260 => Some (4,
	Move (V_TEMP 0x6400) (Var R_X0) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6400)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x00164264: mov w0,#0x0 *)
(*    1458788: mov w0,#0x0 *)
| 0x164264 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00164268: ret *)
(*    1458792: ret *)
| 0x164268 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_rwlockattr_init_armv8.
Proof. Picinae_typecheck. Qed.

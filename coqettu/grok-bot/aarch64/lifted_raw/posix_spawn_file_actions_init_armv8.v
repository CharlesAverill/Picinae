(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: posix_spawn_file_actions_init
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition posix_spawn_file_actions_init_armv8 : program := fun _ a => match a with

(* 0x00149474: str xzr,[x0, #0x8] *)
(*    1348724: str xzr,[x0, #0x8] *)
| 0x149474 => Some (4,
	Move (V_TEMP 0x6100) (BinOp OP_PLUS (Var R_X0) (Word 0x8 64)) $;
	Move (V_TEMP 0x600) (Word 0x0 64) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6100)) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x600))) LittleE 8)
)

(* 0x00149478: mov w0,#0x0 *)
(*    1348728: mov w0,#0x0 *)
| 0x149478 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0014947c: ret *)
(*    1348732: ret *)
| 0x14947c => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx posix_spawn_file_actions_init_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: posix_spawnattr_setpgroup
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition posix_spawnattr_setpgroup_armv8 : program := fun _ a => match a with

(* 0x00149578: str w1,[x0, #0x4] *)
(*    1348984: str w1,[x0, #0x4] *)
| 0x149578 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x4 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6000)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X1))) LittleE 4)
)

(* 0x0014957c: mov w0,#0x0 *)
(*    1348988: mov w0,#0x0 *)
| 0x14957c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00149580: ret *)
(*    1348992: ret *)
| 0x149580 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx posix_spawnattr_setpgroup_armv8.
Proof. Picinae_typecheck. Qed.

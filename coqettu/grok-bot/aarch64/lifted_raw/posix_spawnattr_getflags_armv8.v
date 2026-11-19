(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: posix_spawnattr_getflags
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition posix_spawnattr_getflags_armv8 : program := fun _ a => match a with

(* 0x00149488: ldr w0,[x0] *)
(*    1348744: ldr w0,[x0] *)
| 0x149488 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x0014948c: strh w0,[x1] *)
(*    1348748: strh w0,[x1] *)
| 0x14948c => Some (4,
	Move (V_TEMP 0x6300) (Var R_X1) $;
	Move (V_TEMP 0x3a480) (Extract 31 0 (Var R_X0)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6300)) (Cast CAST_UNSIGNED 16 (Extract 15 0 (Var (V_TEMP 0x3a480)))) LittleE 2)
)

(* 0x00149490: mov w0,#0x0 *)
(*    1348752: mov w0,#0x0 *)
| 0x149490 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00149494: ret *)
(*    1348756: ret *)
| 0x149494 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx posix_spawnattr_getflags_armv8.
Proof. Picinae_typecheck. Qed.

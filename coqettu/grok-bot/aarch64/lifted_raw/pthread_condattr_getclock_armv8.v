(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_condattr_getclock
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_condattr_getclock_armv8 : program := fun _ a => match a with

(* 0x0016106c: ldr w0,[x0] *)
(*    1445996: ldr w0,[x0] *)
| 0x16106c => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00161070: and w0,w0,#0x7fffffff *)
(*    1446000: and w0,w0,#0x7fffffff *)
| 0x161070 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x7fffffff 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00161074: str w0,[x1] *)
(*    1446004: str w0,[x1] *)
| 0x161074 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X0))) LittleE 4)
)

(* 0x00161078: mov w0,#0x0 *)
(*    1446008: mov w0,#0x0 *)
| 0x161078 => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x0016107c: ret *)
(*    1446012: ret *)
| 0x16107c => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_condattr_getclock_armv8.
Proof. Picinae_typecheck. Qed.

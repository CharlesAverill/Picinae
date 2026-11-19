(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: pthread_condattr_getpshared
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pthread_condattr_getpshared_armv8 : program := fun _ a => match a with

(* 0x00161080: ldr w0,[x0] *)
(*    1446016: ldr w0,[x0] *)
| 0x161080 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X0) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6380)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00161084: lsr w0,w0,#0x1f *)
(*    1446020: lsr w0,w0,#0x1f *)
| 0x161084 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x00161088: str w0,[x1] *)
(*    1446024: str w0,[x1] *)
| 0x161088 => Some (4,
	Move (V_TEMP 0x6380) (Var R_X1) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var (V_TEMP 0x6380)) (Cast CAST_UNSIGNED 32 (Extract 31 0 (Var R_X0))) LittleE 4)
)

(* 0x0016108c: mov w0,#0x0 *)
(*    1446028: mov w0,#0x0 *)
| 0x16108c => Some (4,
	Move R_X0 (Word 0x0 64)
)

(* 0x00161090: ret *)
(*    1446032: ret *)
| 0x161090 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx pthread_condattr_getpshared_armv8.
Proof. Picinae_typecheck. Qed.

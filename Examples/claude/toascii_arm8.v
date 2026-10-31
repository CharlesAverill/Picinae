(* Automatically generated with pcode2coq
arch: armv8
file: libc.so.6
function: toascii
entry: 0x134460 (lifted with entry rebased to 0)
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition toascii_arm8 : program := fun _ a => match a with

(* 0x00134460: and w0,w0,#0x7f *)
(*          0: and w0,w0,#0x7f *)
| 0x0 => Some (4,
	Move (V_TEMP 0) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0x7f 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0)))
)

(* 0x00134464: ret *)
(*          4: ret *)
| 0x4 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx toascii_arm8.
Proof. Picinae_typecheck. Qed.


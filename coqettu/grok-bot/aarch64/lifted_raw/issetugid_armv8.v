(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: issetugid
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition issetugid_armv8 : program := fun _ a => match a with

(* 0x0013c620: adrp x0,0x1c2000 *)
(*    1295904: adrp x0,0x1c2000 *)
| 0x13c620 => Some (4,
	Move R_X0 (Word 0x1c2000 64)
)

(* 0x0013c624: ldrb w0,[x0, #0x282] *)
(*    1295908: ldrb w0,[x0, #0x282] *)
| 0x13c624 => Some (4,
	Move (V_TEMP 0x5e00) (BinOp OP_PLUS (Var R_X0) (Word 0x282 64)) $;
	Move (V_TEMP 0x25000) (Load (Var V_MEM64) (Var (V_TEMP 0x5e00)) LittleE 1) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25000)))
)

(* 0x0013c628: ret *)
(*    1295912: ret *)
| 0x13c628 => Some (4,
	Move R_PC (Var R_X30) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *               Static Memory Hypotheses                  *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm8typctx issetugid_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: getpagesize
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition getpagesize_armv8 : program := fun _ a => match a with

(* 0x00123bc4: adrp x0,0x1c2000 *)
(*    1194948: adrp x0,0x1c2000 *)
| 0x123bc4 => Some (4,
	Move R_X0 (Word 0x1c2000 64)
)

(* 0x00123bc8: ldr w0,[x0, #0x2b0] *)
(*    1194952: ldr w0,[x0, #0x2b0] *)
| 0x123bc8 => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x2b0 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00123bcc: ret *)
(*    1194956: ret *)
| 0x123bcc => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx getpagesize_armv8.
Proof. Picinae_typecheck. Qed.

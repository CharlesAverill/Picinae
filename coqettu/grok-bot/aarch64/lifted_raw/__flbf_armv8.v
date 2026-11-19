(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: __flbf
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition __flbf_armv8 : program := fun _ a => match a with

(* 0x0015396c: ldr w0,[x0, #0x90] *)
(*    1390956: ldr w0,[x0, #0x90] *)
| 0x15396c => Some (4,
	Move (V_TEMP 0x6000) (BinOp OP_PLUS (Var R_X0) (Word 0x90 64)) $;
	Move (V_TEMP 0x24700) (Load (Var V_MEM64) (Var (V_TEMP 0x6000)) LittleE 4) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x24700)))
)

(* 0x00153970: mvn w0,w0 *)
(*    1390960: mvn w0,w0 *)
| 0x153970 => Some (4,
	Move (V_TEMP 0x2b100) (UnOp OP_NOT (Extract 31 0 (Var R_X0))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x2b100)))
)

(* 0x00153974: lsr w0,w0,#0x1f *)
(*    1390964: lsr w0,w0,#0x1f *)
| 0x153974 => Some (4,
	Move (V_TEMP 0x28580) (BinOp OP_RSHIFT (Extract 31 0 (Var R_X0)) (Word 0x1f 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x28580)))
)

(* 0x00153978: ret *)
(*    1390968: ret *)
| 0x153978 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx __flbf_armv8.
Proof. Picinae_typecheck. Qed.

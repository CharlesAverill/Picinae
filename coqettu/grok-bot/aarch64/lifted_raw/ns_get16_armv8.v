(* Automatically generated with pcode2coq
arch: armv8
file: ld-musl-aarch64.so.1
SHA256: 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
function: ns_get16
*)

Require Import Picinae_armv8.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition ns_get16_armv8 : program := fun _ a => match a with

(* 0x00143f4c: ldrh w0,[x0] *)
(*    1326924: ldrh w0,[x0] *)
| 0x143f4c => Some (4,
	Move (V_TEMP 0x6300) (Var R_X0) $;
	Move (V_TEMP 0x25200) (Load (Var V_MEM64) (Var (V_TEMP 0x6300)) LittleE 2) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x25200)))
)

(* 0x00143f50: rev16 w0,w0 *)
(*    1326928: rev16 w0,w0 *)
| 0x143f50 => Some (4,
	Move (V_TEMP 0x30400) (Extract 31 0 (Var R_X0)) $;
	Move (V_TEMP 0x30480) (BinOp OP_AND (Var (V_TEMP 0x30400)) (Word 0xff00ff00 32)) $;
	Move (V_TEMP 0x30500) (BinOp OP_RSHIFT (Var (V_TEMP 0x30480)) (Word 0x8 32)) $;
	Move (V_TEMP 0x30580) (BinOp OP_AND (Var (V_TEMP 0x30400)) (Word 0xff00ff 32)) $;
	Move (V_TEMP 0x30600) (BinOp OP_LSHIFT (Var (V_TEMP 0x30580)) (Word 0x8 32)) $;
	Move (V_TEMP 0x30400) (BinOp OP_OR (Var (V_TEMP 0x30500)) (Var (V_TEMP 0x30600))) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x30400)))
)

(* 0x00143f54: and w0,w0,#0xffff *)
(*    1326932: and w0,w0,#0xffff *)
| 0x143f54 => Some (4,
	Move (V_TEMP 0x12180) (BinOp OP_AND (Extract 31 0 (Var R_X0)) (Word 0xffff 32)) $;
	Move R_X0 (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x12180)))
)

(* 0x00143f58: ret *)
(*    1326936: ret *)
| 0x143f58 => Some (4,
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

Theorem welltyped: welltyped_prog arm8typctx ns_get16_armv8.
Proof. Picinae_typecheck. Qed.

(* Automatically generated with pcode2coq
arch: i386
file: ld-musl-i386.so.1
SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
function: pc_thunk_ax
*)

Require Import Picinae_i386.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition pc_thunk_ax_i386 : program := fun _ a => match a with

(* 0x0004a83e: MOV EAX,dword ptr [ESP] *)
(*     305214: MOV EAX,dword ptr [ESP] *)
| 0x4a83e => Some (3,
	Move (V_TEMP 0xb900) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_EAX (Var (V_TEMP 0xb900))
)

(* 0x0004a841: RET *)
(*     305217: RET *)
| 0x4a841 => Some (1,
	Move R_EIP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
	Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 0x4 32)) $;
	Jmp (Var R_EIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x86typctx pc_thunk_ax_i386.
Proof. Picinae_typecheck. Qed.

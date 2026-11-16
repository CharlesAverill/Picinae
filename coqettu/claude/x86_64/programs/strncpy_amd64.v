(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: strncpy
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strncpy_amd64 : program := fun _ a => match a with

(* 0x00165b39: PUSH RBX *)
(*    1465145: PUSH RBX *)
| 0x165b39 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x00165b3a: MOV RBX,RDI *)
(*    1465146: MOV RBX,RDI *)
| 0x165b3a => Some (3,
	Move R_RBX (Var R_RDI)
)

(* 0x00165b3d: CALL 0x00124040 *)
(*    1465149: CALL 0x00124040 *)
| 0x165b3d => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x165b42 64)) LittleE 8) $;
	Jmp (Word 0x124040 64)
)

(* 0x00165b42: MOV RAX,RBX *)
(*    1465154: MOV RAX,RBX *)
| 0x165b42 => Some (3,
	Move R_RAX (Var R_RBX)
)

(* 0x00165b45: POP RBX *)
(*    1465157: POP RBX *)
| 0x165b45 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x00165b46: RET *)
(*    1465158: RET *)
| 0x165b46 => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx strncpy_amd64.
Proof. Picinae_typecheck. Qed.

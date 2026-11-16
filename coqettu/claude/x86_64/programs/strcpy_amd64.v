(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: strcpy
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition strcpy_amd64 : program := fun _ a => match a with

(* 0x001659c7: PUSH RBX *)
(*    1464775: PUSH RBX *)
| 0x1659c7 => Some (1,
	Move (V_TEMP 0x27c80) (Var R_RBX) $;
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Var (V_TEMP 0x27c80))) LittleE 8)
)

(* 0x001659c8: MOV RBX,RDI *)
(*    1464776: MOV RBX,RDI *)
| 0x1659c8 => Some (3,
	Move R_RBX (Var R_RDI)
)

(* 0x001659cb: CALL 0x001347e0 *)
(*    1464779: CALL 0x001347e0 *)
| 0x1659cb => Some (5,
	Move R_RSP (BinOp OP_MINUS (Var R_RSP) (Word 0x8 64)) $;
	Move V_MEM64 (Store (Var V_MEM64) (Var R_RSP) (Cast CAST_UNSIGNED 64 (Word 0x1659d0 64)) LittleE 8) $;
	Jmp (Word 0x1347e0 64)
)

(* 0x001659d0: MOV RAX,RBX *)
(*    1464784: MOV RAX,RBX *)
| 0x1659d0 => Some (3,
	Move R_RAX (Var R_RBX)
)

(* 0x001659d3: POP RBX *)
(*    1464787: POP RBX *)
| 0x1659d3 => Some (1,
	Move (V_TEMP 0x55200) (Word 0x0 64) $;
	Move (V_TEMP 0x55200) (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Move R_RBX (Var (V_TEMP 0x55200))
)

(* 0x001659d4: RET *)
(*    1464788: RET *)
| 0x1659d4 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx strcpy_amd64.
Proof. Picinae_typecheck. Qed.

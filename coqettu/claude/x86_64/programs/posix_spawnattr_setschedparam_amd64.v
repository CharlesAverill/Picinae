(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: posix_spawnattr_setschedparam
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition posix_spawnattr_setschedparam_amd64 : program := fun _ a => match a with

(* 0x0015cd91: MOV EAX,0x26 *)
(*    1428881: MOV EAX,0x26 *)
| 0x15cd91 => Some (5,
	Move R_RAX (Word 0x26 64)
)

(* 0x0015cd96: RET *)
(*    1428886: RET *)
| 0x15cd96 => Some (1,
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

Theorem welltyped: welltyped_prog x64typctx posix_spawnattr_setschedparam_amd64.
Proof. Picinae_typecheck. Qed.

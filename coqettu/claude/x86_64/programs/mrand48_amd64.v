(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: mrand48
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition mrand48_amd64 : program := fun _ a => match a with

(* 0x0015c262: LEA RDI,[0x1a4368] *)
(*    1426018: LEA RDI,[0x1a4368] *)
| 0x15c262 => Some (7,
	Move R_RDI (Word 0x1a4368 64)
)

(* 0x0015c269: JMP 0x0015c247 *)
(*    1426025: JMP 0x0015c247 *)
| 0x15c269 => Some (5,
	Jmp (Word 0x15c247 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx mrand48_amd64.
Proof. Picinae_typecheck. Qed.

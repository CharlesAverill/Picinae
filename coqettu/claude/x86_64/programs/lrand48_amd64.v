(* Automatically generated with pcode2coq
arch: amd64
file: ld-musl-x86_64.so.1
SHA256: cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
function: lrand48
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition lrand48_amd64 : program := fun _ a => match a with

(* 0x0015c23b: LEA RDI,[0x1a4368] *)
(*    1425979: LEA RDI,[0x1a4368] *)
| 0x15c23b => Some (7,
	Move R_RDI (Word 0x1a4368 64)
)

(* 0x0015c242: JMP 0x0015c222 *)
(*    1425986: JMP 0x0015c222 *)
| 0x15c242 => Some (5,
	Jmp (Word 0x15c222 64)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx lrand48_amd64.
Proof. Picinae_typecheck. Qed.

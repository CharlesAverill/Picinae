Require Import Utf8.
Require Import Picinae_amd64.

Require Import vspells_patched.

Theorem strcmp_welltyped: welltyped_prog x64typctx my_prog.
Proof. Picinae_typecheck. Qed.

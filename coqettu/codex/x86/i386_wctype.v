(* Concrete wide-character predicates shared by the musl i386 proofs. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith.
Open Scope N.

Definition wide_control (x:N) :=
  (x<=?31) || ((127<=?x)&&(x<=?159)) ||
  ((8232<=?x)&&(x<=?8233)) || ((65529<=?x)&&(x<=?65531)).

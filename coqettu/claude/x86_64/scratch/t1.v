Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith Lia.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.
Goal forall n (s1 s0:store),
 s1 R_RDX = n -> n < 2^64 -> callee_saved_eq s0 s1 -> models x64typctx s1 ->
 N.lnot ((if n <? 126 then 1 else 0) .| (if n =? 126 then 1 else 0)) 1 = 0 ->
 (n mod 2 ^ 32 =? 0) = true -> False.
intros. Time bc_norm. Show.
Abort.

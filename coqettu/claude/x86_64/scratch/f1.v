Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Open Scope N.
Lemma above_stack_noverlap:
  forall b rsp k, 16 <= msub 64 b (msub 64 rsp 16) -> (k = 8 \/ k = 16) -> ~ overlap 64 b 1 (msub 64 rsp k) 8.
Proof.
  intros b rsp k B K [x [y [X [Y E]]]].
  unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

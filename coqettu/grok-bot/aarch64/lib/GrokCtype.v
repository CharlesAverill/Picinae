(* Grok Bot (agent coqettu): lemmas for musl's branch-free ctype range tests
   ((unsigned)c - lo <= k, compiled to sub/cmp/cset ls) as psimpl leaves them. *)
From Stdlib Require Import Utf8 NArith ZArith Lia.
Require Import Picinae_armv8.
Import ARM8Notations.
Open Scope N.

(* x - lo (mod 2^32) is below len exactly when lo <= x mod 2^32 < lo + len. *)
Lemma msub32_range': ∀ c lo len, 0 < len -> lo + len <= 2^32 ->
  (msub 32 c lo < len <-> lo <= c mod 2^32 < lo + len).
Proof.
  intros c lo len L0 H. rewrite <- (msub_mod_l 32 32) by reflexivity.
  assert (X := N.mod_lt c (2^32) ltac:(discriminate)).
  set (x := c mod 2^32) in *. clearbody x. unfold msub.
  rewrite (N.mod_small lo) by lia.
  destruct (N.le_gt_cases lo x).
  - replace (x + (2^32 - lo)) with ((x - lo) + 1 * 2^32) by lia.
    rewrite N.Div0.mod_add, N.mod_small by lia. lia.
  - rewrite N.mod_small by lia. lia.
Qed.

(* cset ls after "sub w0,w0,#lo; cmp w0,#k": 1 iff lo <= c mod 2^32 <= lo + k. *)
Lemma ls_test: ∀ c lo k, 0 < k -> lo + k < 2^32 ->
  N.lor (if k <=? msub 32 c lo then 0 else 1) (if c mod 2^32 =? lo + k then 1 else 0) =
  (if (lo <=? c mod 2^32) && (c mod 2^32 <=? lo + k) then 1 else 0).
Proof.
  intros c lo k K B. pose proof (msub32_range' c lo k K ltac:(lia)) as [R1 R2].
  assert (X := N.mod_lt c (2^32) ltac:(discriminate)).
  destruct (N.leb_spec k (msub 32 c lo)) as [M|M].
  - assert (O: c mod 2^32 < lo \/ lo + k <= c mod 2^32).
    { destruct (N.lt_ge_cases (c mod 2^32) lo) as [L|L]; [left; exact L|right].
      destruct (N.lt_ge_cases (c mod 2^32) (lo+k)) as [L2|L2]; [|exact L2].
      exfalso. assert (msub 32 c lo < k) by (apply R2; lia). lia. }
    destruct (N.eqb_spec (c mod 2^32) (lo+k)), (N.leb_spec lo (c mod 2^32)), (N.leb_spec (c mod 2^32) (lo+k));
      cbn; first [ reflexivity | exfalso; lia ].
  - specialize (R1 M).
    destruct (N.eqb_spec (c mod 2^32) (lo+k)), (N.leb_spec lo (c mod 2^32)), (N.leb_spec (c mod 2^32) (lo+k));
      cbn; first [ reflexivity | exfalso; lia ].
Qed.

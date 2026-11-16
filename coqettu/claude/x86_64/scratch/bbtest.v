Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List Btauto.
Require Import CoqEtTu.lib.x64_common.
Open Scope N.

Definition temper (x:N) :=
  let x := N.lxor x (x >> 11) in
  let x := N.lxor x (N.land ((x << 7) mod 2^32) 0x9D2C5680) in
  let x := N.lxor x (N.land ((x << 15) mod 2^32) 0xEFC60000) in
  N.lxor x (x >> 18).

Ltac closed_cmp :=
  repeat match goal with |- context [?a <? ?b] =>
    let v := eval vm_compute in (a <? b) in change (a <? b) with v end;
  repeat match goal with |- context [N.testbit ?c ?k] =>
    lazymatch c with Npos _ =>
      let v := eval vm_compute in (N.testbit c k) in change (N.testbit c k) with v end end;
  cbn [andb orb xorb negb].

Ltac bb32 HB :=
  apply N.bits_inj; let i := fresh "i" in intro i;
  let IW := fresh "IW" in
  destruct (N.lt_ge_cases i 32) as [IW|IW];
  [ let rec go k :=
      lazymatch eval compute in (k <? 32) with
      | true => destruct (N.eq_dec i k) as [->|?];
                [ bits_rewrite; bits_norm_idx; closed_cmp;
                  repeat match goal with |- context [N.testbit ?B ?j] =>
                    lazymatch type of HB with context [N.testbit B _] =>
                      rewrite (HB j) by (vm_compute; reflexivity) end end;
                  btauto
                | let k1 := eval compute in (N.succ k) in go k1 ]
      | false => exfalso; lia
      end in go 0
  | bits_rewrite; bits_cases ].

Lemma rax_temper: forall A B (HB: forall i, i < 12 -> N.testbit B i = N.testbit A i),
 ((A mod 2 ^ 32 >> 11
  .^ A
  .^ (A mod 2 ^ 32 >> 11 .^ A) << 7 .& 2636928640
  .^ (A >> 11 .^ A .^ (A >> 11 .^ B) << 7 .& 22144) << 15 .& 4022730752
  .^ (A mod 2 ^ 32 >> 11 .^ A
      .^ (A mod 2 ^ 32 >> 11 .^ A) << 7 .& 2636928640
      .^ (A >> 11 .^ A .^ (A >> 11 .^ B) << 7 .& 22144) << 15 .& 4022730752)
     mod 2 ^ 32 >> 18)
 mod 2 ^ 32 >> 1) = temper (A mod 2^32) >> 1.
Proof.
  intros. unfold temper; cbv zeta. Time bb32 HB.
Qed.

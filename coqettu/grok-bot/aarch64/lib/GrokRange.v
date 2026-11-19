(* GrokRange -- small lemmas/tactics turning ARMv8 compare-flag terms
   (cmp/ccmp/cset on 32-bit operands) into plain range tests.
   Part of Grok Bot (agent coqettu) proof library; machine-checked by Rocq. *)
From Stdlib Require Import NArith ZArith Lia.
Require Import Picinae_armv8.
Open Scope N.

Lemma msub32_cases: forall a k, k <= 2^32 ->
  msub 32 a k = if k <=? a mod 2^32 then a mod 2^32 - k else a mod 2^32 + 2^32 - k.
Proof.
  intros a k Hk. unfold msub.
  assert (Hx: a mod 2^32 < 2^32) by (apply N.mod_lt; discriminate).
  rewrite <- N.add_mod_idemp_l by discriminate.
  destruct (N.eq_dec k (2^32)) as [E|E].
  - subst k. rewrite N.mod_same by discriminate. rewrite N.sub_0_r.
    destruct (N.leb_spec (2^32) (a mod 2^32)); [lia|].
    replace (a mod 2^32 + 2^32 - 2^32) with (a mod 2^32) by lia.
    rewrite <- (N.mul_1_l (2^32)) at 2. rewrite N.mod_add by discriminate.
    apply N.mod_small; assumption.
  - rewrite (N.mod_small k) by lia.
    destruct (N.leb_spec k (a mod 2^32)).
    + replace (a mod 2^32 + (2^32 - k)) with ((a mod 2^32 - k) + 1 * 2^32) by lia.
      rewrite N.mod_add by discriminate. apply N.mod_small. lia.
    + rewrite N.mod_small by lia. lia.
Qed.

Lemma mod32_lt: forall a, a mod 2^32 < 2^32.
Proof. intros. apply N.mod_lt. discriminate. Qed.

(* Close goals built from 32-bit compare flags: move the flag hypotheses
   into the goal, rewrite every msub 32 v k into a case on x := v mod 2^32,
   generalize x (with x < 2^32), case-split every comparison, and finish
   with reflexivity/discriminate/lia. *)
Ltac grok_range_close :=
  repeat match goal with H: context[if _ then _ else _] |- _ =>
    match type of H with _ V_MEM64 = _ => fail 1 | _ => revert H end end;
  repeat match goal with |- context[msub 32 ?v ?k] => rewrite (msub32_cases v k) by lia end;
  match goal with |- context[?v mod 2^32] =>
    let Hx := fresh "Hx" in let x := fresh "x" in
    pose proof (mod32_lt v) as Hx; revert Hx; generalize (v mod 2^32); intros x Hx end;
  repeat match goal with
         | |- context[?p <=? ?q] => destruct (N.leb_spec p q); try (exfalso; lia)
         | |- context[?p <? ?q] => destruct (N.ltb_spec p q); try (exfalso; lia)
         | |- context[?p =? ?q] => destruct (N.eqb_spec p q); try (exfalso; lia)
         end;
  cbn [orb N.lor N.lxor N.land Pos.lor Pos.lxor]; intros;
  first [ reflexivity
        | match goal with H: _ = _ |- _ => discriminate H end
        | lia ].

(* Two-level bitmap lookups (iswpunct/iswalpha): the binary forms the byte
   index as y + (B << 5) and shifts the byte arithmetically by (wc AND 7). *)
Lemma tab_addr: forall T B y, T + y + N.shiftl B 5 = T + B * 32 + y.
Proof. intros. rewrite N.shiftl_mul_pow2. change (2^5) with 32. lia. Qed.

Lemma byte_ashiftr: forall m T k, k < 8 ->
  ashiftr 32 (N.shiftr (getmem 64 LittleE 1 m T) 0 mod 2^32) (N.land (N.shiftr k 0 mod 2^32) 31)
  = N.shiftr (getmem 64 LittleE 1 m T) k.
Proof.
  intros m T k Hk. pose proof (getmem_bound 64 LittleE 1 m T) as B. change (2^(1*8)) with 256 in B.
  rewrite !N.shiftr_0_r. rewrite (N.mod_small (getmem _ _ _ _ _)) by lia.
  rewrite (N.mod_small k) by lia.
  change 31 with (N.ones 5). rewrite N.land_ones. rewrite (N.mod_small k) by (change (2^5) with 32; lia).
  rewrite ashiftr_nonneg by (rewrite N.mod_small by lia; change (2^N.pred 32) with 2147483648; lia).
  rewrite N.mod_small by lia. reflexivity.
Qed.

Ltac grok_tab_close :=
  repeat match goal with |- context[ashiftr 32 (N.shiftr (getmem 64 LittleE 1 ?m ?A) 0 mod 2^32) (N.land (N.shiftr ?k 0 mod 2^32) 31)] =>
    rewrite (byte_ashiftr m A k) by (apply N.mod_lt; discriminate) end;
  rewrite ?tab_addr;
  grok_range_close.

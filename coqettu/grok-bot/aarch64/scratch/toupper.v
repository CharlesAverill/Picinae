From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import toupper_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* C-locale toupper on the low 32 bits of the int argument. *)
Definition toupper_spec (c:N) : N :=
  let c32 := c mod 2^32 in if (97 <=? c32) && (c32 <=? 122) then c32 - 32 else c32.


(* x - lo (mod 2^32) is below len exactly when lo <= x mod 2^32 < lo + len. *)
Lemma msub32_range: ∀ c lo len, 0 < len -> lo + len <= 2^32 ->
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

Lemma and95_range: ∀ x, 97 <= x <= 122 -> x .& 95 = x - 32.
Proof.
  intros x H. assert (E: ∃ n:nat, x = 97 + N.of_nat n /\ (n < 26)%nat) by (exists (N.to_nat (x-97)); lia).
  destruct E as (n & -> & Hn). do 26 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma land_mod32: ∀ x y, (x .& y) mod 2^32 = (x mod 2^32) .& y.
Proof.
  intros x y. apply N.bits_inj. intro b. rewrite N.land_spec.
  destruct (N.lt_ge_cases b 32).
  - rewrite !N.mod_pow2_bits_low by assumption. apply N.land_spec.
  - rewrite !N.mod_pow2_bits_high by assumption. reflexivity.
Qed.

Lemma lor_mod32: ∀ x y, y < 2^32 -> (x .| y) mod 2^32 = (x mod 2^32) .| y.
Proof.
  intros x y Y. apply N.bits_inj. intro b. rewrite N.lor_spec.
  destruct (N.lt_ge_cases b 32).
  - rewrite !N.mod_pow2_bits_low by assumption. apply N.lor_spec.
  - rewrite !N.mod_pow2_bits_high by assumption. rewrite (bound_hibits_zero 32 y b Y H). reflexivity.
Qed.

Section Invariants.
  Variables (sp mem raddr c : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11f2e8 => Inv 0 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11f2fc => Post 0 (s R_X0 = toupper_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition exits := make_exits 0 toupper_armv8 invs.
  Definition invs0 := make_invs 0 toupper_armv8 invs.
End Invariants.

Theorem welltyped': welltyped_prog arm8typctx toupper_armv8.
Proof. Picinae_typecheck. Qed.

Theorem toupper_correct:
  ∀ prog s sp mem raddr c t xs'
    (PROG: toupper_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11f2e8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c),
  satisfies_all prog (invs0 sp mem raddr c) (exits sp mem raddr c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=toupper_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply welltyped'. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  repeat arm8_step; (split; [|repeat split; assumption]); unfold toupper_spec;
  destruct (25 <=? msub 32 c 97) eqn:B1; destruct (c mod 2^32 =? 122) eqn:B2; cbn in BC;
  try discriminate.
  1: { (* outside a..z *)
    apply N.leb_le in B1. apply N.eqb_neq in B2.
    destruct (97 <=? c mod 2^32) eqn:L1, (c mod 2^32 <=? 122) eqn:L2; try reflexivity.
    apply N.leb_le in L1, L2. exfalso.
    assert (msub 32 c 97 < 25) by (apply msub32_range; cbn; lia). lia. }
  all: assert (AND: c .& 95 = (c mod 2^32) .& 95) by
      (rewrite <- (N.mod_small (c .& 95) (2^32)) by
         (eapply N.le_lt_trans; [apply N.land_le_r|reflexivity]); apply land_mod32).
  all: rewrite AND; clear AND.
  all: first
    [ (* c = 'z' *)
      apply N.eqb_eq in B2; rewrite B2; reflexivity
    | (* a..y *)
      apply N.leb_gt in B1; rewrite (msub32_range c 97 25) in B1 by (cbn; lia);
      rewrite (proj2 (N.leb_le 97 _)), (proj2 (N.leb_le _ 122)) by lia; cbn [andb];
      apply and95_range; lia ].
Qed.

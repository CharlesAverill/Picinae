From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import htons_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl GrokBytes.
Import ARM8Notations.
Open Scope N.
Theorem htons_welltyped: welltyped_prog arm8typctx htons_armv8.
Proof. Picinae_typecheck. Qed.
Section Invariants.
  Variables (sp mem raddr x : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x141df0 => Inv 0 (s R_X0 = x /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x141df4 => Post 0 (s R_X0 mod 2^16 = revbytes (x mod 2^16) 2 /\ s R_X0 < 2^32 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition htons_exits := make_exits 0 htons_armv8 invs.
  Definition htons_invs := make_invs 0 htons_armv8 invs.
End Invariants.
Theorem htons_partial_correctness:
  ∀ prog s sp mem raddr x t xs'
    (PROG: htons_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x141df0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = x),
  satisfies_all prog (htons_invs sp mem raddr x) (htons_exits sp mem raddr x) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=htons_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold htons_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply htons_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  pose proof (MDL1 R_X0 64 eq_refl) as YB. rewrite X0 in YB.
  repeat arm8_step.
  splits; try reflexivity; try assumption.
  - apply N.bits_inj; intro i. destruct (N.lt_ge_cases i (2*8)) as [LT|GE].
    + transitivity (N.testbit (revbytes x 2) i).
      * rev_low x 2.
      * rewrite !revbytes_spec, (proj2 (N.ltb_lt _ _) LT).
        rewrite N.mod_pow2_bits_low. reflexivity. unfold rbf.
        assert (i/8 < 2) by (apply N.Div0.div_lt_upper_bound; lia).
        pose proof (N.mod_lt i 8 ltac:(discriminate)). lia.
    + rewrite revbytes_high by (try apply N.mod_lt; try discriminate; assumption).
      match goal with |- N.testbit ?t i = _ =>
        let e := reify_bx x t in change t with (bden x e);
        apply bbnd_ok; [cbn in YB; lia | let v := eval vm_compute in (bbnd e) in change (bbnd e) with v; cbn in GE; lia]
      end.
  - match goal with |- ?t < _ =>
      enough (E: t mod 2^32 = t) by (rewrite <- E; apply N.mod_lt; discriminate) end.
    apply N.bits_inj; intro i. destruct (N.lt_ge_cases i 32) as [LT|GE].
    + apply N.mod_pow2_bits_low. exact LT.
    + rewrite N.mod_pow2_bits_high by exact GE.
      match goal with |- false = N.testbit ?t i =>
        let e := reify_bx x t in change t with (bden x e); symmetry;
        apply bbnd_ok; [cbn in YB; lia | let v := eval vm_compute in (bbnd e) in change (bbnd e) with v; lia]
      end.
Qed.

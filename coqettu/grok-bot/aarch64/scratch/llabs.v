From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import llabs_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

Definition llabs_spec (c:N) : N := ofZ 64 (Z.abs (toZ 64 c)).

Section Invariants.
  Variables (sp mem raddr c : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15d3a4 => Inv 0 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15d3ac => Post 0 (s R_X0 = llabs_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition exits := make_exits 0 llabs_armv8 invs.
  Definition invs0 := make_invs 0 llabs_armv8 invs.
End Invariants.

Theorem welltyped': welltyped_prog arm8typctx llabs_armv8.
Proof. Picinae_typecheck. Qed.

Theorem llabs_correct:
  ∀ prog s sp mem raddr c t xs'
    (PROG: llabs_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15d3a4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c),
  satisfies_all prog (invs0 sp mem raddr c) (exits sp mem raddr c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=llabs_armv8). exact PROG.
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
  assert (C64 := MDL1 R_X0 64 eq_refl). rewrite X0 in C64. simpl in C64.
  repeat arm8_step; (split; [|repeat split; assumption]); unfold llabs_spec;
  rewrite msub_0_r, N.mod_small in BC by exact C64;
  destruct (slt 64 c 0) eqn:S; cbn in BC; try discriminate; unfold slt in S; change (toZ 64 0) with 0%Z in S.
  - apply Z.ltb_lt in S. rewrite Z.abs_neq by lia.
    rewrite msub_sbop. f_equal.
  - apply Z.ltb_ge in S. rewrite Z.abs_eq by lia. rewrite ofZ_toZ. symmetry. apply N.mod_small, C64.
Qed.

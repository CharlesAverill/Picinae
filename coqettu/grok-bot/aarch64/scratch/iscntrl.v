From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import iscntrl_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCtype.
Import ARM8Notations.
Open Scope N.

Theorem iscntrl_welltyped: welltyped_prog arm8typctx iscntrl_armv8.
Proof. Picinae_typecheck. Qed.

Definition iscntrl_spec (c:N) : N := let x := c mod 2^32 in if (x <? 32) || (x =? 127) then 1 else 0.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11ee50 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11ee5c => Post 0 (s R_X0 = iscntrl_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition iscntrl_exits := make_exits 0 iscntrl_armv8 invs.
  Definition iscntrl_invs := make_invs 0 iscntrl_armv8 invs.
End Invariants.

Theorem iscntrl_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: iscntrl_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ee50, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (iscntrl_invs sp mem raddr c d) (iscntrl_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=iscntrl_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold iscntrl_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply iscntrl_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat grok_step.
  all: splits; try reflexivity; try assumption.
  all: unfold iscntrl_spec; cbv zeta.
  all: pose proof (ls_test c 0 31 eq_refl eq_refl) as LT; rewrite ?msub_0_r in LT; change (0 + 31) with 31 in LT; rewrite ?LT.
  all: first [apply N.eqb_eq in BC | apply N.eqb_neq in BC].
  all: repeat match goal with
         | |- context [?a <=? ?b] => destruct (N.leb_spec a b)
         | |- context [?a <? ?b] => destruct (N.ltb_spec a b)
         | |- context [?a =? ?b] => destruct (N.eqb_spec a b) end.
  all: simpl; try reflexivity; lia.
Qed.

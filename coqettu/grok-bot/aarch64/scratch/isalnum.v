From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import isalnum_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCtype GrokCtype2.
Import ARM8Notations.
Open Scope N.

Theorem isalnum_welltyped: welltyped_prog arm8typctx isalnum_armv8.
Proof. Picinae_typecheck. Qed.

Definition isalnum_spec (c:N) : N := let x := c mod 2^32 in if ((48 <=? x) && (x <=? 57)) || ((65 <=? x) && (x <=? 90)) || ((97 <=? x) && (x <=? 122)) then 1 else 0.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11edec => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11ee08 => Post 0 (s R_X0 = isalnum_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition isalnum_exits := make_exits 0 isalnum_armv8 invs.
  Definition isalnum_invs := make_invs 0 isalnum_armv8 invs.
End Invariants.

Theorem isalnum_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: isalnum_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11edec, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (isalnum_invs sp mem raddr c d) (isalnum_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=isalnum_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold isalnum_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply isalnum_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: pose proof (ls_test (N.lor c 32) 97 25 eq_refl eq_refl) as LT0; change (97 + 25) with 122 in LT0.
  all: rewrite ?LT0 in *.
  all: pose proof (ls_test c 48 9 eq_refl eq_refl) as LT1; change (48 + 9) with 57 in LT1.
  all: rewrite ?LT1 in *.
  all: rewrite ?alpha_or32 in *.
  all: unfold isalnum_spec; cbv zeta.
  all: repeat match goal with
         | H: context [?a <=? ?b] |- _ => destruct (a <=? b)
         | |- context [?a <=? ?b] => destruct (a <=? b) end.
  all: simpl in *; first [reflexivity | discriminate | congruence].
Qed.

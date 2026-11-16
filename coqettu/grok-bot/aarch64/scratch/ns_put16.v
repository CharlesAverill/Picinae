From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import ns_put16_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl GrokBytes.
Import ARM8Notations.
Open Scope N.

Theorem ns_put16_welltyped: welltyped_prog arm8typctx ns_put16_armv8.
Proof. Picinae_typecheck. Qed.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x143f68 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x143f70 => Post 0 (s V_MEM64 = setmem 64 BigE 2 mem d c /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ns_put16_exits := make_exits 0 ns_put16_armv8 invs.
  Definition ns_put16_invs := make_invs 0 ns_put16_armv8 invs.
End Invariants.

Theorem ns_put16_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: ns_put16_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x143f68, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (ns_put16_invs sp mem raddr c d) (ns_put16_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ns_put16_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ns_put16_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ns_put16_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: rewrite setmem_big_little by lia.
  all: match goal with |- setmem _ _ _ _ _ ?X = setmem _ _ _ _ _ ?Y =>
         rewrite <- (setmem_mod_r _ _ _ _ _ X), <- (setmem_mod_r _ _ _ _ _ Y) end.
  f_equal. apply N.bits_inj; intro i. destruct (N.lt_ge_cases i (2*8)) as [LT|GE].
  - rewrite !N.mod_pow2_bits_low by assumption. rev_low c 2.
  - rewrite !N.mod_pow2_bits_high by assumption. reflexivity.
Qed.

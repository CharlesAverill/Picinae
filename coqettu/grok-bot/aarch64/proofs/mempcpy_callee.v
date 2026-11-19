(* mempcpy: memcpy (n <= 128) re-checked inside mp_prog with the caller frame memory.
   Written by Grok Bot (agent coqettu); machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require mempcpy_armv8 memcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCopy.
From Grok.proofs Require Import memcpy_defs memcpy_mem memcpy_proof.
From Grok.proofs Require Import mempcpy_defs.
Import ARM8Notations.
Open Scope N.

Ltac bools_to_props_mc := repeat match goal with
 | H: (?a =? ?b) = true |- _ => apply N.eqb_eq in H
 | H: (?a =? ?b) = false |- _ => apply N.eqb_neq in H
 | H: (?a <=? ?b) = true |- _ => apply N.leb_le in H
 | H: (?a <=? ?b) = false |- _ => apply N.leb_gt in H
 | H: (?a <? ?b) = true |- _ => apply N.ltb_lt in H
 | H: (?a <? ?b) = false |- _ => apply N.ltb_ge in H
 | H: context[if ?c then _ else _] |- _ =>
     match type of H with _ V_MEM64 = _ => fail 1 | _ => destruct c eqn:? end
 end.
Theorem memcpy_correct_in_mempcpy:
  ∀ prog s sp mem raddr d src n x29 t xs'
    (P1: mempcpy_armv8.mempcpy_armv8 ⊆2 prog) (P0: memcpy_armv8.memcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118270, s))
    (MDL: models arm8typctx s)
    (HPRE: memcpy_pre (mp_fm sp mem raddr n x29) d src n (sp ⊖ 32) 0x15e82c s),
  satisfies_all prog (mp_invs0 sp mem raddr d src n x29) (mp_exits0 sp mem raddr d src n x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=mp_prog).
    unfold mp_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold mp_invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL HPRE START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. exact HPRE.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply mp_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold memcpy_pre in *; repeat match goal with H: _ /\ _ |- _ => destruct H end.
  all: try match goal with H: False |- _ => destruct H end.
  all: repeat grok_step.
  all: try match goal with H: models _ _ |- _ => clear H end.
  all: try (remember (mp_fm sp mem raddr n x29) as fm; clear Heqfm).
  all: bools_to_props_mc; rewrite ?N.shiftr_div_pow2 in *.
  all: try (exfalso; lia).
  all: try (match goal with H: ?st V_MEM64 = _ |- context [?st V_MEM64] => rewrite H end).
  all: unfold memcpy_post; splits; try reflexivity; try assumption.
  all: try (exfalso; match goal with H: N.lor _ _ = _ |- _ => vm_compute in H; discriminate H end).
  all: apply_cp; pow_lits; lia.
Qed.


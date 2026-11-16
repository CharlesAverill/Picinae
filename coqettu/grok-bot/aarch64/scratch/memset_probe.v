From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lifted Require Import memset_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

Theorem memset_welltyped: welltyped_prog arm8typctx memset_armv8.
Proof. Picinae_typecheck. Qed.

Section Invariants.
  Variables (c : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x118400 => Inv 0 (s R_X1 = c)
    | 0x118404 => Post 0 (s R_Z0 mod 2^128 = c)
    | _ => NoInv
    end.
  Definition mexits := make_exits 0 memset_armv8 invs.
  Definition minvs := make_invs 0 memset_armv8 invs.
End Invariants.

Theorem probe: ∀ s c t xs' (ENTRY: startof t xs' = (Addr 0x118400, s)) (MDL: models arm8typctx s) (X1: s R_X1 = c),
  satisfies_all memset_armv8 (minvs c) (mexits c) (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memset_welltyped. intro MDL1.
  clear - PRE MDL1. destruct_inv 64 PRE.
  arm8_step. dump_ctx.
Admitted.

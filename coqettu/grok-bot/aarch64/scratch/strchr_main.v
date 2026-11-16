From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strchr_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep.
From Grok.proofs Require Import strchr_callees.
Import ARM8Notations.
Open Scope N.

Lemma msub_msub64: ∀ x a b c, a < 2^64 -> b < 2^64 -> c = a + b -> c < 2^64 ->
  msub 64 (msub 64 x a) b = msub 64 x c.
Proof.
  intros x a b c A B C CL. subst c. unfold msub.
  rewrite (N.mod_small a), (N.mod_small b), (N.mod_small (a+b)) by assumption.
  rewrite N.Div0.add_mod_idemp_l.
  replace (x + (2^64 - a) + (2^64 - b)) with (x + (2^64 - (a+b)) + 1 * 2^64) by lia.
  apply N.Div0.mod_add.
Qed.

Theorem strchr_partial_correctness:
  ∀ prog s sp mem raddr p c x29 t xs'
    (P2: strchr_armv8.strchr_armv8 ⊆2 prog) (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15ebcc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs2 sp mem raddr p c x29) (exits2 sp mem raddr p c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strchr_prog).
    apply strchr_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64. simpl in P64.
  pose proof (MDL1 R_X1 64 eq_refl) as C64. rewrite X1 in C64. simpl in C64.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  do 4 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strchr_prog_welltyped. intro MDL2.
  eapply (perform_call 1). reflexivity.
  intros. eapply strchrnul_correct_in_strchr with (c:=c) (x29:=sp ⊖ 32);
    first [ exact strchr_prog_contains2 | exact strchr_prog_contains1 | exact strchr_prog_contains0 | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strchr_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 P64 C64 R64 X2964.
  rename MDL' into MDL. rename s' into s.
  destruct_inv 64 PRE.
  all: destruct PRE as (SP & X30 & X29 & [(MEM & CNZ & SPEC) | (MEM & CZ & SPEC)]); [
    repeat arm8_step;
    [> splits; try (apply N.mod_small; assumption) .. ];
    [> eexists _, (s R_X0); splits; [ reflexivity | left; unfold chr_frame; reflexivity | exact SPEC | ] .. ];
    [> unfold c8; rewrite BC; reflexivity .. ]
  | unfold frame_mem, nul_frame in MEM; repeat arm8_step;
    [> splits; try (apply N.mod_small; assumption) .. ];
    [> eexists _, (s R_X0); splits; [ reflexivity | right; unfold chr_frame; reflexivity | | ] .. ];
    [> unfold frame_mem, nul_frame, c8 in *; rewrite ?CZ in *;
       rewrite (msub_msub64 sp 32 32 64), (msub_msub64 sp 32 24 56), (msub_msub64 sp 32 8 40) in SPEC by lia .. ];
    [> first [ exact SPEC | rewrite BC; reflexivity ] .. ] ].
Qed.

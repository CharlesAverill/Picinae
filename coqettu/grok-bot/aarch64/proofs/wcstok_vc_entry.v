(* wcstok: entry VC (prologue, s == NULL resumes from *p, empty saved state, call wcsspn).
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs wcstok_lib wcstok_vc_posts.
Import ARM8Notations.
Open Scope N.

Ltac wt_call WS MDL2 :=
  lazymatch goal with
  | |- models _ _ => exact MDL2
  | |- _ R_X0 = _ => rewrite WS; reflexivity
  | |- _ R_X19 = _ => rewrite WS; reflexivity
  | |- _ V_MEM64 = _ => reflexivity
  | |- _ R_SP = _ => reflexivity
  | |- _ R_X29 = _ => reflexivity
  | |- _ R_X30 = _ => reflexivity
  | |- _ R_X1 = _ => reflexivity
  | |- _ R_X20 = _ => reflexivity
  | |- _ R_X21 = _ => reflexivity
  | |- _ => sassumption
  end.

Lemma wt_case_entry:
  ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc st t
    (PRE0: wt_pre sp mem s0 sep p Ls Lc)
    (B30: raddr < 2^64) (B19: x19 < 2^64) (B20: x20 < 2^64) (B21: x21 < 2^64) (B22: x22 < 2^64) (B29: x29 < 2^64)
    (MDL: models arm8typctx st)
    (PRE: st R_X0 = s0 /\ st R_X1 = sep /\ st R_X2 = p /\ st V_MEM64 = mem /\ st R_SP = sp /\
          st R_X30 = raddr /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\
          st R_X22 = x22 /\ st R_X29 = x29),
  nextinv wt_prog (wt_invs2 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)
    (wt_exits2 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0) false ((Addr 0x16013c, st) :: t).
Proof.
  intros.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X20 & X21 & X22 & X29).
  destruct PRE0 as (SPL & W_SP & PB & SPRE).
  assert (FM: mem [Ⓠ sp ⊖ 48 := x29] [Ⓠ sp ⊖ 40 := raddr] [Ⓠ sp ⊖ 32 := x19] [Ⓠ sp ⊖ 24 := x20]
                  [Ⓠ sp ⊖ 16 := x21] [Ⓠ sp ⊖ 8 := x22] = wt_M1 sp mem raddr x19 x20 x21 x22 x29)
    by (unfold wt_M1, wt_frame; rewrite !msub_small by lia; reflexivity).
  assert (S48: sp ⊖ 48 = sp - 48) by (apply msub_small; lia).
  assert (FR := wt_rd sp mem raddr x19 x20 x21 x22 x29 0 0 0 _ SPL W_SP B30 B19 B20 B21 B22 B29 (or_introl eq_refl)).
  assert (MQ: wt_M1 sp mem raddr x19 x20 x21 x22 x29 Ⓠ[p] = mem Ⓠ[p]) by (apply wt_M1_q; lia).
  unfold wt_invs2, wt_exits2.
  do 7 arm8_step.
  all: rewrite ?FM, ?S48.
  - (* s == NULL: continue from *p *)
    assert (WS: wt_s mem s0 p = mem Ⓠ[p]) by (unfold wt_s, wt_str; rewrite BC; reflexivity).
    do 2 arm8_step.
    all: rewrite ?MQ in *.
    + (* *p != NULL *)
      apply Bool.negb_true_iff, N.eqb_neq in BC0.
      assert (SNZ: 0 < wt_s mem s0 p) by (rewrite WS; lia).
      assert (SP' := SPRE ltac:(change (wt_str mem s0 p) with (wt_s mem s0 p); lia)). cbv zeta in SP'. change (wt_str mem s0 p) with (wt_s mem s0 p) in SP'.
      destruct SP' as (NFs & Zs & LsB & NFc & Zc & CP & SB & CB).
      do 3 arm8_step.
      eapply models_after_steps. eassumption. apply wt_prog_welltyped. intro MDL2.
      eapply (wt_call_spn sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc).
      all: wt_call WS MDL2.
    + (* *p == NULL: return NULL, nothing stored *)
      apply Bool.negb_false_iff, N.eqb_eq in BC0.
      repeat arm8_step.
      destruct FR as (F1 & F2 & F3 & F4 & F5 & F6).
      splits; try sassumption; try lia.
      all: left; splits; [rewrite WS; exact BC0 | reflexivity | reflexivity].
  - (* s != NULL *)
    assert (WS: wt_s mem s0 p = s0) by (unfold wt_s, wt_str; rewrite BC; reflexivity).
    apply N.eqb_neq in BC.
    assert (SNZ: 0 < wt_s mem s0 p) by (rewrite WS; lia).
    assert (SP' := SPRE ltac:(change (wt_str mem s0 p) with (wt_s mem s0 p); lia)). cbv zeta in SP'. change (wt_str mem s0 p) with (wt_s mem s0 p) in SP'.
    destruct SP' as (NFs & Zs & LsB & NFc & Zc & CP & SB & CB).
    do 3 arm8_step.
    eapply models_after_steps. eassumption. apply wt_prog_welltyped. intro MDL2.
    eapply (wt_call_spn sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc).
    all: wt_call WS MDL2.
Qed.

(* wcstok: VC after wcsspn returns (0x160164): empty remainder, or call wcscspn.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs wcstok_lib wcstok_callees wcstok_vc_postc.
Import ARM8Notations.
Open Scope N.

Lemma wt_after_spn:
  ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k st t
    (SPL: 96 <= sp) (W_SP: sp < 2^64) (PB: p + 8 <= sp - 48) (SB: wt_s mem s0 p + 4*Ls + 4 <= sp - 96)
    (CB: sep + 4*Lc + 4 <= sp - 96) (LsB: Ls < 2^61)
    (NFs: wcslen_proof.wcs_nilfree mem (wt_s mem s0 p) Ls) (Zs: mem Ⓓ[wt_s mem s0 p + 4*Ls] = 0)
    (NFc: wcslen_proof.wcs_nilfree mem sep Lc) (Zc: mem Ⓓ[sep + 4*Lc] = 0) (CP: 0 < sep) (SNZ: 0 < wt_s mem s0 p)
    (B30: raddr < 2^64) (B19: x19 < 2^64) (B20: x20 < 2^64) (B21: x21 < 2^64) (B22: x22 < 2^64) (B29: x29 < 2^64)
    (MDL: models arm8typctx st)
    (KL: k <= Ls) (SPN: wcsspn_proof.spn mem (wt_s mem s0 p) sep Lc k)
    (STOP: mem Ⓓ[wt_s mem s0 p + 4*k] = 0 \/ ¬ wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s mem s0 p + 4*k]))
    (MEM: st V_MEM64 = wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p) (RSP: st R_SP = sp - 48) (R0: st R_X0 = k)
    (R19: st R_X19 = wt_s mem s0 p) (R20: st R_X20 = sep) (R21: st R_X21 = p) (R29: st R_X29 = sp - 48),
  nextinv wt_prog (make_invs 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0))
    (make_exits 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)) true ((Addr 0x160164, st) :: t).
Proof.
  intros.
  assert (FR := wt_rd sp mem raddr x19 x20 x21 x22 x29 s0 sep p _ SPL W_SP B30 B19 B20 B21 B22 B29 (or_intror (or_introl eq_refl))).
  assert (AG := wt_agree sp mem raddr x19 x20 x21 x22 x29 s0 sep p _ SPL W_SP (or_intror (or_introl eq_refl))).
  assert (EK: (wt_s mem s0 p + (k << 2)) mod 2^64 = wt_s mem s0 p + 4*k) by (rewrite shl2; apply N.mod_small; lia).
  assert (EK2: wt_s mem s0 p + (k << 2) = wt_s mem s0 p + 4*k) by (rewrite shl2; reflexivity).
  assert (AGk: wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ⓓ[wt_s mem s0 p + 4*k] = mem Ⓓ[wt_s mem s0 p + 4*k]) by (apply AG; lia).
  do 3 arm8_step.
  all: rewrite EK2, AGk in BC.
  - (* remainder empty: *p = 0, return NULL *)
    apply N.eqb_eq in BC.
    abstract (
    repeat arm8_step;
    destruct (wt_frd_st _ _ _ _ _ _ _ _ p 0 FR SPL W_SP PB) as (F1 & F2 & F3 & F4 & F5 & F6);
    splits; try sassumption; try lia;
    right; left; exists k; splits; first [sassumption | reflexivity]).
  - (* a token starts at s + 4k: call wcscspn *)
    apply N.eqb_neq in BC.
    assert (NWk: ¬ wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s mem s0 p + 4*k])) by (destruct STOP; [contradiction | assumption]).
    clear STOP.
    do 3 arm8_step.
    set (s2 := update _ _ _).
    eapply models_after_steps. eassumption. apply wt_prog_welltyped. intro MDL2.
    apply (perform_call 1 2 eq_refl (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)
                                     (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 1)).
    + intros. abstract (eapply (wcscspn_correct_in_wcstok sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k);
        [ eassumption | eassumption
        | first [ reflexivity | exact RSP | exact MEM | exact EK | exact R19 | exact R20 | exact R21 | exact R29
                | (apply wt_cspn_pre; assumption) ] .. ]).
    + abstract (apply wt_sf).
    + intros a' s' t2 ENT XP UT PRE.
      eapply (wt_post_cspn sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k a' s').
      all: lazymatch goal with
           | |- true_inv _ => exact PRE
           | |- _ => sassumption
           end.
Qed.

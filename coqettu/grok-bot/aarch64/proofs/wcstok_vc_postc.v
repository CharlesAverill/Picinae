(* wcstok: from wcscspn's postcondition through its RET to the VC at 0x16017c.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs wcstok_lib wcstok_vc_cspn wcstok_vc_postq.
Import ARM8Notations.
Open Scope N.

Lemma wt_post_cspn:
  ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k a' s t
    (SPL: 96 <= sp) (W_SP: sp < 2^64) (PB: p + 8 <= sp - 48) (SB: wt_s mem s0 p + 4*Ls + 4 <= sp - 96)
    (CB: sep + 4*Lc + 4 <= sp - 96) (KL: k <= Ls)
    (B30: raddr < 2^64) (B19: x19 < 2^64) (B20: x20 < 2^64) (B21: x21 < 2^64) (B22: x22 < 2^64) (B29: x29 < 2^64)
    (SPN: wcsspn_proof.spn mem (wt_s mem s0 p) sep Lc k) (NZk: mem Ⓓ[wt_s mem s0 p + 4*k] ≠ 0)
    (NWk: ¬ wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s mem s0 p + 4*k]))
    (PRE: true_inv (get_postcondition wt_prog (make_invs 1 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 1))
             (make_exits 1 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 1)) a' s t)),
  nextinv wt_prog (make_invs 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0))
    (make_exits 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)) true ((Addr a', s) :: t).
Proof.
  intros.
  apply wtq_cspn in PRE. destruct PRE as (A & (j & JL & CS & TM & R0 & MD & RSP & R19 & R20 & R21 & R29 & R30) & K22).
  assert (AG := wt_agree sp mem raddr x19 x20 x21 x22 x29 s0 sep p _ SPL W_SP (or_intror (or_introl eq_refl))).
  assert (AGW := wt_agree sp mem raddr x19 x20 x21 x22 x29 s0 sep p _ SPL W_SP (or_intror (or_intror MD))).
  assert (FR := wt_rd sp mem raddr x19 x20 x21 x22 x29 s0 sep p _ SPL W_SP B30 B19 B20 B21 B22 B29 (or_intror (or_intror MD))).
  assert (CSPN := cspn_agree _ mem (sp - 96) (wt_s mem s0 p + 4*k) sep Lc j AG CB ltac:(lia) CS).
  replace (wt_s mem s0 p + 4*k + 4*j) with (wt_s mem s0 p + 4*(k+j)) in TM by lia.
  assert (TERM: mem Ⓓ[wt_s mem s0 p + 4*(k+j)] = 0 \/ wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s mem s0 p + 4*(k+j)])).
  { destruct TM as [T|T]; [left | right]; rewrite <- AG by lia; [exact T|].
    eapply cwinset_agree; [exact AG | exact CB | exact T]. }
  assert (WD: s V_MEM64 Ⓓ[wt_s mem s0 p + 4*(k+j)] = mem Ⓓ[wt_s mem s0 p + 4*(k+j)]) by (apply AGW; lia).
  destruct A as [-> | ->].
  all: arm8_step.
  all: eapply (wt_after_cspn sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k j (s V_MEM64)).
  all: lazymatch goal with
       | |- _ R_SP = _ => exact RSP
       | |- _ R_X0 = _ => exact R0
       | |- _ R_X21 = _ => exact R21
       | |- _ R_X22 = _ => exact K22
       | |- _ V_MEM64 = _ => reflexivity
       | |- _ <= _ => lia
       | |- wt_W2 _ _ _ _ _ _ _ _ _ _ _ _ => exact MD
       | |- _ => sassumption
       end.
Qed.

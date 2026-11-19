(* wcstok: the wcsspn call (0x160160): callee proof, then from wcsspn's
   postcondition through its RET to the VC at 0x160164.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs wcstok_lib wcstok_callees wcstok_vc_postq wcstok_vc_spn.
Import ARM8Notations.
Open Scope N.

Lemma wt_post_spn:
  ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc a' s t
    (SPL: 96 <= sp) (W_SP: sp < 2^64) (PB: p + 8 <= sp - 48) (SB: wt_s mem s0 p + 4*Ls + 4 <= sp - 96)
    (CB: sep + 4*Lc + 4 <= sp - 96) (LsB: Ls < 2^61)
    (NFs: wcslen_proof.wcs_nilfree mem (wt_s mem s0 p) Ls) (Zs: mem Ⓓ[wt_s mem s0 p + 4*Ls] = 0)
    (NFc: wcslen_proof.wcs_nilfree mem sep Lc) (Zc: mem Ⓓ[sep + 4*Lc] = 0) (CP: 0 < sep) (SNZ: 0 < wt_s mem s0 p)
    (B30: raddr < 2^64) (B19: x19 < 2^64) (B20: x20 < 2^64) (B21: x21 < 2^64) (B22: x22 < 2^64) (B29: x29 < 2^64)
    (MDL: models arm8typctx s)
    (PRE: true_inv (get_postcondition wt_prog (make_invs 1 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0))
             (make_exits 1 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)) a' s t)),
  nextinv wt_prog (make_invs 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0))
    (make_exits 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)) true ((Addr a', s) :: t).
Proof.
  intros.
  apply wtq_spn in PRE. destruct PRE as (-> & (k & KL & SPN1 & STOP1 & R0 & MEM & RSP & R19 & R20 & R21 & R29 & R30)).
  assert (AG := wt_agree sp mem raddr x19 x20 x21 x22 x29 s0 sep p _ SPL W_SP (or_introl eq_refl)).
  assert (SPN := spn_agree _ mem (sp - 96) (wt_s mem s0 p) sep Lc k AG CB ltac:(lia) SPN1).
  assert (STOP: mem Ⓓ[wt_s mem s0 p + 4*k] = 0 \/ ¬ wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s mem s0 p + 4*k])).
  { rewrite <- (AG (wt_s mem s0 p + 4*k)) by lia. destruct STOP1 as [T|T]; [left; exact T | right].
    intro W. apply T. eapply winset_agree; [exact (agreeD_sym _ _ _ AG) | exact CB | exact W]. }
  clear SPN1 STOP1.
  arm8_step.
  eapply (wt_after_spn sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k).
  all: lazymatch goal with
       | |- _ V_MEM64 = _ => exact MEM
       | |- _ R_SP = _ => exact RSP
       | |- _ R_X0 = _ => exact R0
       | |- _ R_X19 = _ => exact R19
       | |- _ R_X20 = _ => exact R20
       | |- _ R_X21 = _ => exact R21
       | |- _ R_X29 = _ => exact R29
       | |- models _ _ => (repeat (apply models_update; [vm_compute; first [reflexivity | exact I] |])); exact MDL
       | |- _ => sassumption
       end.
Qed.

Lemma wt_call_spn:
  ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc st t
    (SPL: 96 <= sp) (W_SP: sp < 2^64) (PB: p + 8 <= sp - 48) (SB: wt_s mem s0 p + 4*Ls + 4 <= sp - 96)
    (CB: sep + 4*Lc + 4 <= sp - 96) (LsB: Ls < 2^61)
    (NFs: wcslen_proof.wcs_nilfree mem (wt_s mem s0 p) Ls) (Zs: mem Ⓓ[wt_s mem s0 p + 4*Ls] = 0)
    (NFc: wcslen_proof.wcs_nilfree mem sep Lc) (Zc: mem Ⓓ[sep + 4*Lc] = 0) (CP: 0 < sep) (SNZ: 0 < wt_s mem s0 p)
    (B30: raddr < 2^64) (B19: x19 < 2^64) (B20: x20 < 2^64) (B21: x21 < 2^64) (B22: x22 < 2^64) (B29: x29 < 2^64)
    (MDL: models arm8typctx st)
    (SP: st R_SP = sp - 48) (MEM: st V_MEM64 = wt_M1 sp mem raddr x19 x20 x21 x22 x29) (X30: st R_X30 = 0x160164)
    (X0: st R_X0 = wt_s mem s0 p) (X1: st R_X1 = sep)
    (X19: st R_X19 = wt_s mem s0 p) (X20: st R_X20 = sep) (X21: st R_X21 = p) (X29: st R_X29 = sp - 48),
  nextinv wt_prog (make_invs 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0))
    (make_exits 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)) true ((Addr 0x15fe6c, st) :: t).
Proof.
  intros.
  apply (perform_call 1 2 eq_refl (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)
                                   (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)).
  - intros. eapply (wcsspn_correct_in_wcstok sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 st t0 xs' ENTRY MDL
                      SP MEM X30 X0 X1 X19 X20 X21 X29).
    apply wt_spn_pre; assumption.
  - reflexivity.
  - intros a' s' t2 ENT XP UT PRE.
    assert (MDL': models arm8typctx s').
      eapply preservation_exec_prog; try eassumption. apply wt_prog_welltyped.
    eapply (wt_post_spn sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc a' s').
    all: lazymatch goal with
         | |- true_inv _ => exact PRE
         | |- _ => sassumption
         end.
Qed.

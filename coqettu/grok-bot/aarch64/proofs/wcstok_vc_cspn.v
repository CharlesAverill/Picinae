(* wcstok: VC after wcscspn returns (0x16017c to RET): terminate the token, update *p.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs wcstok_lib.
Import ARM8Notations.
Open Scope N.

Lemma wt_after_cspn:
  ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k j (W: memory) st t
    (SPL: 96 <= sp) (W_SP: sp < 2^64) (PB: p + 8 <= sp - 48) (SB: wt_s mem s0 p + 4*Ls + 4 <= sp - 96)
    (KJ: k + j <= Ls)
    (FR: wt_frd W sp raddr x19 x20 x21 x22 x29) (WW: wt_W2 sp mem raddr x19 x20 x21 x22 x29 s0 sep p W)
    (SPN: wcsspn_proof.spn mem (wt_s mem s0 p) sep Lc k) (NZk: mem Ⓓ[wt_s mem s0 p + 4*k] ≠ 0)
    (NWk: ¬ wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s mem s0 p + 4*k]))
    (CSPN: wcscspn_proof.cspn mem (wt_s mem s0 p + 4*k) sep Lc j)
    (TERM: mem Ⓓ[wt_s mem s0 p + 4*(k+j)] = 0 \/ wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s mem s0 p + 4*(k+j)]))
    (WD: W Ⓓ[wt_s mem s0 p + 4*(k+j)] = mem Ⓓ[wt_s mem s0 p + 4*(k+j)])
    (MEM: st V_MEM64 = W) (RSP: st R_SP = sp - 48) (R0: st R_X0 = j)
    (K22: st R_X22 = wt_s mem s0 p + 4*k) (K21: st R_X21 = p),
  nextinv wt_prog (make_invs 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0))
    (make_exits 2 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc 0 0)) true ((Addr 0x16017c, st) :: t).
Proof.
  intros.
  assert (EA: wt_s mem s0 p + 4*k + (j << 2) = wt_s mem s0 p + 4*(k+j)) by (rewrite shl2; lia).
  assert (EB: 4 + wt_s mem s0 p + 4*k + (j << 2) = wt_s mem s0 p + 4*(k+j) + 4) by (rewrite shl2; lia).
  repeat arm8_step.
  all: rewrite ?EA, ?EB in *.
  - (* end of string: *p = 0 *)
    apply N.eqb_eq in BC. rewrite WD in BC.
    destruct (wt_frd_st _ _ _ _ _ _ _ _ p 0 FR SPL W_SP PB) as (F1 & F2 & F3 & F4 & F5 & F6).
    splits; try sassumption; try lia.
    right. right. exists k, j, W. splits; try sassumption; try reflexivity.
    left. split; [exact BC | reflexivity].
  - (* delimiter found: overwrite it with L'\0', *p = next character *)
    apply N.eqb_neq in BC. rewrite WD in BC.
    assert (FR' := wt_frd_st _ _ _ _ _ _ _ _ p (wt_s mem s0 p + 4*(k+j) + 4)
                     (wt_frd_stD _ _ _ _ _ _ _ _ (wt_s mem s0 p + 4*(k+j)) 0 FR SPL W_SP ltac:(lia)) SPL W_SP PB).
    destruct FR' as (F1 & F2 & F3 & F4 & F5 & F6).
    splits; try sassumption; try lia.
    right. right. exists k, j, W. splits; try sassumption; try reflexivity.
    right. split; [destruct TERM; [contradiction | assumption] | reflexivity].
Qed.

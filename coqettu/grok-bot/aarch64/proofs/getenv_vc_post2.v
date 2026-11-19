(* getenv: strncmp postcondition to getenv_vc_ret2.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in getenv_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require getenv_armv8 strncmp_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCall GrokKeep.
From Grok.proofs Require strchrnul_proof strncmp_proof.
From Grok.proofs Require Import getenv_defs getenv_callees getenv_lib getenv_vc_ret2 getenv_vc_post2pre.
Import ARM8Notations.
Open Scope N.


Ltac ringmod := unfold env_entry; match goal with |- (?a) mod ?m = (?b) mod ?m => replace b with a by ring; reflexivity end.
Ltac scontra BB := lazymatch type of BB with ?X = ?Y =>
  match goal with H: ¬ (?X' = ?Y') |- _ => constr_eq X X'; constr_eq Y Y'; exact (H BB) end end.

Lemma gv_post_ncmp:
  ∀ sp mem raddr x19 x20 x21 x29 name L j q a' s t
    (SC: strchrnul_proof.scan (gv_M sp mem raddr x19 x20 x21 x29) name 0x3d L)
    (NL: name + L < 2^64) (SPL: 48 <= sp) (W_SP: sp < 2^64)
    (G48: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 48] = x29) (G40: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 40] = raddr) (G32: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 32] = x19)
    (G24: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 24] = x20) (G16: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 16] = x21)
    (LP: 0 < L) (NZ: (gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[name + L] = 0) (EN: gv_env (gv_M sp mem raddr x19 x20 x21 x29) ≠ 0)
    (SK: gv_skip (gv_M sp mem raddr x19 x20 x21 x29) name (gv_env (gv_M sp mem raddr x19 x20 x21 x29)) L j)
    (HQ: q = (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[gv_env (gv_M sp mem raddr x19 x20 x21 x29) + 8 * j]) (BC: q ≠ 0)
    (PRE: true_inv (get_postcondition gv_prog
             (make_invs 2 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L q (gv_env (gv_M sp mem raddr x19 x20 x21 x29) ⊕ 8 * j)))
             (make_exits 2 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L q (gv_env (gv_M sp mem raddr x19 x20 x21 x29) ⊕ 8 * j))) a' s t)),
  nextinv gv_prog (make_invs 3 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L 0 0))
    (make_exits 3 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L 0 0)) true ((Addr a', s) :: t).
Proof.
  intros.
      apply gvq_pre in PRE.
      destruct PRE as (-> & (RES & MEM' & RSP & R30) & K19 & K20 & K21).
      destruct RES as [(R0 & L0) | (k & KL & EQk & NFk & STk & R0)].
        exfalso. rewrite L0 in LP. exact (N.lt_irrefl 0 LP).
      subst q.
      arm8_step.
      eapply (gv_after_ncmp sp mem raddr x19 x20 x21 x29 name L j k).
      all: lazymatch goal with
           | |- _ R_SP = _ => exact RSP
           | |- _ V_MEM64 = _ => exact MEM'
           | |- _ R_X0 = _ => exact R0
           | |- _ R_X19 = _ => exact K19
           | |- _ R_X20 = _ => exact K20
           | |- _ R_X21 = _ => exact K21
           | |- _ => sassumption
           end.
Qed.

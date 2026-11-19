(* getenv: loop case (0x11ffdc): NULL-entry exit and strncmp call.
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
From Grok.proofs Require Import getenv_defs getenv_callees getenv_lib getenv_vc_ret2 getenv_vc_post2.
Import ARM8Notations.
Open Scope N.


Ltac ringmod := unfold env_entry; match goal with |- (?a) mod ?m = (?b) mod ?m => replace b with a by ring; reflexivity end.
Ltac scontra BB := lazymatch type of BB with ?X = ?Y =>
  match goal with H: ¬ (?X' = ?Y') |- _ => constr_eq X X'; constr_eq Y Y'; exact (H BB) end end.

Lemma gv_case_loop:
  ∀ sp mem raddr x19 x20 x21 x29 name L s1 t
    (SC: strchrnul_proof.scan (gv_M sp mem raddr x19 x20 x21 x29) name 0x3d L)
    (ST: gv_M sp mem raddr x19 x20 x21 x29 Ⓑ[name + L] = 0 \/ gv_M sp mem raddr x19 x20 x21 x29 Ⓑ[name + L] = 0x3d)
    (NL: name + L < 2^64) (SPL: 48 <= sp) (W_SP: sp < 2^64) (W19: x19 < 2^64) (W20: x20 < 2^64)
    (W21: x21 < 2^64) (W29: x29 < 2^64) (W30: raddr < 2^64) (W0: name < 2^64) (MDL1: models arm8typctx s1)
    (PRE: gv_loop sp mem raddr x19 x20 x21 x29 name L s1),
  nextinv gv_prog (gv_invs3 sp mem raddr x19 x20 x21 x29 name L 0 0)
    (gv_exits3 sp mem raddr x19 x20 x21 x29 name L 0 0) false ((Addr 0x11ffdc, s1) :: t).
Proof.
  intros.
    destruct PRE as (j & R19 & R20 & R21 & LP & NZ & EN & SK & MEM & SP).
    destruct (gv_rd sp mem raddr x19 x20 x21 x29 SPL W_SP W30 W19 W20 W21 W29) as (G48 & G40 & G32 & G24 & G16).
    arm8_step. arm8_step.
    all: gv_bools.
    + (* entry == NULL *)
      abstract ((repeat arm8_step) ; (set (M := gv_M sp mem raddr x19 x20 x21 x29) in *; clearbody M) ; (split; [first [sreflexivity | apply N.mod_small; sassumption] |]) ; (split; [sassumption|]; split; [sassumption|]; split; [sassumption|]; split; [sassumption|]; split; [sassumption|]) ; (split; [sreflexivity|]) ; (left; split; [sreflexivity|]; right; right; right; exists j; split; [sassumption | unfold env_entry; sassumption])).
    + do 3 arm8_step.
      set (s2 := update _ _ _).
      eapply models_after_steps. eassumption. apply gv_prog_welltyped. intro MDL2.
      eapply (perform_call 2 3 eq_refl _ (invs sp mem raddr x19 x20 x21 x29 name L ((gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[gv_env (gv_M sp mem raddr x19 x20 x21 x29) + 8 * j]) (gv_env (gv_M sp mem raddr x19 x20 x21 x29) ⊕ 8 * j))).
      intros. abstract (eapply (strncmp_correct_in_getenv sp mem raddr x19 x20 x21 x29 name L); [eassumption | eassumption | first [reflexivity | exact SP] ..]).
      abstract (apply gv_sf).
      intros a' s' t2 ENT XP UT PRE.
      eapply (gv_post_ncmp sp mem raddr x19 x20 x21 x29 name L j _ a' s' (t2++t0++_::t)).
      all: lazymatch goal with
           | |- true_inv _ => exact PRE
           | |- _ = _ => first [ sassumption | reflexivity ]
           | |- _ => sassumption
           end.
Qed.

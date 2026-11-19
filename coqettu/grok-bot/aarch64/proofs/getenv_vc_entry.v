(* getenv: entry case: prologue, __strchrnul call, hand-off to getenv_vc_ret1.
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
From Grok.proofs Require Import getenv_defs getenv_callees getenv_lib getenv_vc_ret1.
Import ARM8Notations.
Open Scope N.



Lemma gv_case_entry:
  ∀ sp mem raddr x19 x20 x21 x29 name L s1 t
    (SC: strchrnul_proof.scan (gv_M sp mem raddr x19 x20 x21 x29) name 0x3d L)
    (ST: gv_M sp mem raddr x19 x20 x21 x29 Ⓑ[name + L] = 0 \/ gv_M sp mem raddr x19 x20 x21 x29 Ⓑ[name + L] = 0x3d)
    (NL: name + L < 2^64) (SPL: 48 <= sp) (W_SP: sp < 2^64) (W19: x19 < 2^64) (W20: x20 < 2^64)
    (W21: x21 < 2^64) (W29: x29 < 2^64) (W30: raddr < 2^64) (W0: name < 2^64) (MDL1: models arm8typctx s1)
    (PRE: s1 R_X0 = name /\ s1 V_MEM64 = mem /\ s1 R_SP = sp /\ s1 R_X30 = raddr /\
          s1 R_X19 = x19 /\ s1 R_X20 = x20 /\ s1 R_X21 = x21 /\ s1 R_X29 = x29),
  nextinv gv_prog (gv_invs3 sp mem raddr x19 x20 x21 x29 name L 0 0)
    (gv_exits3 sp mem raddr x19 x20 x21 x29 name L 0 0) false ((Addr 0x11ff88, s1) :: t).
Proof.
  intros.
    pose proof (gv_rd sp mem raddr x19 x20 x21 x29 SPL W_SP W30 W19 W20 W21 W29) as GR.
    clear W19 W20 W21 W29 W30.
    destruct PRE as (X0 & MEM & SP & X30 & X19 & X20 & X21 & X29).
    do 7 arm8_step.
    set (s2 := update _ _ _).
    eapply models_after_steps. eassumption. apply gv_prog_welltyped. intro MDL2.
    eapply (perform_call 1). reflexivity.
    intros. eapply (strchrnul_correct_in_getenv sp mem raddr x19 x20 x21 x29 name L 0 0); [eassumption | eassumption | reflexivity ..].
    reflexivity.
    intros.
    unfold s2 in PRE. psimpl in PRE.
    assert (MDL': models arm8typctx s').
      eapply preservation_exec_prog; try eassumption. apply gv_prog_welltyped.
    set (t' := t2++t0++_::t) in *. clearbody s2 t'.
    rename MDL' into MDL. rename s' into s.
    destruct_inv 64 PRE.
    all: destruct PRE as ((RSP & R30 & R29 & ALT) & (K21 & _)).
    all: destruct ALT as [(MEM' & C8 & k & KLT & SCk & STk & R0) | (_ & C8 & _)];
         [| vm_compute in C8; discriminate].
    all: change (strchrnul_proof.c8 61) with 61 in *.
    all: assert (k = L) by (eapply scan_unique; eassumption); subst k.
    all: rewrite N.mod_small in R0 by lia.
    all: simpl in K21.
    all: arm8_step.
    all: destruct GR as (G48 & G40 & G32 & G24 & G16).
    all: eapply (gv_after_chrnul sp mem raddr x19 x20 x21 x29 name L).
    all: lazymatch goal with
         | |- _ R_SP = _ => exact RSP
         | |- _ V_MEM64 = _ => exact MEM'
         | |- _ R_X0 = _ => exact R0
         | |- _ R_X21 = _ => exact K21
         | |- _ => sassumption
         end.
Qed.

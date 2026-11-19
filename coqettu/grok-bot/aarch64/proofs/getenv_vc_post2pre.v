(* getenv: shape of the strncmp postcondition inside the getenv family (generic parameters keep kernel checking cheap).
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
From Grok.proofs Require Import getenv_defs getenv_callees getenv_lib getenv_vc_ret2.
Import ARM8Notations.
Open Scope N.


Ltac ringmod := unfold env_entry; match goal with |- (?a) mod ?m = (?b) mod ?m => replace b with a by ring; reflexivity end.
Ltac scontra BB := lazymatch type of BB with ?X = ?Y =>
  match goal with H: ¬ (?X' = ?Y') |- _ => constr_eq X X'; constr_eq Y Y'; exact (H BB) end end.

Lemma gvq_pre:
  ∀ sp mem raddr x19 x20 x21 x29 name L q k19 a' s t,
  true_inv (get_postcondition gv_prog
             (make_invs 2 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L q k19))
             (make_exits 2 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L q k19)) a' s t) ->
  a' = 0x15f140 /\
  ((s R_X0 = 0 /\ L = 0 \/
    (∃ k, k < L /\ mem_eq (gv_M sp mem raddr x19 x20 x21 x29) name q k /\ nilfree (gv_M sp mem raddr x19 x20 x21 x29) name k /\
          ((gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[name + k] ≠ (gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[q + k] \/ (gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[name + k] = 0 \/ k = L - 1) /\
          s R_X0 = msub 32 ((gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[name + k]) ((gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[q + k]))) /\
   s V_MEM64 = (gv_M sp mem raddr x19 x20 x21 x29) /\ s R_SP = sp ⊖ 48 /\ s R_X30 = 0x11fff0) /\
  s R_X19 = k19 /\ s R_X20 = L /\ s R_X21 = name.
Proof.
  intros until t. intro PRE.
  destruct_inv 64 PRE.
  destruct PRE as (P & K19 & K20 & K21 & _).
  split. reflexivity. split. exact P. split. exact K19. split. exact K20. exact K21.
Qed.

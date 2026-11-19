(* wcstok: shapes of the callee postconditions at level 1 (the other callee's
   return points are excluded by the phase parameter).
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs.
Import ARM8Notations.
Open Scope N.

Lemma wtq_spn: ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k a' s t,
  true_inv (get_postcondition wt_prog (make_invs 1 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 0))
             (make_exits 1 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 0)) a' s t) ->
  a' = 0x15feb8 /\
  wcsspn_proof.wcsspn_post (sp - 48) (wt_M1 sp mem raddr x19 x20 x21 x22 x29) 0x160164 (wt_s mem s0 p) sep
    (wt_s mem s0 p) sep p (sp - 48) Ls Lc s.
Proof.
  intros until t. intro PRE.
  destruct_inv 64 PRE.
  all: destruct PRE as [P PH]; try discriminate PH.
  split. reflexivity. exact P.
Qed.

Lemma wtq_cspn: ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k a' s t,
  true_inv (get_postcondition wt_prog (make_invs 1 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 1))
             (make_exits 1 wt_prog (invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 1)) a' s t) ->
  (a' = 0x15fbcc \/ a' = 0x15fc34) /\
  wcscspn_proof.wcscspn_post (sp - 48) (wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p) 0x16017c
    (wt_s mem s0 p + 4*k) sep (wt_s mem s0 p) sep p (sp - 48) (Ls - k) Lc s /\
  s R_X22 = wt_s mem s0 p + 4*k.
Proof.
  intros until t. intro PRE.
  destruct_inv 64 PRE.
  all: destruct PRE as [P PH]; try discriminate PH.
  all: destruct P as [P [K22 _]].
  all: split; [tauto | split; [exact P | exact K22]].
Qed.

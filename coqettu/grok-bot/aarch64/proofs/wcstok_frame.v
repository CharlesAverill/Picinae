(* wcstok: AAPCS64 callee-saved registers other than X19-X22/X29/X30 are never
   written by wcstok, wcsspn, wcscspn, wcschr or wcslen.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith List.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokCommon.
From Grok.proofs Require Import wcstok_defs.
Open Scope N.

Theorem wcstok_preserves_other_callee_saved:
  ∀ r, In r (R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates wt_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

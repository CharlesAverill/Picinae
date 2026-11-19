(* strrchr: composed program (strrchr + memrchr + strlen), frame and invariant family.
   strrchr (level 1, entry 0x15f228) saves X29/X30/X19 and the 32-bit c, calls strlen
   (level 0, 0x15efa8; invariants of strlen_proof.v, strengthened with X19 = s), restores
   the frame and tail-calls memrchr(s, c, strlen(s) + 1) (0x15e83c; invariants of
   memrchr_defs.v instantiated at level 1).
   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strrchr_armv8 memrchr_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon.
From Grok.proofs Require Import strlen_proof memrchr_defs.
Import ARM8Notations.
Open Scope N.

Definition rr_prog : program :=
  updateall2 (updateall2 strrchr_armv8.strrchr_armv8 memrchr_armv8.memrchr_armv8) strlen_armv8.strlen_armv8.

(* strrchr's 48-byte frame: saved X29, X30, X19 and c (32-bit, at sp-4). *)
Definition rr_frame (sp mem raddr x19 x29 c:N) :=
  mem [Ⓠ sp ⊖ 48 := x29] [Ⓠ sp ⊖ 40 := raddr] [Ⓠ sp ⊖ 32 := x19] [Ⓓ sp ⊖ 4 := c].

Section Invariants.
  Variables (sp mem raddr x19 x29 p c n : N).
  Definition rr_mem := rr_frame sp mem raddr x19 x29 c.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15f228 then
      Inv 1 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X29 = x29)
    else if a <? 0x15efa8 then
      memrchr_defs.invs 1 sp rr_mem raddr x19 x29 p (c mod 2^32) n T Inv Post NoInv s a
    else if a <? 0x15f228 then
      strlen_proof.invs (sp ⊖ 48) rr_mem 0x15f240 p T
        (fun l P => Inv l (P /\ s R_X19 = p)) (fun l P => Post l (P /\ s R_X19 = p)) NoInv s a
    else NoInv.
  Definition exits1 := make_exits 1 rr_prog invs.
  Definition invs1 := make_invs 1 rr_prog invs.
  Definition exits0 := make_exits 0 rr_prog invs.
  Definition invs0 := make_invs 0 rr_prog invs.
End Invariants.


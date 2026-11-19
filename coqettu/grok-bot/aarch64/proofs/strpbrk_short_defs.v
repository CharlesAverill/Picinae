(* strpbrk short reject-set definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Program pbs_prog = strpbrk + css_prog (strcspn + __strchrnul + strlen), frame,
   precondition (strlen(c) < 2), postcondition, invariant family.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O spec) is in
   strpbrk_short_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strpbrk_armv8 strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require strcspn_defs.
From Grok.proofs Require Import strcspn_short_defs.
Import ARM8Notations.
Open Scope N.

Definition pbs_prog : program := updateall2 strpbrk_armv8.strpbrk_armv8 css_prog.

(* strpbrk's frame after stp x29,x30,[sp,#-32]! / str x19,[sp,#16] *)
Definition pbs_frame (sp mem raddr x19 x29 : N) :=
  mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19].

(* Short reject sets strlen(c) < 2 (strcspn's __strchrnul path). *)
Definition pbs_pre (sp mem p c Ks Lc : N) :=
  nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\ Lc < 2 /\
  144 <= sp /\ sp < 2^64 /\ p + Ks + 145 <= sp /\ c + Lc + 145 <= sp.

Definition pbs_post (sp mem raddr p c Ks Lc x19 x29 : N) (s:store) :=
  (∃ K, K <= Ks /\ (∀ i, i < K -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) /\
        ((K = Ks /\ s R_X0 = 0) \/ (K < Ks /\ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K]) /\ s R_X0 = p + K))) /\
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  (∀ a, a < 2^64 -> (a < sp - 144 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]).

Section Invariants.
  Variables (sp mem raddr p c Ks Lc x19 x29 : N).
  Definition pbs_F := css_invs (sp ⊖ 32) (pbs_frame sp mem raddr x19 x29) 0x15f20c p c p (sp ⊖ 32) Ks Lc.
  Definition pbs_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15f1f8 then
      Inv 3 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X29 = x29)
    else if a =? 0x15f224 then Post 3 (pbs_post sp mem raddr p c Ks Lc x19 x29 s)
    (* strcspn short path (family 2) and strchrnul/strlen (1/0) invariants *)
    else pbs_F T Inv Post NoInv s a.
  Definition pbs_exits3 := make_exits 3 pbs_prog pbs_invs.
  Definition pbs_invs3 := make_invs 3 pbs_prog pbs_invs.
  Definition pbs_exits2 := make_exits 2 pbs_prog pbs_invs.
  Definition pbs_invs2 := make_invs 2 pbs_prog pbs_invs.
End Invariants.


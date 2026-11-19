(* strsep short separator-set definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Program ses_prog = strsep + css_prog (strcspn + __strchrnul + strlen), frame,
   precondition ( *str = 0 or strlen(sep) < 2), postcondition, invariant family.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O spec) is in
   strsep_short_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strsep_armv8 strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require strcspn_defs.
From Grok.proofs Require Import strcspn_short_defs.
Import ARM8Notations.
Open Scope N.

Definition ses_prog : program := updateall2 strsep_armv8.strsep_armv8 css_prog.

(* strsep's frame after stp x29,x30,[sp,#-32]! / stp x2,x3,[sp,#16] (s, str spilled) *)
Definition ses_frame (sp mem raddr x29 p q : N) :=
  mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := p] [Ⓠ sp ⊖ 8 := q].

(* str = q (address of the char* variable), *str = p.  If p <> 0, short
   separator sets strlen(sep) < 2 (strcspn's __strchrnul path). *)
Definition ses_pre (sp mem q p c Ks Lc : N) :=
  mem Ⓠ[q] = p /\
  (p = 0 \/ (nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\ Lc < 2 /\
             144 <= sp /\ sp < 2^64 /\ p + Ks + 145 <= sp /\ c + Lc + 145 <= sp /\ q + 8 + 144 <= sp)).

Definition ses_post (sp mem raddr q p c Ks Lc x19 x29 : N) (s:store) :=
  s R_X0 = p /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  ∃ K, K <= Ks /\ (∀ i, i < K -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) /\
    ((K = Ks /\ ∀ a, a < 2^64 -> (a < sp - 144 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem [Ⓠ q := 0] Ⓑ[a]) \/
     (K < Ks /\ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K]) /\
      ∀ a, a < 2^64 -> (a < sp - 144 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem [Ⓑ p + K := 0] [Ⓠ q := p + K + 1] Ⓑ[a])).

Section Invariants.
  Variables (sp mem raddr q p c Ks Lc x19 x29 : N).
  Definition ses_F := css_invs (sp ⊖ 32) (ses_frame sp mem raddr x29 p q) 0x15f278 p c x19 (sp ⊖ 32) Ks Lc.
  Definition ses_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15f258 then
      Inv 3 (s R_X0 = q /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X29 = x29)
    else if a =? 0x15f2a0 then Post 3 (ses_post sp mem raddr q p c Ks Lc x19 x29 s)
    else if a =? 0x15f2a8 then Post 3 (p = 0 /\ s R_X0 = 0 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    else ses_F T Inv Post NoInv s a.
  Definition ses_exits3 := make_exits 3 ses_prog ses_invs.
  Definition ses_invs3 := make_invs 3 ses_prog ses_invs.
  Definition ses_exits2 := make_exits 2 ses_prog ses_invs.
  Definition ses_invs2 := make_invs 2 ses_prog ses_invs.
End Invariants.

(* strsep definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Program se_prog (strsep + strcspn + memset), precondition se_pre, postcondition
   se_post and invariant set se_invs for proofs/strsep_proof.v (see the header there
   for semantics, man page, provenance and the full I/O specification).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strsep_armv8 strcspn_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require Import strcspn_defs.
Import ARM8Notations.
Open Scope N.

Definition se_prog : program := updateall2 strsep_armv8.strsep_armv8 cs_prog.

(* strsep's frame after stp x29,x30,[sp,#-32]! / stp x2,x3,[sp,#16] (s, str spilled) *)
Definition se_frame (sp mem raddr x29 p q : N) :=
  mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := p] [Ⓠ sp ⊖ 8 := q].

(* str = q (address of the char* variable), *str = p.  If p <> 0 the strcspn
   restriction strlen(sep) >= 2 is inherited. *)
Definition se_pre (sp mem q p c Ks Lc : N) :=
  mem Ⓠ[q] = p /\
  (p = 0 \/ (nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\ 2 <= Lc /\
             4096 + 112 <= sp /\ sp < 2^64 /\ p + Ks + 113 <= sp /\ c + Lc + 113 <= sp /\ q + 8 + 112 <= sp)).

Definition se_post (sp mem raddr q p c Ks Lc x19 x29 : N) (s:store) :=
  s R_X0 = p /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  ∃ K, K <= Ks /\ (∀ i, i < K -> ~ cs_in mem c Lc (mem Ⓑ[p + i])) /\
    ((K = Ks /\ ∀ a, a < 2^64 -> (a < sp - 112 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem [Ⓠ q := 0] Ⓑ[a]) \/
     (K < Ks /\ cs_in mem c Lc (mem Ⓑ[p + K]) /\
      ∀ a, a < 2^64 -> (a < sp - 112 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem [Ⓑ p + K := 0] [Ⓠ q := p + K + 1] Ⓑ[a])).

Section Invariants.
  Variables (sp mem raddr q p c Ks Lc x19 x29 : N).
  Definition se_F := strcspn_defs.invs (sp ⊖ 32) (se_frame sp mem raddr x29 p q) 0x15f278 p c x19 (sp ⊖ 32) Ks Lc.
  Definition se_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15f258 then
      Inv 2 (s R_X0 = q /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X29 = x29)
    else if a =? 0x15f2a0 then Post 2 (se_post sp mem raddr q p c Ks Lc x19 x29 s)
    else if a =? 0x15f2a8 then Post 2 (p = 0 /\ s R_X0 = 0 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    else se_F T Inv Post NoInv s a.
  Definition se_exits2 := make_exits 2 se_prog se_invs.
  Definition se_invs2 := make_invs 2 se_prog se_invs.
  Definition se_exits1 := make_exits 1 se_prog se_invs.
  Definition se_invs1 := make_invs 1 se_prog se_invs.
End Invariants.

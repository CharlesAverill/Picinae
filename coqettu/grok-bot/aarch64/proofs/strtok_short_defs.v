(* strtok, short separator-set path -- definitions.  musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Program tks_prog = strtok + strspn + css_prog (strcspn + __strchrnul + strlen),
   precondition (strlen(sep) < 2), postcondition, invariant family.
   Full header is in strtok_short_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strtok_armv8 strspn_armv8 strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.lib Require Import GrokKeep.
From Grok.proofs Require strcspn_defs strspn_defs strcspn_short_defs.
From Grok.proofs Require Import strtok_defs.
Import ARM8Notations.
Open Scope N.

Definition tks_prog : program :=
  updateall2 (updateall2 strtok_armv8.strtok_armv8 strspn_armv8.strspn_armv8) strcspn_short_defs.css_prog.

(* s0 = the s argument; p = the string actually scanned (s0, or the saved static if s0 = NULL). *)
Definition tks_pre (sp mem s0 p c Ks Lc : N) :=
  ((s0 <> 0 /\ p = s0) \/ (s0 = 0 /\ mem Ⓠ[tk_G] = p)) /\ tk_G + 8 + 176 <= sp /\ sp < 2^64 /\
  (p = 0 \/ (nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\ Lc < 2 /\
             mem Ⓧ[0x19e6b0] = 0 /\ mem Ⓧ[0x19e6c0] = 0 /\
             p + Ks + 177 <= sp /\ c + Lc + 177 <= sp)).

Definition tks_out (sp:N) (s:store) (M:memory) :=
  ∀ a, a < 2^64 -> (a < sp - 176 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = M Ⓑ[a].

Definition tks_post (sp mem raddr p c Ks Lc x19 x20 x21 x29 : N) (s:store) :=
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  ((p = 0 /\ s R_X0 = 0 /\ tks_out sp s mem) \/
   (p <> 0 /\ ∃ K1, K1 <= Ks /\ (∀ i, i < K1 -> strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) /\
     ((K1 = Ks /\ s R_X0 = 0 /\ tks_out sp s (mem [Ⓠ tk_G := 0])) \/
      (K1 < Ks /\ ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K1]) /\ s R_X0 = p + K1 /\
       ∃ K2, K1 + K2 <= Ks /\ (∀ i, i < K2 -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K1 + i])) /\
         ((K1 + K2 = Ks /\ tks_out sp s (mem [Ⓠ tk_G := 0])) \/
          (K1 + K2 < Ks /\ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K1 + K2]) /\
           tks_out sp s (mem [Ⓠ tk_G := p + K1 + K2 + 1] [Ⓑ p + K1 + K2 := 0]))))))).

Section Invariants.
  Variables (sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 : N).
  Definition tks_FR := tk_frame sp mem raddr x19 x20 x21 x29.
  (* short strcspn (families 2/1/0: strcspn/strchrnul/strlen), entered with memory M1 at s = p + K1; X21 carried *)
  Definition tks_Fcs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    strcspn_short_defs.css_invs (sp ⊖ 64) M1 0x15f808 (p + K1) c p (sp ⊖ 64) (Ks - K1) Lc T
      (fun n P => Inv n (P /\ keepl_st ((R_X21, 0x1c2000)::nil) s))
      (fun n P => Post n (P /\ keepl_st ((R_X21, 0x1c2000)::nil) s)) NoInv s a.
  (* strspn (its family 0 renumbered 3); X19 = p, X20 = c, X21, X29 carried *)
  Definition tks_L := (R_X19, p) :: (R_X20, c) :: (R_X21, 0x1c2000) :: (R_X29, sp ⊖ 64) :: nil.
  Definition tks_Fss T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    strspn_defs.ss_invs (sp ⊖ 64) tks_FR 0x15f7ec p c Ks Lc T
      (fun _ P => Inv 3 (P /\ keepl_st tks_L s)) (fun _ P => Post 3 (P /\ keepl_st tks_L s)) NoInv s a.
  Definition tks_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15f7c4 then
      Inv 4 (s R_X0 = s0 /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29)
    else if a =? 0x15f7e0 then
      Inv 4 (p <> 0 /\ s R_X19 = p /\ s R_X1 = c /\ s R_X21 = 0x1c2000 /\ s R_SP = sp ⊖ 64 /\ s R_X29 = sp ⊖ 64 /\
             s V_MEM64 = tks_FR)
    else if a =? 0x15f834 then Post 4 (tks_post sp mem raddr p c Ks Lc x19 x20 x21 x29 s)
    else if a =? 0x15f2e8 then tks_Fss T Inv Post NoInv s a
    else if a =? 0x15f380 then tks_Fss T Inv Post NoInv s a
    else if a =? 0x15f314 then tks_Fss T Inv Post NoInv s a
    else if a =? 0x15f340 then tks_Fss T Inv Post NoInv s a
    else if a =? 0x15f360 then tks_Fss T Inv Post NoInv s a
    else tks_Fcs T Inv Post NoInv s a.
  Definition tks_exits4 := make_exits 4 tks_prog tks_invs.
  Definition tks_invs4 := make_invs 4 tks_prog tks_invs.
  Definition tks_exits3 := make_exits 3 tks_prog tks_invs.
  Definition tks_invs3 := make_invs 3 tks_prog tks_invs.
  Definition tks_exits2 := make_exits 2 tks_prog tks_invs.
  Definition tks_invs2 := make_invs 2 tks_prog tks_invs.
End Invariants.

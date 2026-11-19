(* strtok definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Program tk_prog = strtok + strspn + cs_prog (strcspn + memset), frame,
   precondition (separator set strlen(sep) >= 2), postcondition, invariant family.
   Full header (SEMANTICS, SPECIFICATION, PROVENANCE, I/O) is in strtok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strtok_armv8 strspn_armv8 strcspn_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.lib Require Import GrokKeep.
From Grok.proofs Require strcspn_defs strspn_defs.
Import ARM8Notations.
Open Scope N.

Definition tk_prog : program :=
  updateall2 (updateall2 strtok_armv8.strtok_armv8 strspn_armv8.strspn_armv8) strcspn_defs.cs_prog.

(* the static "char *p" of strtok.c *)
Definition tk_G : N := 0x1c25e0.

(* strtok's frame after stp x29,x30,[sp,#-64]! / stp x19,x20,[sp,#16] / str x21,[sp,#32] *)
Definition tk_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp ⊖ 64 := x29] [Ⓠ sp ⊖ 56 := raddr] [Ⓠ sp ⊖ 48 := x19] [Ⓠ sp ⊖ 40 := x20] [Ⓠ sp ⊖ 32 := x21].

(* s0 = the s argument; p = the string actually scanned (s0, or the saved static if s0 = NULL). *)
Definition tk_pre (sp mem s0 p c Ks Lc : N) :=
  ((s0 <> 0 /\ p = s0) \/ (s0 = 0 /\ mem Ⓠ[tk_G] = p)) /\ tk_G + 8 + 144 <= sp /\ sp < 2^64 /\
  (p = 0 \/ (nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\ 2 <= Lc /\
             mem Ⓧ[0x19e6b0] = 0 /\ mem Ⓧ[0x19e6c0] = 0 /\
             p + Ks + 145 <= sp /\ c + Lc + 145 <= sp)).

Definition tk_out (sp:N) (s:store) (M:memory) :=
  ∀ a, a < 2^64 -> (a < sp - 144 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = M Ⓑ[a].

Definition tk_post (sp mem raddr p c Ks Lc x19 x20 x21 x29 : N) (s:store) :=
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  ((p = 0 /\ s R_X0 = 0 /\ tk_out sp s mem) \/
   (p <> 0 /\ ∃ K1, K1 <= Ks /\ (∀ i, i < K1 -> strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) /\
     ((K1 = Ks /\ s R_X0 = 0 /\ tk_out sp s (mem [Ⓠ tk_G := 0])) \/
      (K1 < Ks /\ ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K1]) /\ s R_X0 = p + K1 /\
       ∃ K2, K1 + K2 <= Ks /\ (∀ i, i < K2 -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K1 + i])) /\
         ((K1 + K2 = Ks /\ tk_out sp s (mem [Ⓠ tk_G := 0])) \/
          (K1 + K2 < Ks /\ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K1 + K2]) /\
           tk_out sp s (mem [Ⓠ tk_G := p + K1 + K2 + 1] [Ⓑ p + K1 + K2 := 0]))))))).

Section Invariants.
  Variables (sp mem raddr s0 p c Ks Lc x19 x20 x21 x29 M1 K1 : N).
  Definition tk_FR := tk_frame sp mem raddr x19 x20 x21 x29.
  (* strcspn (family 1), entered with memory M1 at s = p + K1; X21 carried *)
  Definition tk_Fcs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    strcspn_defs.invs (sp ⊖ 64) M1 0x15f808 (p + K1) c p (sp ⊖ 64) (Ks - K1) Lc T
      (fun n P => Inv n (P /\ keepl_st ((R_X21, 0x1c2000)::nil) s))
      (fun n P => Post n (P /\ keepl_st ((R_X21, 0x1c2000)::nil) s)) NoInv s a.
  (* strspn (family 0); X19 = p, X20 = c, X21, X29 carried *)
  Definition tk_L := (R_X19, p) :: (R_X20, c) :: (R_X21, 0x1c2000) :: (R_X29, sp ⊖ 64) :: nil.
  Definition tk_Fss T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    strspn_defs.ss_invs (sp ⊖ 64) tk_FR 0x15f7ec p c Ks Lc T
      (fun n P => Inv n (P /\ keepl_st tk_L s)) (fun n P => Post n (P /\ keepl_st tk_L s)) NoInv s a.
  Definition tk_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15f7c4 then
      Inv 2 (s R_X0 = s0 /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29)
    else if a =? 0x15f7e0 then
      Inv 2 (p <> 0 /\ s R_X19 = p /\ s R_X1 = c /\ s R_X21 = 0x1c2000 /\ s R_SP = sp ⊖ 64 /\ s R_X29 = sp ⊖ 64 /\
             s V_MEM64 = tk_FR)
    else if a =? 0x15f834 then Post 2 (tk_post sp mem raddr p c Ks Lc x19 x20 x21 x29 s)
    else if a =? 0x15f2e8 then tk_Fss T Inv Post NoInv s a
    else if a =? 0x15f380 then tk_Fss T Inv Post NoInv s a
    else if a =? 0x15f314 then tk_Fss T Inv Post NoInv s a
    else if a =? 0x15f340 then tk_Fss T Inv Post NoInv s a
    else if a =? 0x15f360 then tk_Fss T Inv Post NoInv s a
    else tk_Fcs T Inv Post NoInv s a.
  Definition tk_exits2 := make_exits 2 tk_prog tk_invs.
  Definition tk_invs2 := make_invs 2 tk_prog tk_invs.
  Definition tk_exits1 := make_exits 1 tk_prog tk_invs.
  Definition tk_invs1 := make_invs 1 tk_prog tk_invs.
  Definition tk_exits0 := make_exits 0 tk_prog tk_invs.
  Definition tk_invs0 := make_invs 0 tk_prog tk_invs.
End Invariants.

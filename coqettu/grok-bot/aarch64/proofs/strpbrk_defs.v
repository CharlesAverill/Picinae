(* strpbrk definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Program pb_prog (strpbrk + strcspn + memset), precondition pb_pre, postcondition
   pb_post and invariant set pb_invs for proofs/strpbrk_proof.v (see the header there
   for semantics, man page, provenance and the full I/O specification).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strpbrk_armv8 strcspn_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require Import strcspn_defs.
Import ARM8Notations.
Open Scope N.

Definition pb_prog : program := updateall2 strpbrk_armv8.strpbrk_armv8 cs_prog.

(* strpbrk's frame after stp x29,x30,[sp,#-32]! / str x19,[sp,#16] *)
Definition pb_frame (sp mem raddr x19 x29 : N) :=
  mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19].

(* Inherits strcspn's restriction strlen(c) >= 2. *)
Definition pb_pre (sp mem p c Ks Lc : N) :=
  nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\ 2 <= Lc /\
  4096 + 112 <= sp /\ sp < 2^64 /\ p + Ks + 113 <= sp /\ c + Lc + 113 <= sp.

Definition pb_post (sp mem raddr p c Ks Lc x19 x29 : N) (s:store) :=
  (∃ K, K <= Ks /\ (∀ i, i < K -> ~ cs_in mem c Lc (mem Ⓑ[p + i])) /\
        ((K = Ks /\ s R_X0 = 0) \/ (K < Ks /\ cs_in mem c Lc (mem Ⓑ[p + K]) /\ s R_X0 = p + K))) /\
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  (∀ a, a < 2^64 -> (a < sp - 112 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]).

Section Invariants.
  Variables (sp mem raddr p c Ks Lc x19 x29 : N).
  Definition pb_F := strcspn_defs.invs (sp ⊖ 32) (pb_frame sp mem raddr x19 x29) 0x15f20c p c p (sp ⊖ 32) Ks Lc.
  Definition pb_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15f1f8 then
      Inv 2 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X29 = x29)
    else if a =? 0x15f224 then Post 2 (pb_post sp mem raddr p c Ks Lc x19 x29 s)
    (* strcspn (family 1) invariants *)
    else pb_F T Inv Post NoInv s a.
  Definition pb_exits2 := make_exits 2 pb_prog pb_invs.
  Definition pb_invs2 := make_invs 2 pb_prog pb_invs.
  Definition pb_exits1 := make_exits 1 pb_prog pb_invs.
  Definition pb_invs1 := make_invs 1 pb_prog pb_invs.
End Invariants.


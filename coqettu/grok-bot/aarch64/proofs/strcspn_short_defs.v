(* strcspn short-set path definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Program css_prog = strcspn + strchrnul + strlen lifts, frame, precondition
   (strlen(c) < 2), postcondition and invariant family for the path
   c[0] = 0 or c[1] = 0  ->  return __strchrnul(s, c[0]) - s.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O spec)
   is in strcspn_short_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strcspn_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr.
From Grok.proofs Require strcspn_defs strchrnul_proof.
Import ARM8Notations.
Open Scope N.

Definition css_prog : program := updateall2 strcspn_armv8.strcspn_armv8 strchrnul_proof.strchrnul_prog.

(* strcspn's frame after stp x29,x30,[sp,#-80]! / str x19,[sp,#16] *)
Definition css_frame (sp mem raddr x19 x29 : N) :=
  mem [Ⓠ sp ⊖ 80 := x29] [Ⓠ sp ⊖ 72 := raddr] [Ⓠ sp ⊖ 64 := x19].

(* Short reject set: Lc = strlen(c) < 2. strchrnul's own 32-byte frame (c[0] = 0
   case) lies at sp-112..sp-81. *)
Definition css_pre (sp mem p c Ks Lc : N) :=
  nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\ Lc < 2 /\
  112 <= sp /\ sp < 2^64 /\ p + Ks + 113 <= sp /\ c + Lc + 113 <= sp.

Definition css_post (sp mem raddr p c x19 x29 Ks Lc : N) (s:store) :=
  (∃ K, K <= Ks /\ s R_X0 = K /\ (∀ i, i < K -> ~ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + i])) /\
        (K = Ks \/ strcspn_defs.cs_in mem c Lc (mem Ⓑ[p + K]))) /\
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  (∀ a, a < 2^64 -> (a < sp - 112 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]).

Section Invariants.
  Variables (sp mem raddr p c x19 x29 Ks Lc : N).
  (* strchrnul/strlen (families 1/0), every invariant strengthened with X19 = p *)
  Definition css_F T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    strchrnul_proof.invs (sp ⊖ 80) (css_frame sp mem raddr x19 x29) 0x15ed1c p (mem Ⓑ[c]) (sp ⊖ 80) T
      (fun n P => Inv n (P /\ s R_X19 = p)) (fun n P => Post n (P /\ s R_X19 = p)) NoInv s a.
  Definition css_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    if a =? 0x15ecf0 then
      Inv 2 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
             s R_X19 = x19 /\ s R_X29 = x29)
    else if a =? 0x15ed28 then Post 2 (css_post sp mem raddr p c x19 x29 Ks Lc s)
    else css_F T Inv Post NoInv s a.
  Definition css_exits2 := make_exits 2 css_prog css_invs.
  Definition css_invs2 := make_invs 2 css_prog css_invs.
  Definition css_exits1 := make_exits 1 css_prog css_invs.
  Definition css_invs1 := make_invs 1 css_prog css_invs.
End Invariants.

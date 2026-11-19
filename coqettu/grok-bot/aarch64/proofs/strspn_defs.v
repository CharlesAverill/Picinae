(* strspn definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Table invariant ss_mem, precondition ss_pre, postcondition ss_post and the
   invariant set for the strspn proof (0x15f2e8 in Ghidra, 0x5f2e8 ELF vaddr).
   Reuses bset / cs_in from strcspn_defs.v.  Full header (SEMANTICS, manual
   SPECIFICATION, PROVENANCE, I/O specification) is in strspn_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strspn_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require Import strcspn_defs.
Import ARM8Notations.
Open Scope N.

(* strspn is a leaf: the 32-byte table is zeroed by copying a 32-byte all-zero
   .rodata constant at 0x19e6b0 (ELF 0x9e6b0) with ldp/stp q30,q31. *)
Definition ss_mem (sp mem c : N) (j:N) (M:memory) :=
  (∀ a, a < 2^64 -> (a < sp - 32 \/ sp <= a) -> M Ⓑ[a] = mem Ⓑ[a]) /\
  (∀ w, w < 4 -> M Ⓠ[sp - 32 + 8 * w] = bset mem c (N.to_nat j) w).

Definition ss_pre (sp mem p c Ks Lc : N) :=
  nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\
  mem Ⓧ[0x19e6b0] = 0 /\ mem Ⓧ[0x19e6c0] = 0 /\
  32 <= sp /\ sp < 2^64 /\ p + Ks + 33 <= sp /\ c + Lc + 33 <= sp.

Definition ss_post (sp mem raddr p c Ks Lc : N) (s:store) :=
  (∃ K, K <= Ks /\ s R_X0 = K /\ (∀ i, i < K -> cs_in mem c Lc (mem Ⓑ[p + i])) /\
        (K = Ks \/ ~ cs_in mem c Lc (mem Ⓑ[p + K]))) /\
  s R_SP = sp /\ s R_X30 = raddr /\
  (∀ a, a < 2^64 -> (a < sp - 32 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]).

Section Invariants.
  Variables (sp mem raddr p c Ks Lc : N).
  Definition ss_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15f2e8 => Inv 0 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f314 => Inv 0 (∃ j, j <= Lc /\ s R_X1 = c + j /\ s R_X5 = sp - 32 /\ s R_X6 = 1 /\ s R_X0 = p /\
                         s R_SP = sp ⊖ 32 /\ s R_X30 = raddr /\ ss_mem sp mem c j (s V_MEM64))
    | 0x15f340 => Inv 0 (∃ k, Lc = 1 /\ k <= Ks /\ s R_X1 = p + k /\ s R_X0 = p /\ s R_X3 = mem Ⓑ[c] /\
                         s R_SP = sp ⊖ 32 /\ s R_X30 = raddr /\ (∀ i, i < k -> mem Ⓑ[p + i] = mem Ⓑ[c]) /\
                         (∀ a, a < 2^64 -> (a < sp - 32 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]))
    | 0x15f360 => Inv 0 (∃ k, k <= Ks /\ s R_X3 = p + k /\ s R_X0 = p /\ s R_SP = sp ⊖ 32 /\ s R_X30 = raddr /\
                         (∀ i, i < k -> cs_in mem c Lc (mem Ⓑ[p + i])) /\ ss_mem sp mem c Lc (s V_MEM64))
    | 0x15f380 => Post 0 (ss_post sp mem raddr p c Ks Lc s)
    | _ => NoInv
    end.
  Definition ss_exits := make_exits 0 strspn_armv8.strspn_armv8 ss_invs.
  Definition ss_invs0 := make_invs 0 strspn_armv8.strspn_armv8 ss_invs.
End Invariants.

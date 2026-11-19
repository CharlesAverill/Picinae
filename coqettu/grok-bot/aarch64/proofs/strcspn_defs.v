(* strcspn definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Program (cs_prog = strcspn + memset lifts), bitset model (bset), memory
   invariant (cs_mem), precondition cs_pre, postcondition cs_post and the
   invariant set for the strcspn proof (0x15ecf0 in Ghidra, 0x5ecf0 ELF vaddr).
   Full header (SEMANTICS, manual SPECIFICATION, PROVENANCE, I/O specification)
   is in strcspn_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strcspn_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require memset_proof.
Import ARM8Notations.
Open Scope N.

Definition cs_prog : program := updateall2 strcspn_armv8.strcspn_armv8 memset_armv8.memset_armv8.

Theorem cs_prog_welltyped: welltyped_prog arm8typctx cs_prog.
Proof.
  intros s a. unfold cs_prog, updateall2, updateall.
  destruct (memset_armv8.memset_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (memset_proof.memset_welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply strcspn_armv8.welltyped.
Qed.

Lemma cs_prog_mono: ∀ prog, strcspn_armv8.strcspn_armv8 ⊆2 prog -> memset_armv8.memset_armv8 ⊆2 prog -> cs_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold cs_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* membership of byte b in the reject set c[0..L) *)
Definition cs_in (mem:memory) (c L b : N) := ∃ i, i < L /\ mem Ⓑ[c + i] = b.

(* the 256-bit table word w (bits 64w..64w+63) after inserting c[0..j) *)
Fixpoint bset (mem:memory) (c:N) (j:nat) (w:N) : N :=
  match j with
  | O => 0
  | S j' => let b := mem Ⓑ[c + N.of_nat j'] in
            if b / 64 =? w then N.lor (bset mem c j' w) (2 ^ (b mod 64)) else bset mem c j' w
  end.

(* caller memory after the prologue and the spill stp x5,x3,[sp,#0x20] *)
Definition cs_frame (sp mem raddr x19 x29 c : N) :=
  mem [Ⓠ sp ⊖ 80 := x29] [Ⓠ sp ⊖ 72 := raddr] [Ⓠ sp ⊖ 64 := x19] [Ⓠ sp ⊖ 48 := sp ⊖ 32] [Ⓠ sp ⊖ 40 := c].

(* memory during the two loops: frame outside the table, table words = bset *)
Definition cs_mem (sp mem raddr x19 x29 c : N) (j:N) (M:memory) :=
  (∀ a, a < 2^64 -> (a < sp - 32 \/ sp <= a) -> M Ⓑ[a] = cs_frame sp mem raddr x19 x29 c Ⓑ[a]) /\
  (∀ w, w < 4 -> M Ⓠ[sp - 32 + 8 * w] = bset mem c (N.to_nat j) w).

(* Restricted to reject sets with at least two bytes (c[0], c[1] nonzero): the
   other path calls strchrnul and is not covered. Ks = strlen(p), Lc = strlen(c). *)
Definition cs_pre (sp mem p c Ks Lc : N) :=
  nilfree mem p Ks /\ mem Ⓑ[p + Ks] = 0 /\ nilfree mem c Lc /\ mem Ⓑ[c + Lc] = 0 /\ 2 <= Lc /\
  4096 + 80 <= sp /\ sp < 2^64 /\ p + Ks + 81 <= sp /\ c + Lc + 81 <= sp.

Definition cs_post (sp mem raddr p c x19 x29 Ks Lc : N) (s:store) :=
  (∃ K, K <= Ks /\ s R_X0 = K /\ (∀ i, i < K -> ~ cs_in mem c Lc (mem Ⓑ[p + i])) /\
        (K = Ks \/ cs_in mem c Lc (mem Ⓑ[p + K]))) /\
  s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  (∀ a, a < 2^64 -> (a < sp - 80 \/ sp <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]).

Section Invariants.
  Variables (sp mem raddr p c x19 x29 Ks Lc : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15ecf0 => Inv 1 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x15ed4c => Inv 1 (∃ j, j <= Lc /\ s R_X0 = 1 /\ s R_X3 = c + j /\ s R_X5 = sp - 32 /\ s R_X19 = p /\
                         s R_SP = sp ⊖ 80 /\ cs_mem sp mem raddr x19 x29 c j (s V_MEM64))
    | 0x15ed78 => Inv 1 (∃ k, k <= Ks /\ s R_X3 = p + k /\ s R_X5 = sp - 32 /\ s R_X19 = p /\ s R_SP = sp ⊖ 80 /\
                         (∀ i, i < k -> ~ cs_in mem c Lc (mem Ⓑ[p + i])) /\
                         cs_mem sp mem raddr x19 x29 c Lc (s V_MEM64))
    | 0x15ed28 => Post 1 (cs_post sp mem raddr p c x19 x29 Ks Lc s)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 cs_prog invs.
  Definition invs0 := make_invs 0 cs_prog invs.
  Definition exits1 := make_exits 1 cs_prog invs.
  Definition invs1 := make_invs 1 cs_prog invs.
End Invariants.

(* l64a -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, loop)

   SEMANTICS
   ---------
   musl's C source is

       static const char digits[] =
           "./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
       char *l64a(long x0)
       {
           static char s[7];
           char *p;
           uint32_t x = x0;
           for (p=s; x; p++, x>>=6)
               *p = digits[x&63];
           *p = 0;
           return s;
       }

   SPECIFICATION
   -------------
   POSIX l64a: converts the low 32 bits of x0 to a radix-64 ASCII string of up
   to 6 characters, least significant digit first, in a static buffer, and
   returns a pointer to it (the empty string for 0).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            l64a at 0x3b14c (ELF vaddr); 0x13b14c in Ghidra (image base 0x100000).
            Static buffer s at Ghidra 0x1c2348 (ELF 0xc2348); digit table at
            Ghidra 0x19dab0 (ELF 0x9dab0), read from memory (not assumed to hold
            the literal above).
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter, options --globalAddressing --typeCheck,
            project aarch64/ghidra2; see ../lifted/l64a_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = x0; X30 = return address; m = memory.  Let x = x0 mod 2^32.
   Output:  If execution reaches the RET (0x13b17c): X0 = s (0x1c2348), and for
            the number of digits i (i <= 6, x >> 6i = 0, x >> 6i' <> 0 for i' < i)
            memory is m with s[i'] := m[digits + ((x >> 6i') mod 64)] for each
            i' < i, then s[i] := 0; nothing else changes.  SP, X30 and the AAPCS64
            callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import l64a_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf2.
Import ARM8Notations.
Open Scope N.

Definition L64S : N := 0x1c2348.
Definition L64D : N := 0x19dab0.

(* Memory after the first i digit stores (the digit table is read from m). *)
Fixpoint l64w (m:memory) (x:N) (i:nat) : memory :=
  match i with
  | O => m
  | S i' => (l64w m x i') [Ⓑ L64S + N.of_nat i' := m Ⓑ[L64D + (x >> (6 * N.of_nat i')) mod 64]]
  end.

Lemma l64w_digit: ∀ m x i w, w < 64 -> (i <= 7)%nat ->
  (l64w m x i) Ⓑ[L64D + w] = m Ⓑ[L64D + w].
Proof.
  intros m x i w W. induction i as [|i IH]; intro I.
  - reflexivity.
  - cbn [l64w]. rewrite getmem_noverlap. apply IH. lia.
    apply noverlap. intros i0 j0 I0 J0.
    assert (E1: i0 = 0) by lia. assert (E2: j0 = 0) by lia. subst i0 j0.
    rewrite !N.add_0_r. unfold L64D, L64S.
    rewrite (N.mod_small (0x19dab0 + w)) by lia.
    rewrite (N.mod_small (0x1c2348 + N.of_nat i)) by lia. lia.
Qed.

Lemma shr_nz_bound: ∀ x k, x < 2^32 -> x >> k <> 0 -> k < 32.
Proof.
  intros x k X H. destruct (N.lt_ge_cases k 32) as [L|G]. exact L.
  exfalso. apply H. rewrite N.shiftr_div_pow2. apply N.div_small.
  eapply N.lt_le_trans. exact X. apply N.pow_le_mono_r; lia.
Qed.

Theorem l64a_nwc: ∀ s2 s1, l64a_armv8 s1 = l64a_armv8 s2.
Proof. reflexivity. Qed.

Theorem l64a_welltyped: welltyped_prog arm8typctx l64a_armv8.
Proof. Picinae_typecheck. Qed.

Theorem l64a_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates l64a_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem l64a_preserves_x30:
  forall_endstates l64a_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr x0 : N).
  Definition l64a_post (s:store) :=
    ∃ i:nat, (i <= 6)%nat /\ (x0 mod 2^32) >> (6 * N.of_nat i) = 0 /\
      (∀ i', (i' < i)%nat -> (x0 mod 2^32) >> (6 * N.of_nat i') <> 0) /\
      s R_X0 = L64S /\
      s V_MEM64 = (l64w mem (x0 mod 2^32) i) [Ⓑ L64S + N.of_nat i := 0] /\
      s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x13b14c => Inv 0 (s R_X0 = x0 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x13b170 => Inv 0 (∃ i:nat, (i <= 6)%nat /\
                     s R_X0 mod 2^32 = (x0 mod 2^32) >> (6 * N.of_nat i) /\
                     (∀ i', (i' < i)%nat -> (x0 mod 2^32) >> (6 * N.of_nat i') <> 0) /\
                     s R_X1 = L64S + N.of_nat i /\ s R_X3 = L64D /\ s R_X4 = 0x1c2000 /\
                     s V_MEM64 = l64w mem (x0 mod 2^32) i /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x13b17c => Post 0 (l64a_post s)
    | _ => NoInv
    end.
  Definition l64a_exits := make_exits 0 l64a_armv8 invs.
  Definition l64a_invs := make_invs 0 l64a_armv8 invs.
End Invariants.

Theorem l64a_partial_correctness:
  ∀ prog s sp mem raddr x0 t xs'
    (PROG: l64a_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x13b14c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = x0),
  satisfies_all prog (l64a_invs sp mem raddr x0) (l64a_exits sp mem raddr x0) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=l64a_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold l64a_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply l64a_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & MEM & SP & X30).
    repeat arm8_step.
    exists 0%nat. splits; try assumption; try reflexivity.
    + lia.
    + rewrite X0. cbn [N.of_nat]. rewrite N.mul_0_r, N.shiftr_0_r. reflexivity.
    + intros i' H. lia.
  - destruct PRE as (i & I6 & XM & NZ & X1 & X3 & X4 & MEM & SP & X30).
    assert (XB: x0 mod 2^32 < 2^32) by (apply N.mod_lt; discriminate).
    repeat arm8_step; rewrite ?N.shiftr_0_r, ?XM in *.
    + apply Bool.negb_true_iff, N.eqb_neq in BC.
      pose proof (shr_nz_bound _ _ XB BC) as B32.
      exists (S i). splits; try assumption; try reflexivity.
      * lia.
      * rewrite N.shiftr_shiftr. f_equal. lia.
      * intros i' H. destruct (Nat.eq_dec i' i) as [->|NE]. exact BC. apply NZ. lia.
      * unfold L64S. rewrite N.mod_small by lia. lia.
      * change (s1 R_X0 mod 64) with (s1 R_X0 mod 2^6).
        rewrite <- (mod_mod_pow2 (s1 R_X0) 6 32) by lia. rewrite XM.
        cbn [l64w]. rewrite l64w_digit. reflexivity.
        apply N.mod_lt. discriminate. lia.
    + apply Bool.negb_false_iff, N.eqb_eq in BC.
      exists i. splits; try assumption; try reflexivity.
Qed.

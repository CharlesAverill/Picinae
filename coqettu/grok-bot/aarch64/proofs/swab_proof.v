(* swab -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/unistd/swab.c:
       void swab(const void *restrict _src, void *restrict _dest, ssize_t n)
       {
           const char *src = _src;
           char *dest = _dest;
           for (; n>1; n-=2) {
               dest[0] = src[1];
               dest[1] = src[0];
               dest += 2;
               src += 2;
           }
       }
   The binary computes end = src + n and loops while (end - src) > 1 as a
   signed 64-bit comparison (cmp x3,#1; b.gt), loading both bytes of a pair
   before storing either.  The signed "gt" flag test is handled by lemma
   gt1_test (lib/GrokSigned.v).

   SPECIFICATION (man 3 swab, Linux man-pages 6.9.1)
   -------------------------------------------------
     SYNOPSIS
            #include <unistd.h>
            void swab(const void from[restrict .n], void to[restrict .n],
                      ssize_t n);

     DESCRIPTION
            The swab() function copies n bytes from the array pointed to by
            from to the array pointed to by to, exchanging adjacent even and
            odd bytes.  This function is used to exchange data between
            machines that have different low/high byte ordering.
            This function does nothing when n is negative.  When n is
            positive and odd, it handles n-1 bytes as above, and does
            something unspecified with the last byte.  (In other words, n
            should be even.)

     RETURN VALUE
            None.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            swab at 0x5f9d8 (ELF vaddr); 0x15f9d8 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/swab_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = from = q, X1 = to = d, X2 = n (ssize_t; toZ 64 n is its
            signed value); X30 = return address raddr; SP = sp; m = memory.
   Output:  If execution reaches the RET (0x15fa00): memory =
            swb m q d (Z.to_nat (toZ 64 n / 2)), i.e. exactly floor(n/2)
            byte pairs swapped when n >= 0 and nothing when n < 0 (an odd
            last byte is left untouched); pair i writes to[2i] := from[2i+1],
            to[2i+1] := from[2i], both read from the memory produced by the
            previous pairs (addresses mod 2^64).  SP, X30 and the AAPCS64
            callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import swab_armv8.
From Grok.lib Require Import GrokCommon GrokSigned.
Import ARM8Notations.
Open Scope N.

Theorem swab_welltyped: welltyped_prog arm8typctx swab_armv8.
Proof. Picinae_typecheck. Qed.

Theorem swab_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates swab_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem swab_preserves_x30:
  forall_endstates swab_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* swb m q d k: memory after k iterations of the swab loop: for i < k,
   dest[2i] := src[2i+1] and dest[2i+1] := src[2i], both bytes of a pair
   read before either is written (as the binary does); addresses are
   taken mod 2^64 by getmem/setmem. *)
Fixpoint swb (m:memory) (q d:N) (k:nat) : memory :=
  match k with
  | O => m
  | S k' => let m' := swb m q d k' in let i := N.of_nat k' in
            m' [Ⓑ d + 2*i := m' Ⓑ[1 + q + 2*i]] [Ⓑ 1 + d + 2*i := m' Ⓑ[q + 2*i]]
  end.

Lemma toZ_sub2k: ∀ n k, n < 2^64 -> (k = 0 \/ Z.le (2 * Z.of_N k) (toZ 64 n)) ->
  toZ 64 (n ⊖ 2*k) = Z.sub (toZ 64 n) (2 * Z.of_N k).
Proof.
  intros n k N K. destruct K as [K|K].
  - subst k. rewrite N.mul_0_r, msub_0_r, N.mod_small by assumption. lia.
  - rewrite toZ64 in K by assumption. destruct (N.ltb_spec n (2^63)); [|lia].
    rewrite msub_small by lia. rewrite !toZ64 by lia.
    destruct (N.ltb_spec n (2^63)), (N.ltb_spec (n - 2*k) (2^63)); lia.
Qed.

Section Invariants.
  Variables (sp mem raddr q d n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15f9d8 => Inv 0 (s R_X0 = q /\ s R_X1 = d /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f9f4 => Inv 0 (∃ k, n < 2^64 /\ (k = 0 \/ Z.le (2 * Z.of_N k) (toZ 64 n)) /\
                         s R_X0 = q ⊕ 2*k /\ s R_X1 = d ⊕ 2*k /\ s R_X2 = q ⊕ n /\
                         s V_MEM64 = swb mem q d (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15fa00 => Post 0 (s V_MEM64 = swb mem q d (Z.to_nat (Z.div (toZ 64 n) 2)) /\
                          s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition swab_exits := make_exits 0 swab_armv8 invs.
  Definition swab_invs := make_invs 0 swab_armv8 invs.
End Invariants.

Theorem swab_partial_correctness:
  ∀ prog s sp mem raddr q d n t xs'
    (PROG: swab_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f9d8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = q) (X1: s R_X1 = d) (X2: s R_X2 = n),
  satisfies_all prog (swab_invs sp mem raddr q d n) (swab_exits sp mem raddr q d n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=swab_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold swab_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply swab_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as Q64. rewrite X0 in Q64. simpl in Q64.
    pose proof (MDL1 R_X1 64 eq_refl) as D64. rewrite X1 in D64. simpl in D64.
    pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
    repeat arm8_step.
    exists 0. repeat split; try assumption; try (left; reflexivity).
    all: try rewrite X1; rewrite N.mul_0_r, N.add_0_r; symmetry; apply N.mod_small; assumption.
  - destruct PRE as (k & N64 & KB & X0 & X1 & X2 & MEM & SP & X30).
    repeat arm8_step.
    all: assert (XB: n ⊖ 2*k < 2^64) by (unfold msub; apply N.mod_upper_bound; discriminate).
    all: pose proof (toZ_sub2k n k N64 KB) as TS.
    + apply (gt1_test _ XB) in BC. rewrite TS in BC.
      assert (E: Z.to_nat (Z.div (toZ 64 n) 2) = N.to_nat k) by (Z.div_mod_to_equations; lia).
      rewrite E. repeat split; assumption.
    + assert (GT: ~ Z.le (toZ 64 (n ⊖ 2*k)) 1) by (rewrite <- (gt1_test _ XB), BC; discriminate).
      rewrite TS in GT. exists (k+1). repeat split.
      all: first
        [ assumption | reflexivity
        | right; lia
        | f_equal; lia
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [swb]; rewrite ?N2Nat.id; reflexivity ].
Qed.

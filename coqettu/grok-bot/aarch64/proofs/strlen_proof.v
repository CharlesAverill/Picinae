(* strlen -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (word-at-a-time)

   SEMANTICS
   ---------
   musl's src/string/strlen.c scans byte-wise until s is 8-byte aligned,
   then a word at a time using the "has zero byte" test
       HASZERO(x) = (x - ONES) & ~x & HIGHS,  ONES = 0x0101..01, HIGHS = 0x8080..80
   and finally byte-wise again from the first word whose test is non-zero:

       for (; (uintptr_t)s % ALIGN; s++) if (!*s) return s-a;
       for (w = s [as a word pointer]; !HASZERO(w[0]); w++);
       s = w [as a byte pointer];
       for (; *s; s++);
       return s-a;

   In the binary X1 is the cursor; the word loop adds X4 = 0xfefefefefefefeff
   (= -ONES), BICs with the word, and TSTs against 0x8080808080808080.
   The aligned 8-byte loads may read bytes past the terminator (in the same
   aligned word); Picinae's memory is total, so no page-fault reasoning is
   involved.  The key lemma (GrokBits.haszero_test_zero) proves the
   direction the loop needs: if HASZERO(x) = 0 then no byte of x is zero.

   SPECIFICATION (man 3 strlen, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <string.h>
            size_t strlen(const char *s);

     DESCRIPTION
            The  strlen() function calculates the length of the string pointed to by
            s, excluding the terminating null byte ('\0').

     RETURN VALUE
            The strlen() function returns the number of bytes in the string pointed
            to by s.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strlen at 0x5efa8 (ELF vaddr); 0x15efa8 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strlen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s; X30 = return address; m = memory on entry.  Nothing is
            assumed about the string (in particular not its length).
   Output:  If execution reaches the RET (0x15f000), there is a k < 2^64 with
            X0 = k, bytes s+0 .. s+k-1 all non-zero and byte s+k zero, i.e.
            X0 is the length of the string (k is unique, strlen_post_unique).
            Memory, SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.  Addresses wrap modulo 2^64.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem strlen_nwc: ∀ s2 s1, strlen_armv8 s1 = strlen_armv8 s2.
Proof. reflexivity. Qed.

Theorem strlen_welltyped: welltyped_prog arm8typctx strlen_armv8.
Proof. Picinae_typecheck. Qed.

Theorem strlen_preserves_memory:
  forall_endstates strlen_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strlen_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates strlen_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem strlen_preserves_x30:
  forall_endstates strlen_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)

Section Invariants.
  Variables (sp mem raddr p : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* entry *)
    | 0x15efa8 => Inv 0 (s R_X0 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* byte loop until 8-aligned: tst x1,#7 *)
    | 0x15efb4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* word loop: ldr x3,[x1] *)
    | 0x15efd8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s R_X4 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* final byte loop: ldrb w2,[x1] *)
    | 0x15eff4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* ret *)
    | 0x15f000 => Post 0 (∃ k, k < 2^64 /\ s R_X0 = k /\ nilfree mem p k /\ mem Ⓑ[p + k] = 0 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition strlen_exits := make_exits 0 strlen_armv8 invs.
  Definition strlen_invs := make_invs 0 strlen_armv8 invs.
End Invariants.


Theorem strlen_partial_correctness:
  ∀ prog s sp mem raddr p t xs'
    (PROG: strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15efa8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p),
  satisfies_all prog (strlen_invs sp mem raddr p) (strlen_exits sp mem raddr p) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strlen_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold strlen_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strlen_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    repeat arm8_step.
    exists 0. repeat split; try assumption.
    all: first [ apply nilfree_0 | rewrite N.add_0_r; symmetry; apply N.mod_small; exact P64 ].
  - (* byte loop until X1 is 8-aligned *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30).
    repeat arm8_step.
    + exists k. repeat split; assumption.
    + apply cbnz32_true in BC0; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC0; [|apply byte_lt32].
      exists k. repeat split; assumption.
  - (* aligned word loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & X4 & MEM & SP & X30).
    repeat arm8_step.
    + exists ((k+8) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le.
      intros i Hi. destruct (N.lt_ge_cases i k). apply NF; assumption.
      pose proof (haszero_test_zero _ (qword_lt64 mem (p+k)) BC (i-k) ltac:(lia)) as H8.
      rewrite byte_of_qword in H8 by lia. replace (p + k + (i - k)) with (p + i) in H8 by lia.
      exact H8.
    + exists k. repeat split; assumption.
  - (* final byte loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30).
    repeat arm8_step.
    + apply cbnz32_true in BC; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC; [|apply byte_lt32].
      exists k. repeat split; assumption.
Qed.

(* The k of the post-condition is the string length: it is unique. *)
Theorem strlen_post_unique:
  ∀ m p k1 k2, nilfree m p k1 -> m Ⓑ[p + k1] = 0 -> nilfree m p k2 -> m Ⓑ[p + k2] = 0 -> k1 = k2.
Proof.
  intros m p k1 k2 NF1 Z1 NF2 Z2.
  destruct (N.lt_trichotomy k1 k2) as [H|[H|H]].
    exfalso. exact (NF2 k1 H Z1).
    exact H.
    exfalso. exact (NF1 k2 H Z2).
Qed.

(* strchrnul -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls strlen)

   SEMANTICS
   ---------
   musl's src/string/strchrnul.c (word-at-a-time):
       c = (unsigned char)c;
       if (!c) return s + strlen(s);
       for (; (uintptr_t)s % ALIGN; s++)
           if (!*s || UC(s[0]) == c) return s;
       k = ONES * c;
       for (w = VP(s); !HASZERO(w[0]) && !HASZERO(w[0]^k); w++);
       s = VP(w);
       for (; *s && UC(s[0]) != c; s++);
       return s;
   (UC = cast to unsigned char, VP = pointer cast; written this way
   so the comment stays well-formed.)  If c mod 256 = 0 the binary saves
   X29/X30 and s in a 32-byte frame below SP and calls strlen (0x15efa8,
   verified in the same file against the same invariant family, as callee
   id 0).  Otherwise: byte loop to 8-byte alignment, aligned quadword loop
   testing haszero(x) | haszero(x ^ c*0x0101..01) (lemma chrnul_test), final
   byte loop.  The quadword loop may read up to 7 bytes past the terminator
   inside the same aligned quadword (as the C code does).
   This file verifies the composition strchrnul + strlen (program
   strchrnul_prog = both lifts) with Picinae's perform_call.

   SPECIFICATION (man 3 strchrnul, Linux man-pages 6.9.1)
   ------------------------------------------------------
     SYNOPSIS
            #define _GNU_SOURCE
            #include <string.h>
            char *strchrnul(const char *s, int c);

     DESCRIPTION
            The strchrnul() function is like strchr() except that if c is not
            found in s, then it returns a pointer to the null byte at the end
            of s, rather than NULL.
            Here "character" means "byte"; these functions do not work with
            wide or multibyte characters.

     RETURN VALUE
            The strchrnul() function returns a pointer to the matched
            character, or a pointer to the null byte at the end of s (i.e.,
            s+strlen(s)) if the character is not found.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strchrnul at 0x5ebf4 (ELF vaddr); 0x15ebf4 in Ghidra (image base 0x100000)
            strlen at 0x5efa8 (ELF vaddr); 0x15efa8 in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strchrnul_armv8.v and
            ../lifted/strlen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s = p, X1 = c (int; only c8 = c mod 256 matters); SP = sp;
            X30 = return address raddr; X29 = x29; m = memory on entry.
   Output:  If execution reaches either RET (0x15ec40, 0x15eca0):
            SP = sp, X30 = raddr, X29 = x29, and (strchrnul_post) either
              - c8 <> 0, memory = m, and strchrnul_spec m p c8 X0; or
              - c8 = 0, memory = frame_mem (m with x29, raddr, p stored at
                sp-32, sp-24, sp-8), and strchrnul_spec frame_mem p 0 X0.
            strchrnul_spec m p c r: there is k < 2^64 such that bytes 0..k-1
            at p are neither 0 nor c, byte k is 0 or c, and r = p + k
            (mod 2^64).  (If the scan wraps around the whole address space k
            restarts at 0.)
            X19..X28 and Z8..Z15 are never written
            (strchrnul_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep.
Import ARM8Notations.
Open Scope N.

Definition strchrnul_prog : program := updateall2 strchrnul_armv8.strchrnul_armv8 strlen_armv8.strlen_armv8.

Lemma strchrnul_prog_contains: strchrnul_armv8.strchrnul_armv8 ⊆2 strchrnul_prog.
Proof.
  intros s a insn SC. unfold strchrnul_prog, updateall2, updateall, strlen_armv8.strlen_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem strchrnul_prog_welltyped: welltyped_prog arm8typctx strchrnul_prog.
Proof.
  intros s a. unfold strchrnul_prog, updateall2, updateall.
  destruct (strlen_armv8.strlen_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (strlen_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply strchrnul_armv8.welltyped.
Qed.

(* The first k bytes at p are neither 0 nor c. *)
Definition scan (m:memory) (p:addr) (c:N) (k:N) :=
  ∀ i, i < k -> m Ⓑ[p + i] ≠ 0 /\ m Ⓑ[p + i] ≠ c.

Lemma scan_0: ∀ m p c, scan m p c 0.
Proof. intros m p c i H. destruct i; discriminate. Qed.

Lemma scan_succ: ∀ m p c k, scan m p c k -> m Ⓑ[p + k] ≠ 0 -> m Ⓑ[p + k] ≠ c ->
  scan m p c (k+1).
Proof.
  intros m p c k W N0 NC i I. destruct (N.lt_ge_cases i k). apply W; assumption.
  replace i with k by lia. split; assumption.
Qed.

Lemma scan_mono: ∀ m p c k k', k' <= k -> scan m p c k -> scan m p c k'.
Proof. intros m p c k k' LE W i I. apply W. lia. Qed.

Lemma scan_nilfree: ∀ m p k, nilfree m p k -> scan m p 0 k.
Proof. intros m p k NF i I. split; apply NF; exact I. Qed.

(* strchrnul result for byte c (< 256). *)
Definition strchrnul_spec (m:memory) (p c r:N) :=
  ∃ k, k < 2^64 /\ scan m p c k /\ (m Ⓑ[p + k] = 0 \/ m Ⓑ[p + k] = c) /\ r = p ⊕ k.


(* Word test of strchrnul: haszero(x) | haszero(x ^ splat c), masked; if it is
   zero, no byte of the quadword is 0 or c. *)
Lemma chrnul_test: ∀ m a c, c < 2^8 ->
  ((m Ⓠ[ a ] ⊖ 72340172838076673
    .& (m Ⓠ[ a ] .^ 18446744073709551615)
    .| (m Ⓠ[ a ] .^ (c * 72340172838076673 .^ 18446744073709551615))
       .& (m Ⓠ[ a ] .^ c * 72340172838076673) ⊖ 72340172838076673)
   .& 9259542123273814144 =? 0) = true ->
  ∀ i, i < 8 -> m Ⓑ[a + i] ≠ 0 /\ m Ⓑ[a + i] ≠ c.
Proof.
  intros m a c C T i I. apply N.eqb_eq in T.
  rewrite N.land_lor_distr_l in T. apply N.lor_eq_0_iff in T. destruct T as [T1 T2].
  split.
  - pose proof (haszero_test_zero _ (qword_lt64 m a) (proj2 (N.eqb_eq _ _) T1) i I) as H.
    rewrite byte_of_qword in H by lia. exact H.
  - rewrite <- N.lxor_assoc, (N.lxor_comm (m Ⓠ[a])) in T2.
    rewrite (N.land_comm ((c * 72340172838076673 .^ m Ⓠ[a]) .^ 18446744073709551615)) in T2.
    exact (hasbyte_test_zero m a c C (proj2 (N.eqb_eq _ _) T2) i I).
Qed.

Ltac post_k k :=
  splits; try assumption; left; splits; [reflexivity | assumption |];
  exists k; splits; [assumption | assumption | | reflexivity];
  first [ left; apply N.eqb_eq; assumption | right; apply N.eqb_eq; assumption ].

Ltac adv1 k :=
  exists ((k+1) mod 2^64);
  splits; first [ assumption | reflexivity | apply mp2_mod_lt | apply ptr_adv
                | (eapply scan_mono; [apply mod64_le | apply scan_succ; [assumption | apply N.eqb_neq; assumption ..]]) ].

Section Invariants.
  Variables (sp mem raddr p c x29 : N).
  Definition c8 := c mod 2^8.
  (* strchrnul's 32-byte frame (c8 = 0 path only): saved X29, X30 and s. *)
  Definition frame_mem := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 8 := p].
  Definition strchrnul_post (s:store) :=
    s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\
    ((s V_MEM64 = mem /\ c8 ≠ 0 /\ strchrnul_spec mem p c8 (s R_X0)) \/
     (s V_MEM64 = frame_mem /\ c8 = 0 /\ strchrnul_spec frame_mem p 0 (s R_X0))).
  Definition FR (s:store) := s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strchrnul (s = p, c = c) *)
    | 0x15ebf4 => Inv 1 (s R_X0 = p /\ s R_X1 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\
                         s R_X30 = raddr /\ s R_X29 = x29)
    (* byte loop until 8-aligned: tst x2,#7 *)
    | 0x15ec00 => Inv 1 (∃ k, k < 2^64 /\ s R_X2 = p ⊕ k /\ s R_X1 = c8 /\ c8 ≠ 0 /\ scan mem p c8 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    (* word loop: ldr x3,[x2] *)
    | 0x15ec58 => Inv 1 (∃ k, k < 2^64 /\ s R_X2 = p ⊕ k /\ s R_X1 = c8 /\ c8 ≠ 0 /\ scan mem p c8 k /\
                         s R_X6 = c8 * 0x0101010101010101 /\ s R_X7 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    (* final byte loop: ldrb w0,[x2] *)
    | 0x15ec8c => Inv 1 (∃ k, k < 2^64 /\ s R_X2 = p ⊕ k /\ s R_X1 = c8 /\ c8 ≠ 0 /\ scan mem p c8 k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x15ec40 => Post 1 (strchrnul_post s)
    | 0x15eca0 => Post 1 (strchrnul_post s)
    (* strlen (s = p) *)
    | 0x15efa8 => Inv 0 (s R_X0 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15efb4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15efd8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s R_X4 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15eff4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = p /\ s R_X1 = p ⊕ k /\ nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15f000 => Post 0 (∃ k, k < 2^64 /\ s R_X0 = k /\ nilfree mem p k /\ mem Ⓑ[p + k] = 0 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strchrnul_prog invs.
  Definition invs0 := make_invs 0 strchrnul_prog invs.
  Definition exits1 := make_exits 1 strchrnul_prog invs.
  Definition invs1 := make_invs 1 strchrnul_prog invs.
End Invariants.

Theorem strlen_correct_in_strchrnul:
  ∀ prog s t xs'
    (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15efa8, s))
    (MDL: models arm8typctx s),
  ∀ c x29,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) c x29)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) c x29)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  clearbody sp mem raddr p.
  eapply satisfies_all_pmono with (p1:=strchrnul_prog).
    unfold strchrnul_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchrnul_prog_welltyped. intro MDL1.
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

Theorem strchrnul_partial_correctness:
  ∀ prog s sp mem raddr p c x29 t xs'
    (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15ebf4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr p c x29) (exits1 sp mem raddr p c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strchrnul_prog).
    unfold strchrnul_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchrnul_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  assert (C8: c8 c < 2^8) by (apply N.mod_lt; discriminate).
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & X1 & MEM & SP & X30 & X29).
    pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64. simpl in P64.
    pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
    pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
    grok_step. grok_step. grok_step.
    + (* c8 = 0: call strlen *)
      apply N.eqb_eq in BC.
      do 4 arm8_step.
      set (s2 := update _ _ _).
      eapply models_after_steps. eassumption. apply strchrnul_prog_welltyped. intro MDL2.
      eapply (perform_call 0). reflexivity.
      intros. eapply strlen_correct_in_strchrnul with (c:=c) (x29:=x29);
        first [ exact strchrnul_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
      reflexivity.
      intros.
      unfold s2 in PRE. psimpl in PRE.
      assert (MDL': models arm8typctx s').
        eapply preservation_exec_prog; try eassumption. apply strchrnul_prog_welltyped.
      set (t' := t2++t0++_::t) in *. clearbody s2 t'.
      clear - PRE MDL' SP64 P64 R64 X2964 BC.
      rename MDL' into MDL. rename s' into s.
      destruct_inv 64 PRE.
      destruct PRE as (k & KLT & R0 & NF & Z & MEM & SP & X30).
      repeat arm8_step.
      splits; try (apply N.mod_small; assumption).
      right. splits. reflexivity. exact BC.
      exists k. splits. exact KLT. apply scan_nilfree; exact NF. left; exact Z. reflexivity.
    + (* c8 <> 0: byte loop with k = 0 *)
      apply N.eqb_neq in BC.
      exists 0. rewrite N.add_0_r, N.mod_small by exact P64.
      splits; first [ reflexivity | assumption | apply scan_0 | lia ].
  - (* byte loop until aligned *)
    destruct PRE as (k & KLT & X2 & X1 & CNZ & SC & MEM & SP & X30 & X29).
    repeat grok_step.
    all: first [ post_k k | adv1 k |
                 (exists k; splits; try assumption; try reflexivity;
                  rewrite N.shiftr_0_r, (N.mod_small (c8 c)), scast_small32 by lia;
                  apply N.mod_small; lia) ].
  - (* word loop *)
    destruct PRE as (k & KLT & X2 & X1 & CNZ & SC & X6 & X7 & MEM & SP & X30 & X29).
    repeat grok_step.
    + exists ((k+8) mod 2^64). splits; try assumption; try reflexivity.
      apply mp2_mod_lt. apply ptr_adv.
      eapply scan_mono. apply mod64_le.
      intros i Hi. destruct (N.lt_ge_cases i k). apply SC; assumption.
      pose proof (chrnul_test _ _ _ C8 BC (i-k) ltac:(lia)) as H8.
      replace (p + k + (i - k)) with (p + i) in H8 by lia. exact H8.
    + exists k. splits; try assumption; try reflexivity.
  - (* final byte loop *)
    destruct PRE as (k & KLT & X2 & X1 & CNZ & SC & MEM & SP & X30 & X29).
    repeat grok_step.
    all: first [ post_k k | adv1 k ].
Qed.

(* Frame: the AAPCS64 callee-saved registers other than X29/X30 are never
   written by strchrnul or strlen. *)
Theorem strchrnul_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates strchrnul_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

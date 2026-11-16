(* strnlen -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls memchr)

   SEMANTICS
   ---------
   musl's src/string/strnlen.c:
       const char *p = memchr(s, 0, n);
       return p ? p-s : n;
   The binary saves X29/X30 and X19/X20 in a 32-byte frame below SP, calls
   memchr (0x15e1ec, verified in the same file against the same invariant
   family, as callee id 0), then computes p - s and selects n if p = NULL.
   This file verifies the composition strnlen + memchr (program
   strnlen_prog = both lifts) with Picinae's perform_call.

   SPECIFICATION (man 3 strnlen, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <string.h>
            size_t strnlen(const char s[.maxlen], size_t maxlen);

     DESCRIPTION
            The strnlen() function returns the number of bytes in the string
            pointed to by s, excluding the terminating null byte ('\0'), but at
            most maxlen.  In doing this, strnlen() looks only at the first
            maxlen characters in the string pointed to by s and never beyond
            s[maxlen-1].

     RETURN VALUE
            The strnlen() function returns strlen(s), if that is less than
            maxlen, or maxlen if there is no null terminating ('\0') among the
            first maxlen characters pointed to by s.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strnlen at 0x5f1c0 (ELF vaddr); 0x15f1c0 in Ghidra (image base 0x100000)
            memchr at 0x5e1ec (ELF vaddr); 0x15e1ec in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strnlen_armv8.v and
            ../lifted/memchr_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s, X1 = maxlen = n; SP = sp; X30 = return address raddr;
            X19, X20, X29 = x19, x20, x29; m = memory on entry.
   Memory:  strnlen stores x29, raddr, x19, x20 at sp-32 .. sp-1 (frame_mem);
            memchr then reads the string from frame_mem, so the spec below is
            stated over frame_mem (it equals m wherever the string does not
            overlap the 32 bytes just below SP).
   Output:  If execution reaches the RET (0x15f1f4): memory = frame_mem,
            SP = sp, X30 = raddr, X19 = x19, X20 = x20, X29 = x29, and
            strnlen_post frame_mem s n X0 holds, i.e. either
              - X0 = n and none of the first n bytes is 0, or
              - there is k < n with bytes 0..k-1 non-zero, byte k zero, and
                X0 = k, or, in the degenerate case s + k = 0 (mod 2^64),
                where memchr's pointer is NULL, X0 = n.
            X21..X28 and Z8..Z15 are never written
            (strnlen_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strnlen_armv8 memchr_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep.
From Grok.proofs Require Import memchr_proof.
Import ARM8Notations.
Open Scope N.

Definition strnlen_prog : program := updateall2 strnlen_armv8.strnlen_armv8 memchr_armv8.memchr_armv8.

Lemma strnlen_prog_contains: strnlen_armv8.strnlen_armv8 ⊆2 strnlen_prog.
Proof.
  intros s a insn SC. unfold strnlen_prog, updateall2, updateall, memchr_armv8.memchr_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem strnlen_prog_welltyped: welltyped_prog arm8typctx strnlen_prog.
Proof.
  intros s a. unfold strnlen_prog, updateall2, updateall.
  destruct (memchr_armv8.memchr_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (memchr_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply strnlen_armv8.welltyped.
Qed.

Lemma msub_add_cancel64: ∀ a x, a < 2^64 -> msub 64 ((a + x) mod 2^64) a = x mod 2^64.
Proof.
  intros a x A. unfold msub. rewrite (N.mod_small a) by exact A.
  rewrite N.Div0.add_mod_idemp_l.
  replace (a + x + (2^64 - a)) with (x + 1 * 2^64) by lia.
  apply N.Div0.mod_add.
Qed.

Section Invariants.
  Variables (sp mem raddr a1 a2 a3 x19 x20 x29 : N).
  (* Memory as seen by memchr and on return: strnlen's 32-byte frame (saved X29, X30,
     X19, X20) is stored just below the caller's SP. *)
  Definition frame_mem := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19] [Ⓠ sp ⊖ 8 := x20].
  Definition strnlen_post (m:memory) (s:N) (n:N) (r:N) :=
    (r = n /\ nomatch m s 0 n) \/
    (∃ k, k < n /\ nomatch m s 0 k /\ m Ⓑ[s + k] = 0 /\ (r = k \/ (s ⊕ k = 0 /\ r = n))).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strnlen *)
    | 0x15f1c0 => Inv 1 (s R_X0 = a1 /\ s R_X1 = a2 /\ s V_MEM64 = mem /\ s R_SP = sp /\
                         s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x15f1f4 => Post 1 (s V_MEM64 = frame_mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29 /\
                         strnlen_post frame_mem a1 a2 (s R_X0))
    (* memchr (p = a1, c = a2, n = a3) *)
    | 0x15e1ec => Inv 0 (s R_X0 = a1 /\ s R_X1 = a2 /\ s R_X2 = a3 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x15e200 => Inv 0 (∃ k, a3 < 2^64 /\ k <= a3 /\ s R_X3 = a1 ⊕ k /\ s R_X2 = a3 - k /\ s R_X1 = c8 a2 /\
                         nomatch mem a1 (c8 a2) k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x15e218 => Inv 0 (∃ k, a3 < 2^64 /\ k < a3 /\ s R_X3 = a1 ⊕ k /\ s R_X2 = a3 - k /\ s R_X1 = c8 a2 /\
                         nomatch mem a1 (c8 a2) k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x15e258 => Inv 0 (∃ k e, a3 < 2^64 /\ k <= e /\ e <= a3 /\ (e - k) mod 8 = 0 /\
                         s R_X3 = a1 ⊕ k /\ s R_X0 = a1 ⊕ e /\ s R_X7 = a1 ⊕ a3 /\
                         s R_X6 = c8 a2 * 0x0101010101010101 /\ s R_X8 = 0xfefefefefefefeff /\
                         s R_X1 = c8 a2 /\ nomatch mem a1 (c8 a2) k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x15e288 => Inv 0 (∃ k, a3 < 2^64 /\ k <= a3 /\ s R_X0 = a1 ⊕ k /\ s R_X2 = a3 - k /\ s R_X1 = c8 a2 /\
                         nomatch mem a1 (c8 a2) k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | 0x15e2a4 => Post 0 (((∃ k, k < a3 /\ s R_X0 = a1 ⊕ k /\ nomatch mem a1 (c8 a2) k /\ mem Ⓑ[a1 + k] = c8 a2) \/
                           (s R_X0 = 0 /\ nomatch mem a1 (c8 a2) a3)) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X29 = x29)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strnlen_prog invs.
  Definition invs0 := make_invs 0 strnlen_prog invs.
  Definition exits1 := make_exits 1 strnlen_prog invs.
  Definition invs1 := make_invs 1 strnlen_prog invs.
End Invariants.

Theorem memchr_correct_in_strnlen:
  ∀ prog s t xs'
    (P1: strnlen_armv8.strnlen_armv8 ⊆2 prog) (P0: memchr_armv8.memchr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e1ec, s))
    (MDL: models arm8typctx s),
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X2) (s R_X19) (s R_X20) (s R_X29))
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X2) (s R_X19) (s R_X20) (s R_X29))
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  set (c := s R_X1). set (n := s R_X2). set (x19 := s R_X19). set (x20 := s R_X20). set (x29 := s R_X29).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  assert (X1: s R_X1 = c) by reflexivity. assert (X2: s R_X2 = n) by reflexivity.
  assert (X19: s R_X19 = x19) by reflexivity. assert (X20: s R_X20 = x20) by reflexivity.
  assert (X29: s R_X29 = x29) by reflexivity.
  clearbody sp mem raddr p c n x19 x20 x29.
  eapply satisfies_all_pmono with (p1:=strnlen_prog).
    unfold strnlen_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 X19 X20 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strnlen_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  assert (C8 := c8_lt c).
  assert (C8' : c8 c mod 2^32 = c8 c) by (apply N.mod_small; change (2^32) with (2^8 * 2^24); lia).
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X19 & X20 & X29).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. pose proof (MDL1 R_X2 64 eq_refl) as N64.
    rewrite X0 in P64. rewrite X2 in N64. simpl in P64, N64.
    repeat arm8_step.
    exists 0. rewrite N.add_0_r, N.sub_0_r, mod_small64 by assumption.
    repeat split; try assumption; try lia. apply nomatch_0.
  - (* 0x15e200: byte-alignment loop *)
    destruct PRE as (k & N64 & KLE & X3 & X2 & X1 & NM & MEM & SP & X30 & X19 & X20 & X29).
    repeat arm8_step; rewrite ?C8' in *; norm_bc.
    all: first [ post_or k
               | exists k; solve [fin_all]
               | exists (k+1); solve [fin_all] ].
  - (* 0x15e218 *)
    destruct PRE as (k & N64 & KLT & X3 & X2 & X1 & NM & MEM & SP & X30 & X19 & X20 & X29).
    pose proof (N.mul_div_le (n - k) 8 ltac:(discriminate)).
    repeat arm8_step; rewrite ?C8' in *; norm_bc.
    all: first [ exists k; solve [fin_all]
               | exists k, (k + 8 * ((n - k) / 8)); solve [fin_all] ].
  - (* 0x15e258: word loop *)
    destruct PRE as (k & e & N64 & KE & EN & KE8 & X3 & X0 & X7 & X6 & X8 & X1 & NM & MEM & SP & X30 & X19 & X20 & X29).
    repeat arm8_step; rewrite ?C8' in *;
    try match goal with H: (msub 64 _ _ .& _ .& _ =? 0) = true |- _ =>
          pose proof (hasbyte_test_zero _ _ _ C8 H) as HB; clear H end;
    norm_bc; rewrite ?mod_small64 in * by lia.
    all: try (match goal with H: ?a <> ?b |- _ => destruct (step8 _ _ KE KE8 H) end).
    all: try (match goal with H: ?a = ?b |- _ => constr_eq a k; constr_eq b e; subst e end).
    all: first [ exists k; solve [fin_all]
               | exists (k+8), e; solve [fin_all] ].
  - (* 0x15e288: tail byte loop *)
    destruct PRE as (k & N64 & KLE & X0 & X2 & X1 & NM & MEM & SP & X30 & X19 & X20 & X29).
    repeat arm8_step; rewrite ?C8' in *; norm_bc.
    all: first [ post_or k
               | exists (k+1); solve [fin_all] ].
Qed.

Theorem strnlen_partial_correctness:
  ∀ prog s sp mem raddr a1 a2 x19 x20 x29 t xs'
    (P1: strnlen_armv8.strnlen_armv8 ⊆2 prog) (P0: memchr_armv8.memchr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f1c0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a1) (X1: s R_X1 = a2)
    (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr a1 a2 0 x19 x20 x29)
                     (exits1 sp mem raddr a1 a2 0 x19 x20 x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strnlen_prog).
    unfold strnlen_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X19 X20 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strnlen_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X19 & X20 & X29).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X1 64 eq_refl) as A264. rewrite X1 in A264. simpl in A264.
  pose proof (MDL1 R_X0 64 eq_refl) as A164. rewrite X0 in A164. simpl in A164.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X19 64 eq_refl) as X1964. rewrite X19 in X1964. simpl in X1964.
  pose proof (MDL1 R_X20 64 eq_refl) as X2064. rewrite X20 in X2064. simpl in X2064.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  do 8 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strnlen_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply memchr_correct_in_strnlen;
    first [ exact strnlen_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strnlen_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 A264 A164 R64 X1964 X2064 X2964.
  rename MDL' into MDL. rename t' into t. rename s' into s.
  destruct_inv 64 PRE.
  destruct PRE as (RES & MEM & SP & X30 & X19 & X20 & X29).
  repeat arm8_step; (splits; [reflexivity|apply N.mod_small; assumption ..|]); unfold strnlen_post, frame_mem.
  all: first [ apply N.eqb_eq in BC | apply N.eqb_neq in BC ];
       destruct RES as [(k & K & R0 & NM & Z) | (R0 & NM)].
  all: try unfold c8 in *; first [
    (left; split; [reflexivity|exact NM]) |
    (right; exists k; splits; try assumption; right; split; [rewrite <- R0; assumption | reflexivity]) |
    (right; exists k; splits; try assumption; left; rewrite R0, msub_add_cancel64, N.mod_small by lia; reflexivity) |
    contradiction ].
Qed.

(* Frame: the remaining AAPCS64 callee-saved registers are never written by
   strnlen or memchr. *)
Theorem strnlen_preserves_other_callee_saved:
  ∀ r, In r (R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates strnlen_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

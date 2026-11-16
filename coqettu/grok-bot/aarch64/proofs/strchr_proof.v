(* strchr -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls strchrnul, which calls strlen)

   SEMANTICS
   ---------
   musl's src/string/strchr.c:
       char *r = __strchrnul(s, c);
       return UC(r[0]) == (unsigned char)c ? r : 0;
   (UC = cast to unsigned char.)  The binary saves X29/X30 and the 32-bit
   c in a 32-byte frame below SP, calls strchrnul (0x15ebf4), which itself
   may call strlen (0x15efa8) when c mod 256 = 0, then compares the byte at
   the result with c mod 256 (ldrb + cmp w2,w1,UXTB).  All three functions
   are verified in one invariant family over the program
   strchr_prog = strchr + strchrnul + strlen lifts (ids 2/1/0,
   strchr_callees.v; composition with Picinae's perform_call).
   NOTE: the original lifter dropped the UXTB truncation in
   `cmp w2,w1,UXTB` (lifter bug 3, fixed in ../lifter, see
   ../lifter/README_GROK.md); the lift used here is the fixed one.

   SPECIFICATION (man 3 strchr, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <string.h>
            char *strchr(const char *s, int c);

     DESCRIPTION
            The strchr() function returns a pointer to the first occurrence
            of the character c in the string s.
            Here "character" means "byte"; these functions do not work with
            wide or multibyte characters.

     RETURN VALUE
            The strchr() function returns a pointer to the matched character
            or NULL if the character is not found.  The terminating null byte
            is considered part of the string, so that if c is specified as
            '\0', these functions return a pointer to the terminator.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strchr at 0x5ebcc (ELF vaddr); 0x15ebcc in Ghidra (image base 0x100000)
            strchrnul at 0x5ebf4; 0x15ebf4 in Ghidra
            strlen at 0x5efa8; 0x15efa8 in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strchr_armv8.v,
            ../lifted/strchrnul_armv8.v and ../lifted/strlen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s = p, X1 = c (int; only c8 = c mod 256 matters); SP = sp;
            X30 = return address raddr; X29 = x29; m = memory on entry.
   Output:  If execution reaches the RET at 0x15ebf0 (strchr_post):
            SP = sp, X30 = raddr, X29 = x29, and the final memory m' is
            chr_frame (m with x29, raddr, c stored at sp-32, sp-24, sp-4
            (32-bit)) or, when c8 = 0, chr_frame extended with strchrnul's
            frame (sp-32, 0x15ebdc, p at sp-64, sp-56, sp-40); and there is r
            with strchrnul_spec m' p c8 r (bytes p..r-1 are neither 0 nor c8,
            byte r is 0 or c8, r = p + k mod 2^64) and
            X0 = (if m'[r] = c8 then r else 0).
            X19..X28 and Z8..Z15 are never written
            (strchr_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strchr_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep.
From Grok.proofs Require Import strchr_callees.
Import ARM8Notations.
Open Scope N.

Lemma msub_msub64: ∀ x a b c, a < 2^64 -> b < 2^64 -> c = a + b -> c < 2^64 ->
  msub 64 (msub 64 x a) b = msub 64 x c.
Proof.
  intros x a b c A B C CL. subst c. unfold msub.
  rewrite (N.mod_small a), (N.mod_small b), (N.mod_small (a+b)) by assumption.
  rewrite N.Div0.add_mod_idemp_l.
  replace (x + (2^64 - a) + (2^64 - b)) with (x + (2^64 - (a+b)) + 1 * 2^64) by lia.
  apply N.Div0.mod_add.
Qed.

Theorem strchr_partial_correctness:
  ∀ prog s sp mem raddr p c x29 t xs'
    (P2: strchr_armv8.strchr_armv8 ⊆2 prog) (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15ebcc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs2 sp mem raddr p c x29) (exits2 sp mem raddr p c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strchr_prog).
    apply strchr_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchr_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64. simpl in P64.
  pose proof (MDL1 R_X1 64 eq_refl) as C64. rewrite X1 in C64. simpl in C64.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  do 4 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strchr_prog_welltyped. intro MDL2.
  eapply (perform_call 1). reflexivity.
  intros. eapply strchrnul_correct_in_strchr with (c:=c) (x29:=sp ⊖ 32);
    first [ exact strchr_prog_contains2 | exact strchr_prog_contains1 | exact strchr_prog_contains0 | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strchr_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 P64 C64 R64 X2964.
  rename MDL' into MDL. rename s' into s.
  destruct_inv 64 PRE.
  all: destruct PRE as (SP & X30 & X29 & [(MEM & CNZ & SPEC) | (MEM & CZ & SPEC)]); [
    repeat arm8_step;
    [> splits; try (apply N.mod_small; assumption) .. ];
    [> eexists _, (s R_X0); splits; [ reflexivity | left; unfold chr_frame; reflexivity | exact SPEC | ] .. ];
    [> unfold c8; rewrite BC; reflexivity .. ]
  | unfold frame_mem, nul_frame in MEM; repeat arm8_step;
    [> splits; try (apply N.mod_small; assumption) .. ];
    [> eexists _, (s R_X0); splits; [ reflexivity | right; unfold chr_frame; reflexivity | | ] .. ];
    [> unfold frame_mem, nul_frame, c8 in *; rewrite ?CZ in *;
       rewrite (msub_msub64 sp 32 32 64), (msub_msub64 sp 32 24 56), (msub_msub64 sp 32 8 40) in SPEC by lia .. ];
    [> first [ exact SPEC | rewrite BC; reflexivity ] .. ] ].
Qed.

(* Frame: the AAPCS64 callee-saved registers other than X29/X30 are never
   written by strchr, strchrnul or strlen. *)
Theorem strchr_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates strchr_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

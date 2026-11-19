(* explicit_bzero -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls memset), n < 160 (full memset)

   SEMANTICS
   ---------
   musl's src/string/explicit_bzero.c:
       void explicit_bzero(void *d, size_t n)
       { d = memset(d, 0, n); __asm__ __volatile__ ("" : : "r"(d) : "memory"); }
   compiled to
       stp x29,x30,[sp,#-16]!; mov x2,x1; mov w1,#0; mov x29,sp;
       bl memset; ldp x29,x30,[sp],#16; ret.
   This file verifies the composition explicit_bzero + memset (program
   eb_prog = both lifts) with Picinae's perform_call; memset is the callee
   (id 0), re-verified inside the composed program with the same proof as
   proofs/memset_full_proof.v (memset_full_correct_in_explicit_bzero).
   This file supersedes the n <= 96 limit of explicit_bzero_proof.v (kept
   unchanged; its eb_prog, frame_mem and eb_post are reused here).

   SPECIFICATION (man 3 explicit_bzero, Linux man-pages 6.9.1)
   -----------------------------------------------------------
     SYNOPSIS
            #include <string.h>
            void explicit_bzero(void s[.n], size_t n);
     DESCRIPTION
            The bzero() function erases the data in the n bytes of the memory
            starting at the location pointed to by s, by writing zeros (bytes
            containing NUL) to that area.
            The explicit_bzero() function performs the same task as bzero().
            It differs from bzero() in that it guarantees that compiler
            optimizations will not remove the erase operation if the compiler
            deduces that the operation is "unnecessary".
     RETURN VALUE
            None.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            explicit_bzero at 0x5e108 (ELF vaddr); 0x15e108 in Ghidra (image base 0x100000)
            memset at 0x18400 (ELF vaddr); 0x118400 in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/explicit_bzero_armv8.v and ../lifted/memset_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = d, X1 = n; SP = sp; X30 = raddr; X29 = x29; memory m.
   Precondition: n < 160, 4096 <= d, d + n < 2^64.  (A zero fill of
            n >= 160 bytes takes memset's DC ZVA path, which the lifter
            models as Nop, so it cannot be verified soundly from this lift.)
   Output:  If the RET (0x15e120) is reached (eb_post): X0 = d, SP = sp,
            the n bytes at d..d+n-1 are 0, every other byte equals
            frame_mem (m with x29/raddr stored at sp-16..sp-1, the saved
            frame), and X29 / X30 are the 8-byte values read back from
            sp-16 / sp-8 of the final memory; these equal x29 / raddr
            whenever d..d+n-1 does not overlap the 16 bytes below sp.
            X19..X28 and Z8..Z15 are never written
            (explicit_bzero_proof.explicit_bzero_preserves_other_callee_saved,
            same program eb_prog).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require explicit_bzero_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
From Grok.proofs Require Import memset_proof memset_full_defs memset_full_proof explicit_bzero_proof explicit_bzero_full_defs.
Import ARM8Notations.
Open Scope N.

Theorem memset_full_correct_in_explicit_bzero:
  ∀ prog s sp mem raddr d n x29 c t xs'
    (P1: explicit_bzero_armv8.explicit_bzero_armv8 ⊆2 prog) (P0: memset_armv8.memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118400, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = d) (X1: s R_X1 = c) (X2: s R_X2 = n) (MEM: s V_MEM64 = frame_mem sp mem raddr x29)
    (SP: s R_SP = sp ⊖ 16) (X30: s R_X30 = 0x15e11c)
    (SIDE: mf_side c n) (LOW: 4096 <= d) (NW: d + n < 2^64),
  satisfies_all prog (ebf_invs0 sp mem raddr d n x29 c) (ebf_exits0 sp mem raddr d n x29 c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=eb_prog).
    unfold eb_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold ebf_invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL X0 X1 X2 MEM SP X30 SIDE LOW NW START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply eb_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold mf_loop, mfb, fbase in *; repeat match goal with H: _ /\ _ |- _ => destruct H end.
  all: try match goal with H: False |- _ => destruct H end.
  1: (arm8_step; splits; try reflexivity; try assumption; match goal with |- context[?s R_Z0] => solve_splat c (s R_Z0) end).
  (* 0x118404 *)
  (* old small-path cases 0x118404 .. 0x118470 *)
  2-6: (repeat grok_step; try (remember (frame_mem sp mem raddr x29) as fm; clear Heqfm); memset_prep;
    try (unfold memset_post); unfold mfb, fbase; splits; try reflexivity; try assumption; try lia;
    try (intros i I; memset_addr; repeat rd1; first [match goal with ZS: splat_bytes _ _ _ |- _ => memset_byte ZS end | lia | reflexivity]);
    try (intros x A O; memset_addr; repeat rd1; first [reflexivity | lia]);
    try (intros; match goal with H: _ V_MEM64 = _ |- _ => rewrite H end; reflexivity)).
  (* 0x118404 *)
  1: (repeat grok_step; try (remember (frame_mem sp mem raddr x29) as fm; clear Heqfm); memset_prep; unfold mfb, fbase; splits; try reflexivity; try assumption; memset_addr; try lia).
  (* 0x118480 *)
  1: { repeat grok_step. all: try (remember (frame_mem sp mem raddr x29) as fm; clear Heqfm). all: memset_prep.
       all: try (exfalso; unfold mf_side in *; lia).
       all: rewrite !land_m16 by lia.
       all: assert (DM: d mod 16 < 16) by (apply N.mod_lt; discriminate).
       all: assert (DL: d mod 16 <= d) by (apply N.Div0.mod_le).
       all: unfold fbase; splits; try reflexivity; try assumption; memset_addr; try lia.
       all: first
         [ intros i I1 I2; rd1; [ mf_byte | exfalso; lia | exfalso; lia ]
         | intros x A O; rd1; [ exfalso; lia | reflexivity | reflexivity ] ]. }
  (* 0x1184e8 *)
  1: { repeat grok_step. all: try (remember (frame_mem sp mem raddr x29) as fm; clear Heqfm). all: memset_prep.
       all: repeat match goal with H: MemAcc _ _ _ _ _ |- _ => clear H end.
       all: unfold fbase; splits; try reflexivity; try assumption; memset_addr; try lia.
       all: match goal with
         | |- ∀ i, i < _ -> _ => intros i I; repeat rd2; first [ mf_byte | mf_ih ]
         | |- ∀ i, _ <= i -> _ => intros i I1 I2; repeat rd2; first [ mf_byte | mf_ih ]
         | |- ∀ a, a < _ -> _ => intros x A O; repeat rd2; first [ exfalso; lia | mf_out ]
         end. }
Qed.

Theorem explicit_bzero_full_partial_correctness:
  ∀ prog s sp mem raddr d n x29 t xs'
    (P1: explicit_bzero_armv8.explicit_bzero_armv8 ⊆2 prog) (P0: memset_armv8.memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e108, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = n) (X29: s R_X29 = x29)
    (SMALL: n < 160) (LOW: 4096 <= d) (NW: d + n < 2^64),
  satisfies_all prog (ebf_invs1 sp mem raddr d n x29 0) (ebf_exits1 sp mem raddr d n x29 0) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=eb_prog).
    unfold eb_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold ebf_invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 SMALL LOW NW START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply eb_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & SMALL & LOW & NW).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  do 5 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply eb_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply memset_full_correct_in_explicit_bzero;
    first [ exact eb_prog_contains | apply subset_updateall2 | eassumption | reflexivity | (unfold mf_side; right; right; assumption) ].
  assert (S2X2: s2 R_X2 = n) by (unfold s2; reflexivity).
  rewrite S2X2. reflexivity.
  assert (S2X2: s2 R_X2 = n) by (unfold s2; reflexivity). rewrite S2X2.
  assert (S2X1: s2 R_X1 = 0) by (unfold s2; reflexivity). rewrite S2X1.
  intros.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply eb_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 R64 X2964 SMALL LOW NW.
  rename MDL' into MDL. rename t' into t. rename s' into s.
  destruct_inv 64 PRE.
  all: unfold memset_post in PRE; destruct PRE as (RX0 & RSP & RX30 & BYTES & OTHER).
  all: repeat arm8_step.
  all: splits; try assumption; try reflexivity; try (apply N.mod_small; assumption).
  all: intros i I; rewrite BYTES by exact I; reflexivity.
Qed.


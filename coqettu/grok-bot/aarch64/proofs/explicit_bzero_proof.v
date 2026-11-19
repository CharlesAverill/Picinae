(* explicit_bzero -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls memset)

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
   proofs/memset_proof.v (memset_correct_in_explicit_bzero).

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
   Precondition (as for memset_proof.v): n <= 96, 4096 <= d, d + n < 2^64.
            (For n > 96 memset takes the DC ZVA path, which is not covered.)
   Output:  If the RET (0x15e120) is reached (eb_post): X0 = d, SP = sp,
            the n bytes at d..d+n-1 are 0, every other byte equals
            frame_mem (m with x29/raddr stored at sp-16..sp-1, the saved
            frame), and X29 / X30 are the 8-byte values read back from
            sp-16 / sp-8 of the final memory; these equal x29 / raddr
            whenever d..d+n-1 does not overlap the 16 bytes below sp.
            X19..X28 and Z8..Z15 are never written
            (explicit_bzero_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require explicit_bzero_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
From Grok.proofs Require Import memset_proof.
Import ARM8Notations.
Open Scope N.

Definition eb_prog : program := updateall2 explicit_bzero_armv8.explicit_bzero_armv8 memset_armv8.memset_armv8.

Lemma eb_prog_contains: explicit_bzero_armv8.explicit_bzero_armv8 ⊆2 eb_prog.
Proof.
  intros s a insn SC. unfold eb_prog, updateall2, updateall, memset_armv8.memset_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem eb_prog_welltyped: welltyped_prog arm8typctx eb_prog.
Proof.
  intros s a. unfold eb_prog, updateall2, updateall.
  destruct (memset_armv8.memset_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (memset_proof.memset_welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply explicit_bzero_armv8.welltyped.
Qed.

Section Invariants.
  Variables (sp mem raddr d n x29 c : N).
  Definition frame_mem := mem [Ⓠ sp ⊖ 16 := x29] [Ⓠ sp ⊖ 8 := raddr].
  Definition eb_post (s:store) :=
    s R_X0 = d /\ s R_SP = sp /\
    (∀ i, i < n -> s V_MEM64 Ⓑ[d + i] = 0) /\
    (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> s V_MEM64 Ⓑ[a] = frame_mem Ⓑ[a]) /\
    s R_X29 = s V_MEM64 Ⓠ[sp ⊖ 16] /\ s R_X30 = s V_MEM64 Ⓠ[sp ⊖ 8].
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e108 => Inv 1 (s R_X0 = d /\ s R_X1 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\
                         n <= 96 /\ 4096 <= d /\ d + n < 2^64)
    | 0x15e120 => Post 1 (eb_post s)
    | _ => memset_proof.invs frame_mem d c n (sp ⊖ 16) 0x15e11c T Inv Post NoInv s a
    end.
  Definition exits0 := make_exits 0 eb_prog invs.
  Definition invs0 := make_invs 0 eb_prog invs.
  Definition exits1 := make_exits 1 eb_prog invs.
  Definition invs1 := make_invs 1 eb_prog invs.
End Invariants.

Theorem memset_correct_in_explicit_bzero:
  ∀ prog s sp mem raddr d n x29 c t xs'
    (P1: explicit_bzero_armv8.explicit_bzero_armv8 ⊆2 prog) (P0: memset_armv8.memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118400, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = d) (X1: s R_X1 = c) (X2: s R_X2 = n) (MEM: s V_MEM64 = frame_mem sp mem raddr x29)
    (SP: s R_SP = sp ⊖ 16) (X30: s R_X30 = 0x15e11c)
    (SMALL: n <= 96) (LOW: 4096 <= d) (NW: d + n < 2^64),
  satisfies_all prog (invs0 sp mem raddr d n x29 c) (exits0 sp mem raddr d n x29 c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=eb_prog).
    unfold eb_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL X0 X1 X2 MEM SP X30 SMALL LOW NW START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply eb_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold mbase in *; repeat match goal with H: _ /\ _ |- _ => destruct H end.
  all: try match goal with H: False |- _ => destruct H end.
  1: (arm8_step; splits; try assumption; match goal with |- context[?s R_Z0] => solve_splat c (s R_Z0) end).
  all: repeat grok_step.
  all: try (remember (frame_mem sp mem raddr x29) as fm; clear Heqfm).
  all: memset_prep.
  all: try (unfold memset_post); unfold mbase; splits; try reflexivity; try assumption; try lia.
  all: try (intros i I; memset_addr; repeat rd1; first [match goal with ZS: splat_bytes _ _ _ |- _ => memset_byte ZS end | lia | reflexivity]).
  all: try (intros x A O; memset_addr; repeat rd1; first [reflexivity | lia]).
  all: intros; match goal with H: _ V_MEM64 = _ |- _ => rewrite H end; reflexivity.
Qed.

Theorem explicit_bzero_partial_correctness:
  ∀ prog s sp mem raddr d n x29 t xs'
    (P1: explicit_bzero_armv8.explicit_bzero_armv8 ⊆2 prog) (P0: memset_armv8.memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e108, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = n) (X29: s R_X29 = x29)
    (SMALL: n <= 96) (LOW: 4096 <= d) (NW: d + n < 2^64),
  satisfies_all prog (invs1 sp mem raddr d n x29 0) (exits1 sp mem raddr d n x29 0) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=eb_prog).
    unfold eb_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
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
  intros. eapply memset_correct_in_explicit_bzero;
    first [ exact eb_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
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

(* Frame: the remaining AAPCS64 callee-saved registers are never written by
   explicit_bzero or memset. *)
Theorem explicit_bzero_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates eb_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.


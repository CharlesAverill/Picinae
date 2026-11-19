(* iswspace -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls wcschr)

   SEMANTICS
   ---------
   musl's src/ctype/iswspace.c:
       static const wchar_t spaces[] = {
           L" ", L"\t", L"\n", L"\r", 11, 12, 0x0085,
           0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005,
           0x2006, 0x2008, 0x2009, 0x200a,
           0x2028, 0x2029, 0x205f, 0x3000, 0 };
       int iswspace(wint_t wc) { return wc && wcschr(spaces, wc); }
   (the first four entries are the characters space, tab, newline and
   carriage return), compiled to
       cbnz w0, L; ret;
       L: stp x29,x30,[sp,#-16]!; mov w1,w0; adrp x0,0x74000; mov x29,sp;
          add x0,x0,#0xe0; bl wcschr; cmp x0,#0; cset w0,ne;
          ldp x29,x30,[sp],#16; ret.
   The table spaces[] is in .rodata at ELF 0x740e0 (Ghidra 0x1740e0); its
   bytes in the binary start 20 00 00 00 09 00 00 00 0a 00 00 00 0d 00 00 00.
   This file verifies the composition iswspace + wcschr (program
   iswspace_prog = both lifts) with Picinae's perform_call; wcschr is the
   callee (id 0) and is re-verified inside the composed program
   (wcschr_correct_in_iswspace).  Because wc mod 2^32 <> 0 on the call path,
   wcschr's c = 0 branch (which would call wcslen) is shown unreachable.

   SPECIFICATION (man 3 iswspace, Linux man-pages 6.9.1)
   -----------------------------------------------------
     SYNOPSIS
            #include <wctype.h>
            int iswspace(wint_t wc);
     DESCRIPTION
            The iswspace() function is the wide-character equivalent of the
            isspace(3) function.  It tests whether wc is a wide character
            belonging to the wide-character class "space".
     RETURN VALUE
            The iswspace() function returns nonzero if wc is a wide character
            belonging to the wide-character class "space".  Otherwise, it
            returns zero.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            iswspace at 0x1f210 (ELF vaddr); 0x11f210 in Ghidra (image base 0x100000)
            wcschr at 0x5fab4 (ELF vaddr); 0x15fab4 in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/iswspace_armv8.v and ../lifted/wcschr_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = wc (X0 = c; wc = c mod 2^32); SP = sp; X30 = raddr;
            X29 = x29; memory m.
   Output:  If execution reaches a RET:
            - 0x11f214 (wc = 0): X0 = c (so W0 = 0), memory = m;
            - 0x11f23c (wc <> 0): there is r with
              wcschr_spec frame_mem 0x1740e0 wc r (proofs/wcschr_proof.v: r
              points at the first wide char equal to wc in the 0-terminated
              table, or r = 0 if the terminator comes first), and
              X0 = 0 if r = 0, else 1; memory = frame_mem (m with x29/raddr
              stored at sp-16..sp-1; equal to m at the table whenever the
              table does not overlap the 16 bytes below sp).
            On both paths SP = sp, X30 = raddr, X29 = x29.
            X19..X28 and Z8..Z15 are never written
            (iswspace_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require iswspace_armv8 wcschr_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
From Grok.proofs Require Import wcslen_proof.
From Grok.proofs Require wcschr_proof.
Import wcschr_proof (wscan, wscan_0, wscan_succ, wcschr_spec).
Import ARM8Notations.
Open Scope N.

Definition iswspace_prog : program := updateall2 iswspace_armv8.iswspace_armv8 wcschr_armv8.wcschr_armv8.

Lemma iswspace_prog_contains: iswspace_armv8.iswspace_armv8 ⊆2 iswspace_prog.
Proof.
  intros s a insn SC. unfold iswspace_prog, updateall2, updateall, wcschr_armv8.wcschr_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem iswspace_prog_welltyped: welltyped_prog arm8typctx iswspace_prog.
Proof.
  intros s a. unfold iswspace_prog, updateall2, updateall.
  destruct (wcschr_armv8.wcschr_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (wcschr_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply iswspace_armv8.welltyped.
Qed.

Section Invariants.
  Variables (sp mem raddr c x29 : N).
  Definition frame_mem := mem [Ⓠ sp ⊖ 16 := x29] [Ⓠ sp ⊖ 8 := raddr].
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* iswspace *)
    | 0x11f210 => Inv 1 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x11f214 => Post 1 (s R_X0 = c /\ c mod 2^32 = 0 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x11f23c => Post 1 (∃ r, wcschr_spec frame_mem 0x1740e0 (c mod 2^32) r /\
                          s R_X0 = (if r =? 0 then 0 else 1) /\ c mod 2^32 ≠ 0 /\
                          s V_MEM64 = frame_mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    (* wcschr (s = 0x1740e0, the space table; c <> 0) *)
    | 0x15fab4 => Inv 0 (s R_X0 = 0x1740e0 /\ s R_X1 = c mod 2^32 /\ c mod 2^32 ≠ 0 /\ s V_MEM64 = frame_mem /\
                         s R_SP = sp ⊖ 16 /\ s R_X30 = 0x11f230 /\ s R_X29 = sp ⊖ 16)
    | 0x15fae0 => Inv 0 (∃ k, k < 2^62 /\ s R_X2 = 0x1740e0 ⊕ 4*k /\ s R_X1 = c mod 2^32 /\ c mod 2^32 ≠ 0 /\
                         wscan frame_mem 0x1740e0 (c mod 2^32) k /\
                         s V_MEM64 = frame_mem /\ s R_SP = sp ⊖ 16 /\ s R_X30 = 0x11f230 /\ s R_X29 = sp ⊖ 16)
    | 0x15faf4 | 0x15fafc => Post 0 (wcschr_spec frame_mem 0x1740e0 (c mod 2^32) (s R_X0) /\ s V_MEM64 = frame_mem /\
                         s R_SP = sp ⊖ 16 /\ s R_X30 = 0x11f230 /\ s R_X29 = sp ⊖ 16)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 iswspace_prog invs.
  Definition invs0 := make_invs 0 iswspace_prog invs.
  Definition exits1 := make_exits 1 iswspace_prog invs.
  Definition invs1 := make_invs 1 iswspace_prog invs.
End Invariants.

Theorem wcschr_correct_in_iswspace:
  ∀ prog s sp mem raddr c x29 t xs'
    (P1: iswspace_armv8.iswspace_armv8 ⊆2 prog) (P0: wcschr_armv8.wcschr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fab4, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = 0x1740e0) (X1: s R_X1 = c mod 2^32) (CNZ: c mod 2^32 ≠ 0)
    (MEM: s V_MEM64 = frame_mem sp mem raddr x29) (SP: s R_SP = sp ⊖ 16)
    (X30: s R_X30 = 0x11f230) (X29: s R_X29 = sp ⊖ 16),
  satisfies_all prog (invs0 sp mem raddr c x29) (exits0 sp mem raddr c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=iswspace_prog).
    unfold iswspace_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 CNZ X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply iswspace_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & CNZ & MEM & SP & X30 & X29).
    arm8_step. arm8_step; rewrite ?N.shiftr_0_r, ?N.mod_mod in BC by discriminate.
    + exists 0. splits; first [ reflexivity | assumption | apply wscan_0 | lia ].
    + apply Bool.negb_false_iff, N.eqb_eq in BC. contradiction.
  - destruct PRE as (k & KLT & X2 & X1 & CNZ & WS & MEM & SP & X30 & X29).
    repeat arm8_step.
    all: remember (frame_mem sp mem raddr x29) as fm; clear Heqfm.
    + apply N.eqb_eq in BC. splits; try assumption; try reflexivity.
      right. exists k. splits; try assumption. reflexivity.
    + apply N.eqb_eq in BC0. splits; try assumption; try reflexivity.
      left. exists k. splits; try assumption. reflexivity.
    + apply N.eqb_neq in BC, BC0.
      destruct (N.lt_ge_cases (k+1) (2^62)) as [LT|GE].
      * exists (k+1). splits; try assumption; try reflexivity.
        f_equal. lia.
        apply wscan_succ; assumption.
      * exists 0. splits; try assumption; try reflexivity.
        assert (E: 1523940 + 4*k = 1523936 + 2^64) by lia. rewrite E, add_wrap_full. f_equal; lia.
        apply wscan_0.
Qed.

Theorem iswspace_partial_correctness:
  ∀ prog s sp mem raddr c x29 t xs'
    (P1: iswspace_armv8.iswspace_armv8 ⊆2 prog) (P0: wcschr_armv8.wcschr_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11f210, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr c x29) (exits1 sp mem raddr c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=iswspace_prog).
    unfold iswspace_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply iswspace_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30 & X29).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  arm8_step.
  all: rewrite N.shiftr_0_r in BC.
  2: { apply Bool.negb_false_iff, N.eqb_eq in BC. splits; try reflexivity; assumption. }
  apply Bool.negb_true_iff, N.eqb_neq in BC.
  do 6 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply iswspace_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply wcschr_correct_in_iswspace;
    first [ exact iswspace_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
  reflexivity.
  intros.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply iswspace_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' BC SP64 R64 X2964.
  rename MDL' into MDL. rename t' into t. rename s' into s.
  destruct_inv 64 PRE.
  all: destruct PRE as (SPEC & MEM & SP & X30 & X29).
  all: pose proof (MDL R_X0 64 eq_refl) as R064; simpl in R064.
  all: repeat arm8_step.
  all: exists (s R_X0); splits; try assumption; try (apply N.mod_small; assumption).
  all: unfold frame_mem; psimpl; try reflexivity; try (apply N.mod_small; assumption).
Qed.

(* Frame: the remaining AAPCS64 callee-saved registers are never written by
   iswspace or wcschr. *)
Theorem iswspace_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates iswspace_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

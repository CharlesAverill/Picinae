(* ispunct -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls isalnum)

   SEMANTICS
   ---------
   musl's src/ctype/ispunct.c:
       int ispunct(int c) { return isgraph(c) && !isalnum(c); }
   isgraph is inlined as (unsigned)c-0x21 < 0x5e, so the binary is
       sub w1,w0,#0x21; cmp w1,#0x5d; b.ls L; mov w0,#0; ret;
       L: stp x29,x30,[sp,#-16]!; mov x29,sp; bl isalnum;
          cmp w0,#0; cset w0,eq; ldp x29,x30,[sp],#16; ret.
   This file verifies the composition ispunct + isalnum (program
   ispunct_prog = both lifts) with Picinae's perform_call; isalnum is the
   callee (id 0) and is re-verified inside the composed program
   (isalnum_correct_in_ispunct).

   SPECIFICATION (man 3 ispunct, Linux man-pages 6.9.1, C/POSIX locale)
   -------------------------------------------------------------------
     SYNOPSIS
            #include <ctype.h>
            int ispunct(int c);
     DESCRIPTION
            ispunct()
                   checks for any printable character which is not a space
                   or an alphanumeric character.
     RETURN VALUE
            The values returned are nonzero if the character c falls into
            the tested class, and zero if not.
   (musl supports only the C/POSIX ctype classes, i.e. ASCII.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            ispunct at 0x1eeb4 (ELF vaddr); 0x11eeb4 in Ghidra (image base 0x100000)
            isalnum at 0x1edec (ELF vaddr); 0x11edec in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/ispunct_armv8.v and
            ../lifted/isalnum_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = c (X0 = c; only c mod 2^32 is used); SP = sp; X30 = raddr;
            X29 = x29; memory m.
   Output:  If execution reaches a RET:
            - 0x11eec4 (c mod 2^32 - 33, mod 2^32, is above 93, i.e. c is not
              a graphic ASCII character): X0 = 0, memory = m;
            - 0x11eee0 (graphic ASCII c, 0x21..0x7e): X0 = 1 if
              isalnum_spec c = 0 (c is not a letter or digit), else X0 = 0;
              memory = frame_mem (m with x29/raddr stored at sp-16..sp-1).
            On both paths SP = sp, X30 = raddr, X29 = x29.  Combined, X0 = 1
            exactly for the ASCII punctuation characters; EOF (-1) gives 0.
            X19..X28 and Z8..Z15 are never written
            (ispunct_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require ispunct_armv8 isalnum_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCtype GrokCtype2 GrokRange.
From Grok.proofs Require Import isalnum_proof.
Import ARM8Notations.
Open Scope N.

Definition ispunct_prog : program := updateall2 ispunct_armv8.ispunct_armv8 isalnum_armv8.isalnum_armv8.

Lemma ispunct_prog_contains: ispunct_armv8.ispunct_armv8 ⊆2 ispunct_prog.
Proof.
  intros s a insn SC. unfold ispunct_prog, updateall2, updateall, isalnum_armv8.isalnum_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem ispunct_prog_welltyped: welltyped_prog arm8typctx ispunct_prog.
Proof.
  intros s a. unfold ispunct_prog, updateall2, updateall.
  destruct (isalnum_armv8.isalnum_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (isalnum_armv8.welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply ispunct_armv8.welltyped.
Qed.

Section Invariants.
  Variables (sp mem raddr c x29 : N).
  Definition frame_mem := mem [Ⓠ sp ⊖ 16 := x29] [Ⓠ sp ⊖ 8 := raddr].
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* ispunct *)
    | 0x11eeb4 => Inv 1 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x11eec4 => Post 1 (s R_X0 = 0 /\ msub 32 c 33 > 93 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x11eee0 => Post 1 (s R_X0 = (if isalnum_spec c =? 0 then 1 else 0) /\ msub 32 c 33 <= 93 /\
                          s V_MEM64 = frame_mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    (* isalnum, called with the frame pushed *)
    | 0x11edec => Inv 0 (s R_X0 = c /\ s V_MEM64 = frame_mem /\ s R_SP = sp ⊖ 16 /\ s R_X30 = 0x11eed4 /\ s R_X29 = sp ⊖ 16)
    | 0x11ee08 => Post 0 (s R_X0 = isalnum_spec c /\ s V_MEM64 = frame_mem /\ s R_SP = sp ⊖ 16 /\ s R_X30 = 0x11eed4 /\ s R_X29 = sp ⊖ 16)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 ispunct_prog invs.
  Definition invs0 := make_invs 0 ispunct_prog invs.
  Definition exits1 := make_exits 1 ispunct_prog invs.
  Definition invs1 := make_invs 1 ispunct_prog invs.
End Invariants.

Theorem isalnum_correct_in_ispunct:
  ∀ prog s sp mem raddr c x29 t xs'
    (P1: ispunct_armv8.ispunct_armv8 ⊆2 prog) (P0: isalnum_armv8.isalnum_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11edec, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = c) (MEM: s V_MEM64 = frame_mem sp mem raddr x29) (SP: s R_SP = sp ⊖ 16)
    (X30: s R_X30 = 0x11eed4) (X29: s R_X29 = sp ⊖ 16),
  satisfies_all prog (invs0 sp mem raddr c x29) (exits0 sp mem raddr c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ispunct_prog).
    unfold ispunct_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ispunct_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30 & X29).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: pose proof (ls_test (N.lor c 32) 97 25 eq_refl eq_refl) as LT0; change (97 + 25) with 122 in LT0.
  all: rewrite ?LT0 in *.
  all: pose proof (ls_test c 48 9 eq_refl eq_refl) as LT1; change (48 + 9) with 57 in LT1.
  all: rewrite ?LT1 in *.
  all: rewrite ?alpha_or32 in *.
  all: unfold isalnum_spec; cbv zeta.
  all: repeat match goal with
         | H: context [?a <=? ?b] |- _ => destruct (a <=? b)
         | |- context [?a <=? ?b] => destruct (a <=? b) end.
  all: simpl in *; first [reflexivity | discriminate | congruence].
Qed.


Lemma isp_gt: forall c,
  (if 93 <=? msub 32 c 33 then 0 else 1) .| (if c mod 2 ^ 32 =? 126 then 1 else 0) = 0 ->
  msub 32 c 33 > 93.
Proof.
  intros c. rewrite (msub32_cases c 33) by lia. pose proof (mod32_lt c) as Hx.
  revert Hx. generalize (c mod 2^32). intros x Hx.
  repeat match goal with
  | |- context[?a <=? ?b] => destruct (N.leb_spec a b)
  | |- context[?a =? ?b] => destruct (N.eqb_spec a b) end;
  simpl; intros; try discriminate; lia.
Qed.

Lemma isp_le: forall c p,
  (if 93 <=? msub 32 c 33 then 0 else 1) .| (if c mod 2 ^ 32 =? 126 then 1 else 0) = N.pos p ->
  msub 32 c 33 <= 93.
Proof.
  intros c p. rewrite (msub32_cases c 33) by lia. pose proof (mod32_lt c) as Hx.
  revert Hx. generalize (c mod 2^32). intros x Hx.
  repeat match goal with
  | |- context[?a <=? ?b] => destruct (N.leb_spec a b)
  | |- context[?a =? ?b] => destruct (N.eqb_spec a b) end;
  simpl; intros; try discriminate; lia.
Qed.

Theorem ispunct_partial_correctness:
  ∀ prog s sp mem raddr c x29 t xs'
    (P1: ispunct_armv8.ispunct_armv8 ⊆2 prog) (P0: isalnum_armv8.isalnum_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11eeb4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr c x29) (exits1 sp mem raddr c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ispunct_prog).
    unfold ispunct_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ispunct_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30 & X29).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  do 3 arm8_step.
  1: { apply isp_gt in BC. repeat arm8_step. splits; try reflexivity; try assumption; try (apply N.mod_small; assumption). }
  apply isp_le in BC.
  do 3 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply ispunct_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply isalnum_correct_in_ispunct;
    first [ exact ispunct_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
  assert (S2X0: s2 R_X0 = c) by (unfold s2; reflexivity).
  rewrite S2X0. reflexivity.
  assert (S2X0: s2 R_X0 = c) by (unfold s2; reflexivity). rewrite S2X0.
  intros.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply ispunct_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' BC SP64 R64 X2964.
  rename MDL' into MDL. rename t' into t. rename s' into s.
  destruct_inv 64 PRE.
  destruct PRE as (RES & MEM & SP & X30 & X29).
  repeat arm8_step.
  assert (SL: isalnum_spec c < 2^32) by (unfold isalnum_spec; cbv zeta; destruct (_ || _); reflexivity).
  rewrite (N.mod_small _ _ SL).
  splits; try reflexivity; try assumption; try (apply N.mod_small; assumption).
  all: unfold frame_mem; psimpl; try reflexivity; try (apply N.mod_small; assumption).
Qed.

(* Frame: the remaining AAPCS64 callee-saved registers are never written by
   ispunct or isalnum. *)
Theorem ispunct_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates ispunct_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

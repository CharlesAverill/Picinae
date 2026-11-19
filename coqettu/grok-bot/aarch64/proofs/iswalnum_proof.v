(* iswalnum -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls iswalpha)

   SEMANTICS
   ---------
   musl's src/ctype/iswalnum.c:
       int iswalnum(wint_t wc) { return wc-(unsigned)'0' < 10 || iswalpha(wc); }
   compiled to
       sub w1,w0,#0x30; cmp w1,#9; b.hi L; mov w0,#1; ret;
       L: stp x29,x30,[sp,#-16]!; mov x29,sp; bl iswalpha;
          cmp w0,#0; cset w0,ne; ldp x29,x30,[sp],#16; ret.
   This file verifies the composition iswalnum + iswalpha (program
   iswalnum_prog = both lifts) with Picinae's perform_call; iswalpha is the
   callee (id 0) and is re-verified inside the composed program
   (iswalpha_correct_in_iswalnum).

   SPECIFICATION (man 3 iswalnum, Linux man-pages 6.9.1)
   -----------------------------------------------------
     SYNOPSIS
            #include <wctype.h>
            int iswalnum(wint_t wc);
     DESCRIPTION
            The iswalnum() function is the wide-character equivalent of the
            isalnum(3) function.  It tests whether wc is a wide character
            belonging to the wide-character class "alnum".
     RETURN VALUE
            The iswalnum() function returns nonzero if wc is a wide character
            belonging to the wide-character class "alnum".  Otherwise, it
            returns zero.
   musl's class "alnum" = the ASCII digits plus its "alpha" class, a two-level
   bitmap at ELF 0x721b0 (Ghidra 0x1721b0) for wc < 0x20000 plus the range
   0x20000..0x2fffd; see proofs/iswalpha_proof.v and iswalpha_val below.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            iswalnum at 0x1ef14 (ELF vaddr); 0x11ef14 in Ghidra (image base 0x100000)
            iswalpha at 0x1ef48 (ELF vaddr); 0x11ef48 in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/iswalnum_armv8.v and ../lifted/iswalpha_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = wc = c (only c mod 2^32 is used); SP = sp; X30 = raddr;
            X29 = x29; memory m.
   Output:  If execution reaches a RET:
            - 0x11ef24 ((c mod 2^32) - 48 mod 2^32 <= 9, an ASCII digit):
              X0 = 1, memory = m;
            - 0x11ef40 (otherwise): X0 = 0 if iswalpha_val frame_mem c = 0,
              else X0 = 1, where frame_mem is m with x29/raddr stored at
              sp-16..sp-1 and iswalpha_val is iswalpha's result (bitmap bytes
              read from frame_mem, which equals m at the table whenever the
              16 bytes below SP do not overlap it); memory = frame_mem.
            On both paths SP = sp, X30 = raddr, X29 = x29.
            X19..X28 and Z8..Z15 are never written
            (iswalnum_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require iswalnum_armv8 iswalpha_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf GrokLeaf2 GrokRange.
From Grok.proofs Require Import iswalpha_proof.
Import ARM8Notations.
Open Scope N.

Definition iswalnum_prog : program := updateall2 iswalnum_armv8.iswalnum_armv8 iswalpha_armv8.iswalpha_armv8.

Lemma iswalnum_prog_contains: iswalnum_armv8.iswalnum_armv8 ⊆2 iswalnum_prog.
Proof.
  intros s a insn SC. unfold iswalnum_prog, updateall2, updateall, iswalpha_armv8.iswalpha_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem iswalnum_prog_welltyped: welltyped_prog arm8typctx iswalnum_prog.
Proof.
  intros s a. unfold iswalnum_prog, updateall2, updateall.
  destruct (iswalpha_armv8.iswalpha_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (iswalpha_proof.iswalpha_welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply iswalnum_armv8.welltyped.
Qed.

(* iswalpha result as a function of memory m and argument a (see iswalpha_proof). *)
Definition iswalpha_val (m a : N) : N :=
  if a mod 2^32 <=? 131071 then (m Ⓑ[0x1721b0 + (m Ⓑ[0x1721b0 + (a mod 2^32 >> 8)] * 32 + (a >> 3) mod 32)] >> a mod 8) .& 1
  else if a mod 2^32 <=? 196605 then 1 else 0.

Lemma iswalpha_val_lt: ∀ m a, iswalpha_val m a < 2^32.
Proof.
  intros. unfold iswalpha_val.
  destruct (_ <=? 131071). change 1 with (N.ones 1). rewrite N.land_ones.
  eapply N.lt_le_trans. apply N.mod_lt. discriminate. discriminate.
  destruct (_ <=? 196605); reflexivity.
Qed.

Lemma land1_mod2: ∀ x, x .& 1 = x mod 2.
Proof. intros. change 1 with (N.ones 1). apply N.land_ones. Qed.

Ltac isw_flags :=
  repeat match goal with |- context[msub 32 ?v ?k] => rewrite (msub32_cases v k) by lia end;
  match goal with |- context[?v mod 2^32] =>
    let Hx := fresh "Hx" in pose proof (mod32_lt v) as Hx; revert Hx; generalize (v mod 2^32); intros ? ? end;
  repeat match goal with
  | |- context[?a <=? ?b] => destruct (N.leb_spec a b)
  | |- context[?a <? ?b] => destruct (N.ltb_spec a b)
  | |- context[?a =? ?b] => destruct (N.eqb_spec a b) end;
  simpl; intros; try discriminate; lia.

Section Invariants.
  Variables (sp mem raddr c x29 : N).
  Definition frame_mem := mem [Ⓠ sp ⊖ 16 := x29] [Ⓠ sp ⊖ 8 := raddr].
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* iswalnum *)
    | 0x11ef14 => Inv 1 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x11ef24 => Post 1 (s R_X0 = 1 /\ msub 32 c 48 <= 9 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    | 0x11ef40 => Post 1 (s R_X0 = (if iswalpha_val frame_mem c =? 0 then 0 else 1) /\ msub 32 c 48 > 9 /\
                          s V_MEM64 = frame_mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29)
    (* iswalpha, called with the frame pushed *)
    | 0x11ef48 => Inv 0 (s R_X0 = c /\ s V_MEM64 = frame_mem /\ s R_SP = sp ⊖ 16 /\ s R_X30 = 0x11ef34 /\ s R_X29 = sp ⊖ 16)
    | 0x11ef64 => Post 0 (s R_X0 = iswalpha_val frame_mem c /\ s V_MEM64 = frame_mem /\ s R_SP = sp ⊖ 16 /\ s R_X30 = 0x11ef34 /\ s R_X29 = sp ⊖ 16)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 iswalnum_prog invs.
  Definition invs0 := make_invs 0 iswalnum_prog invs.
  Definition exits1 := make_exits 1 iswalnum_prog invs.
  Definition invs1 := make_invs 1 iswalnum_prog invs.
End Invariants.

Theorem iswalpha_correct_in_iswalnum:
  ∀ prog s sp mem raddr c x29 t xs'
    (P1: iswalnum_armv8.iswalnum_armv8 ⊆2 prog) (P0: iswalpha_armv8.iswalpha_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ef48, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = c) (MEM: s V_MEM64 = frame_mem sp mem raddr x29) (SP: s R_SP = sp ⊖ 16)
    (X30: s R_X30 = 0x11ef34) (X29: s R_X29 = sp ⊖ 16),
  satisfies_all prog (invs0 sp mem raddr c x29) (exits0 sp mem raddr c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=iswalnum_prog).
    unfold iswalnum_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply iswalnum_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30 & X29).
  repeat grok_step.
  all: remember (frame_mem sp mem raddr x29) as fm; clear Heqfm.
  all: unfold iswalpha_val; splits; try reflexivity; try assumption.
  all: try grok_leaf_close.
  all: try clear MDL1.
  all: rewrite ?land1_mod2, ?N.add_assoc.
  all: grok_tab_close.
Qed.

Theorem iswalnum_partial_correctness:
  ∀ prog s sp mem raddr c x29 t xs'
    (P1: iswalnum_armv8.iswalnum_armv8 ⊆2 prog) (P0: iswalpha_armv8.iswalpha_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ef14, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs1 sp mem raddr c x29) (exits1 sp mem raddr c x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=iswalnum_prog).
    unfold iswalnum_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply iswalnum_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30 & X29).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  do 3 arm8_step.
  all: first [ (assert (G: msub 32 c 48 <= 9) by (revert BC; clear; isw_flags); clear BC)
             | (assert (G: msub 32 c 48 > 9) by (revert BC; clear; isw_flags); clear BC) ].
  all: try solve [ match goal with G: _ <= 9 |- _ => idtac end;
                   repeat arm8_step; splits; try reflexivity; try assumption; try (apply N.mod_small; assumption) ].
  do 3 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply iswalnum_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply iswalpha_correct_in_iswalnum;
    first [ exact iswalnum_prog_contains | apply subset_updateall2 | eassumption | reflexivity ].
  assert (S2X0: s2 R_X0 = c) by (unfold s2; reflexivity).
  rewrite S2X0. reflexivity.
  assert (S2X0: s2 R_X0 = c) by (unfold s2; reflexivity). rewrite S2X0.
  intros.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply iswalnum_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' G SP64 R64 X2964.
  rename MDL' into MDL. rename t' into t. rename s' into s.
  destruct_inv 64 PRE.
  destruct PRE as (RES & MEM & SP & X30 & X29).
  repeat arm8_step.
  rewrite (N.mod_small _ _ (iswalpha_val_lt _ _)).
  splits; try reflexivity; try assumption; try (apply N.mod_small; assumption).
  all: unfold frame_mem; psimpl; try reflexivity; try (apply N.mod_small; assumption).
Qed.

(* Frame: the remaining AAPCS64 callee-saved registers are never written by
   iswalnum or iswalpha. *)
Theorem iswalnum_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates iswalnum_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

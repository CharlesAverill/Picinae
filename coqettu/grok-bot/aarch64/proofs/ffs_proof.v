(* ffs -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/misc/ffs.c:
       int ffs(int i) { return i ? a_ctz_l(i)+1 : 0; }
   The binary: cbz w0 -> ret (X0 unchanged, so W0 = 0); otherwise
   sxtw x0,w0; rbit x0,x0; clz x0,x0; add w0,w0,#1; ret.
   The lifter expands rbit into a 6-stage mask-and-shift network; psimpl
   rewrites it further.  The proof reifies the resulting expression
   (lib/GrokBitRefl.v) and checks by computation (brev_check) that bit j of
   it is bit 63-j of the input for j < 64 and 0 above.  clz is lifted as
   64 - N.size x (our LZCOUNT lifter fix, ../lifter/README_GROK.md).

   SPECIFICATION (man 3 ffs, Linux man-pages 6.9.1)
   ------------------------------------------------
     SYNOPSIS
            #include <strings.h>
            int ffs(int i);

     DESCRIPTION
            The ffs() function returns the position of the first (least
            significant) bit set in the word i.  The least significant bit is
            position 1 and the most significant position is, for example, 32
            or 64.

     RETURN VALUE
            These functions return the position of the first bit set, or 0 if
            no bits are set in i.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            ffs at 0x3b294 (ELF vaddr); 0x13b294 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE and LZCOUNT fixes, see ../lifter/README_GROK.md),
            options --globalAddressing --typeCheck; see ../lifted/ffs_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = i (X0 = i, only its low 32 bits matter); SP = sp;
            X30 = raddr; m = memory.
   Output:  At the RET (0x13b2a8): memory = m, SP = sp, X30 = raddr and
            ffs_spec i (X0 mod 2^32), i.e. the int result W0 is
              - 0 if i mod 2^32 = 0, or
              - b + 1 where b < 32 is the index of the lowest set bit of i
                (bit b of i is 1 and bits 0..b-1 are 0).
            Callee-saved registers X19..X29, SP, Z8..Z15 and X30 are never
            written (ffs_preserves_callee_saved, ffs_preserves_x30).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List Btauto.
Require Import Picinae_armv8.
From Grok.lifted Require Import ffs_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem ffs_nwc: ∀ s2 s1, ffs_armv8 s1 = ffs_armv8 s2.
Proof. reflexivity. Qed.

Theorem ffs_welltyped: welltyped_prog arm8typctx ffs_armv8.
Proof. Picinae_typecheck. Qed.

Theorem ffs_preserves_memory:
  forall_endstates ffs_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ffs_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates ffs_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem ffs_preserves_x30:
  forall_endstates ffs_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.


Lemma lowest_bit: ∀ x, x ≠ 0 -> ∃ t, N.testbit x t = true /\ ∀ j, j < t -> N.testbit x j = false.
Proof.
  intro x. induction x as [x IH] using (well_founded_induction N.lt_wf_0). intro NZ.
  destruct (N.odd x) eqn:O.
  - exists 0. split. rewrite N.bit0_odd. exact O. intros j J. lia.
  - assert (H2: x / 2 ≠ 0).
    { intro Z. apply NZ. pose proof (N.div_mod x 2 ltac:(discriminate)) as D.
      rewrite Z in D. rewrite <- N.bit0_mod, N.bit0_odd, O in D. simpl in D. lia. }
    destruct (IH (x/2) ltac:(apply N.div_lt; lia) H2) as (t & T & L).
    exists (N.succ t). rewrite N.div2_bits in T. split. exact T.
    intros j J. destruct (N.eq_dec j 0) as [->|JN].
    + rewrite N.bit0_odd. exact O.
    + replace j with (N.succ (N.pred j)) by lia. rewrite <- N.div2_bits.
      apply L. lia.
Qed.

Lemma scast_low32: ∀ x j, j < 32 -> N.testbit (scast 32 64 x) j = N.testbit x j.
Proof.
  intros x j J.
  rewrite <- (N.mod_pow2_bits_low (scast 32 64 x) 32 j J), <- (N.mod_pow2_bits_low x 32 j J).
  f_equal. pose proof (ofZ_toZ_bitcast 32 32 x ltac:(reflexivity)) as E.
  unfold scast, ofZ in *. rewrite <- E. apply N2Z.inj.
  rewrite N2Z.inj_mod, !Z2N.id by (apply Z.mod_pos_bound; lia).
  change (Z.of_N (2^32)) with (2^32)%Z. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
  apply Z.mod_mod_divide; first [ (exists (2^32)%Z; reflexivity) | lia ].
Qed.

Lemma size_rev: ∀ e y t, (∀ j, N.testbit e j = (j <? 64) && N.testbit y (63 - j)) ->
  t < 64 -> N.testbit y t = true -> (∀ j, j < t -> N.testbit y j = false) -> N.size e = 64 - t.
Proof.
  intros e y t RB T Y L.
  assert (B: N.testbit e (63 - t) = true).
  { rewrite RB. replace (63 - (63 - t)) with t by lia. rewrite Y. apply N.ltb_lt in T.
    replace (63 - t <? 64) with true. reflexivity. symmetry. apply N.ltb_lt. lia. }
  assert (NZ: e ≠ 0) by (intro Z; rewrite Z, N.bits_0 in B; discriminate).
  rewrite N.size_log2 by exact NZ.
  rewrite (N.log2_bits_unique e (63 - t)). lia. exact B.
  intros m M. rewrite RB. destruct (m <? 64) eqn:MM; [|reflexivity].
  apply N.ltb_lt in MM. rewrite Bool.andb_true_l. apply L. lia.
Qed.

(* ffs result: 0 if no bit of the int is set, else 1 + index of the lowest set bit. *)
Definition ffs_spec (i r:N) :=
  (i mod 2^32 = 0 /\ r = 0) \/
  (∃ t, t < 32 /\ N.testbit i t = true /\ (∀ j, j < t -> N.testbit i j = false) /\ r = t + 1).

Section Invariants.
  Variables (sp mem raddr i : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x13b294 => Inv 0 (s R_X0 = i /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x13b2a8 => Post 0 (ffs_spec i (s R_X0 mod 2^32) /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ffs_exits := make_exits 0 ffs_armv8 invs.
  Definition ffs_invs := make_invs 0 ffs_armv8 invs.
End Invariants.

Theorem ffs_partial_correctness:
  ∀ prog s sp mem raddr i t xs'
    (PROG: ffs_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x13b294, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = i),
  satisfies_all prog (ffs_invs sp mem raddr i) (ffs_exits sp mem raddr i) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ffs_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ffs_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ffs_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  repeat arm8_step.
  - (* i mod 2^32 = 0 *)
    apply N.eqb_eq in BC. splits; try assumption. left. split. exact BC.
    exact BC.
  - rewrite N.shiftr_0_r.
    set (y := scast 32 64 (i mod 2^32)).
    assert (Y64: y < 2^64) by (unfold y, scast, ofZ; apply N2Z.inj_lt; rewrite Z2N.id by (apply Z.mod_pos_bound; lia); apply Z.mod_pos_bound; lia).
    assert (YD: y = scast 32 64 (i mod 2^32)) by reflexivity.
    clearbody y.
    match goal with |- context [ N.size ?E ] =>
      let r := reify_bx y E in change E with (bden y r);
      pose proof (brev_check_ok r y Y64 ltac:(vm_compute; reflexivity)) as RB
    end.
    apply N.eqb_neq in BC.
    destruct (lowest_bit _ BC) as (b & T & L).
    assert (T32: b < 32).
    { destruct (N.lt_ge_cases b 32). assumption. rewrite N.mod_pow2_bits_high in T by assumption. discriminate. }
    rewrite N.mod_pow2_bits_low in T by assumption.
    assert (YB: N.testbit y b = true) by (rewrite YD, scast_low32, N.mod_pow2_bits_low by lia; exact T).
    assert (YL: ∀ j, j < b -> N.testbit y j = false).
    { intros j J. rewrite YD, scast_low32 by lia. exact (L j J). }
    rewrite (size_rev _ y b RB ltac:(lia) YB YL).
    splits; try assumption. right. exists b. splits; try assumption.
    intros j J. specialize (L j J). rewrite N.mod_pow2_bits_low in L by lia. exact L.
    rewrite msub_small by lia; try rewrite N.mod_small by lia; lia.
Qed.

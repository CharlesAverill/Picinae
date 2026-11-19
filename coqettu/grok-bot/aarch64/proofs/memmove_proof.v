(* memmove -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (src/string/memmove.c)

   SEMANTICS
   ---------
   void *memmove(void *dest, const void *src, size_t n): copies n bytes from
   src to dest, correctly for overlapping areas, and returns dest.  musl's C:
     if (d == s) return d;
     if ((uintptr_t)s-(uintptr_t)d-n <= -2*n) return memcpy(d, s, n);
     if (d < s) { forward: byte loop to 8-byte alignment of d when
                  (s^d)%8 == 0, then 8-byte word loop, then byte tail }
     else       { backward: byte loop down to 8-byte alignment of d+n when
                  (s^d)%8 == 0, then word loop, then byte loop }
   The unsigned test s-d-n <= -2n holds exactly when n > 0 and the areas are
   disjoint; the binary then tail-calls memcpy (b 0x118270).

   SPECIFICATION (man 3 memmove, Linux man-pages 6.9.1)
   -----------------------------------------------------
     The memmove() function copies n bytes from memory area src to memory
     area dest.  The memory areas may overlap: copying takes place as though
     the bytes in src are first copied into a temporary array that does not
     overlap src or dest, and the bytes are then copied from the temporary
     array to dest.  The memmove() function returns a pointer to dest.

   THEOREMS AND PRECONDITIONS
   --------------------------
   The three theorems together cover every n < 2^62 with d + n < 2^64 and
   s + n < 2^64:
   - memmove_overlap_partial_correctness: n = 0, or the areas overlap
     (d < s + n and s < d + n; includes d = s).  The loops are proved with
     overlap-aware invariants (GrokMove.fwd / bwd): the finished dest prefix
     (forward) or suffix (backward) equals the ORIGINAL source bytes, and the
     source bytes not yet read are still original (a store at d+k only hits
     source bytes already read, since d < s, resp. s < d going down).
     The disjoint branch (0x15e750) is proved unreachable (GrokMove.mva_branch).
   - memmove_disjoint_small_partial_correctness (0 < n <= 128) and
     memmove_disjoint_large_partial_correctness (128 < n): disjoint areas.
     The straight-line prefix is stepped instruction by instruction
     (GrokTail.step_satisfies_all) to the tail call, after which the memcpy
     theorems apply (memcpy_proof / memcpy_large_proof); their invariant
     sets, exits and postcondition (memcpy_post) are the conclusion.
   - n < 2^62: the binary computes -2n (neg x7, x2, lsl #1) modulo 2^64, so
     the test is only meaningful while 2n does not wrap; objects that large
     cannot exist (aarch64 Linux user space is below 2^48).
   - d + n < 2^64, s + n < 2^64: an object cannot end at the very top of the
     address space.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            memmove at 0x5e708 (ELF vaddr); 0x15e708 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/memmove_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest = d, X1 = src = s, X2 = n; X30 = return address raddr;
            SP = sp; mem = memory on entry.
   Output:  If execution reaches a RET (0x15e7b8, or memcpy's RETs after the
            tail call): X0 = d, SP = sp, X30 = raddr, byte d+i equals the
            entry byte mem[s+i] for every i < n, and every byte outside
            [d, d+n) is unchanged (memcpy_post / copied).  The AAPCS64
            callee-saved registers are unchanged (memmove_preserves_callee_saved;
            memcpy_preserves_callee_saved for the tail call).
 *)

From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memmove_armv8 memcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCopy GrokCov GrokTail GrokPrefix.
From Grok.proofs Require Import memcpy_defs memcpy_proof memcpy_large_defs memcpy_large_proof.
From Grok.proofs Require Import memmove_lib memmove_defs memmove_prefix.
Import ARM8Notations.
Open Scope N.

Theorem memmove_nwc: ∀ s2 s1, memmove_armv8 s1 = memmove_armv8 s2.
Proof. reflexivity. Qed.

Theorem memmove_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates memmove_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem memmove_preserves_x30:
  forall_endstates memmove_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Ltac bools_to_props_mv := repeat match goal with
 | H: (?a =? ?b) = true |- _ => apply N.eqb_eq in H
 | H: (?a =? ?b) = false |- _ => apply N.eqb_neq in H
 | H: (?a <=? ?b) = true |- _ => apply N.leb_le in H
 | H: (?a <=? ?b) = false |- _ => apply N.leb_gt in H
 | H: (?a <? ?b) = true |- _ => apply N.ltb_lt in H
 | H: (?a <? ?b) = false |- _ => apply N.ltb_ge in H
 | H: context[if ?c then _ else _] |- _ =>
     match type of H with _ V_MEM64 = _ => fail 1 | _ => destruct c eqn:? end
 end.
Ltac splitc := repeat match goal with |- _ ∧ _ => split end.
Ltac mvbase := lazymatch goal with |- (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ∧ _ =>
  split; [splitc; first [assumption | reflexivity | lia] |] end.
Ltac memr := match goal with H: _ V_MEM64 = ?m |- _ => rewrite H end.
Theorem memmove_overlap_partial_correctness: ∀ prog s mem d src n sp raddr t xs'
    (P1: memmove_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e708, s))
    (MDL: models arm8typctx s) (HPRE: mva_pre mem d src n sp raddr s),
  satisfies_all prog (mva_invs mem d src n sp raddr) (mva_exits mem d src n sp raddr) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memmove_armv8). exact P1.
    intros a s1 t1 EXIT NOCODE. unfold mva_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL HPRE START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. exact HPRE.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memmove_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold mva_pre, mv_base in *; repeat match goal with H: _ /\ _ |- _ => destruct H | H: ∃ _, _ |- _ => destruct H end.
  all: try match goal with H: False |- _ => destruct H end.
  all: repeat grok_step.
  all: try match goal with H: models _ _ |- _ => clear H end.
  all: repeat match goal with H: MemAcc _ _ _ _ _ |- _ => clear H end.
  all: bools_to_props_mv; rewrite ?N.shiftr_div_pow2 in *.
  all: try (exfalso; lia).
  all: try lor_absurd.
  all: unfold mv_base, memcpy_post; upd_simpl.
  all: rewrite ?land7, ?land_m8 in * by (change (2^64) with 18446744073709551616 in *; lia).
  all: repeat match goal with H: negb _ = true |- _ => apply Bool.negb_true_iff in H
                            | H: negb _ = false |- _ => apply Bool.negb_false_iff in H end; bools_to_props_mv.
  (* 1: d = src *)
  - match goal with BC: d = src |- _ => rewrite <- BC in * end. mvbase. memr. apply copied_same.
  (* 2, 3: backward entry *)
  - mvbase. split; [lia|]. split; [reflexivity|]. exists n. split; [reflexivity|]. split; [lia|]. memr. apply bwd_init.
  - mvbase. split; [lia|]. split; [reflexivity|]. exists n. split; [reflexivity|]. split; [lia|]. memr. apply bwd_init.
  (* 4, 5: forward entry *)
  - mvbase. split; [lia|]. exists 0. memr. splitc; try lia. apply fwd_init.
  - mvbase. split; [lia|]. exists 0, 0. memr. splitc; try lia. apply fwd_init.
  (* 6, 7: disjoint branch impossible *)
  - exfalso. destruct (mva_branch d src n) as [A B]; try assumption; lia.
  - exfalso. destruct (mva_branch d src n) as [A B]; try assumption; lia.
  (* 8: forward aligned -> word loop *)
  - mvbase. split; [assumption|]. exists x, 0.
    match goal with H: (d + x) mod 8 = 0 |- _ => rewrite H end.
    splitc; try lia; try reflexivity. rewrite N.add_0_r. assumption.
  (* 9: forward alignment loop, n exhausted *)
  - mvbase. match goal with H: fwd _ _ _ _ _ ?k |- _ => replace k with n in H by lia; apply fwd_done; exact H end.
  (* 10: forward alignment byte *)
  - mvbase. split; [assumption|]. exists (x + 1). num_norm. splitc; try lia.
    rewrite (fwd_read mem (s1 V_MEM64) src d n x x 1) by (try assumption; lia).
    apply fwd_step; try assumption; try lia. intros j J. apply byte_load. assumption.
  (* 11: word loop exit -> byte tail *)
  - mvbase. split; [assumption|]. exists (x + x0), 0. num_norm. splitc; try lia. rewrite N.add_0_r. assumption.
  (* 12: forward word *)
  - mvbase. split; [assumption|]. exists x, (x0 + 8).
    assert (X8: x0 + 8 <= n - x - (n - x) mod 8)
      by (apply mod8_up; [assumption | apply sub_mod8 | assumption | assumption]).
    num_norm. splitc; try lia.
    all: try (apply mod8_add8; assumption).
    replace (src + x + x0) with (src + (x + x0)) by lia. replace (d + x + x0) with (d + (x + x0)) by lia.
    rewrite (fwd_read mem (s1 V_MEM64) src d n (x + x0) (x + x0) 8) by (try assumption; lia).
    replace (x + (x0 + 8)) with (x + x0 + 8) by lia.
    apply fwd_step; try assumption; try lia. intros j J. apply byte_load. assumption.
  (* 13: byte tail done *)
  - mvbase. match goal with H: fwd _ _ _ _ _ ?k |- _ => replace k with n in H by lia; apply fwd_done; exact H end.
  (* 14: forward tail byte *)
  - mvbase. split; [assumption|]. exists x, (x0 + 1). num_norm. splitc; try lia.
    replace (src + x + x0) with (src + (x + x0)) by lia. replace (d + x + x0) with (d + (x + x0)) by lia.
    rewrite (fwd_read mem (s1 V_MEM64) src d n (x + x0) (x + x0) 1) by (try assumption; lia).
    replace (x + (x0 + 1)) with (x + x0 + 1) by lia.
    apply fwd_step; try assumption; try lia. intros j J. apply byte_load. assumption.
  (* 15: return *)
  - splitc; first [reflexivity | assumption].
  (* 16: backward aligned -> word loop *)
  - mvbase. split; [assumption|]. split; [assumption|]. exists x, x. splitc; try reflexivity; try lia; try assumption.
    all: first [ (apply N.mod_le; discriminate) | (rewrite N.sub_diag; reflexivity) ].
  (* 17: backward alignment loop, done *)
  - mvbase. match goal with H: bwd _ _ _ _ _ ?k |- _ => replace k with 0 in H by lia; apply bwd_done; exact H end.
  (* 18: backward alignment byte *)
  - mvbase. split; [assumption|]. split; [reflexivity|]. exists (x - 1). num_norm. splitc; try lia.
    match goal with |- bwd _ (setmem 64 LittleE 1 _ ?a (getmem 64 LittleE 1 _ ?b)) _ _ _ _ =>
      replace a with (d + (x - 1)) by lia; replace b with (src + (x - 1)) by lia end.
    rewrite (bwd_read mem (s1 V_MEM64) src d n x (x - 1) 1) by (try assumption; lia).
    eapply (bwd_step mem _ src d n (x - 1) 1); try assumption; try lia.
    all: first [ (replace (x - 1 + 1) with x by lia; assumption) | (intros j J; apply byte_load; assumption) ].
  (* 19: backward word loop exit *)
  - mvbase. split; [assumption|]. split; [assumption|]. exists (x mod 8). splitc; try reflexivity.
    all: try (pose proof (N.mod_le x 8 ltac:(discriminate)); lia).
    match goal with H: ?a = x mod 8, B: bwd _ _ _ _ _ ?a |- _ => rewrite <- H; exact B end.
  (* 20: backward word *)
  - mvbase. split; [assumption|]. split; [reflexivity|].
    destruct (mod8_down x x0) as [D1 D2]; try assumption.
    exists x, (x0 - 8). num_norm. splitc; try lia; try assumption.
    match goal with |- bwd _ (setmem 64 LittleE 8 _ ?a (getmem 64 LittleE 8 _ ?b)) _ _ _ _ =>
      replace a with (d + (x0 - 8)) by lia; replace b with (src + (x0 - 8)) by lia end.
    rewrite (bwd_read mem (s1 V_MEM64) src d n x0 (x0 - 8) 8) by (try assumption; lia).
    eapply (bwd_step mem _ src d n (x0 - 8) 8); try assumption; try lia.
    all: first [ (replace (x0 - 8 + 8) with x0 by lia; assumption) | (intros j J; apply byte_load; assumption) ].
  (* 21: backward tail byte *)
  - mvbase. split; [assumption|]. split; [reflexivity|]. exists (x - 1). num_norm. splitc; try lia.
    match goal with |- bwd _ (setmem 64 LittleE 1 _ ?a (getmem 64 LittleE 1 _ ?b)) _ _ _ _ =>
      replace a with (d + (x - 1)) by lia; replace b with (src + (x - 1)) by lia end.
    rewrite (bwd_read mem (s1 V_MEM64) src d n x (x - 1) 1) by (try assumption; lia).
    eapply (bwd_step mem _ src d n (x - 1) 1); try assumption; try lia.
    all: first [ (replace (x - 1 + 1) with x by lia; assumption) | (intros j J; apply byte_load; assumption) ].
  (* 22: backward tail done *)
  - mvbase. match goal with H: bwd _ _ _ _ _ ?k |- _ => replace k with 0 in H by lia; apply bwd_done; exact H end.
Qed.

Ltac noaddr := intros a s1 t1 IN; repeat (destruct IN as [<-|IN]; [reflexivity|]); destruct IN.

Theorem memmove_disjoint_small_partial_correctness:
  ∀ prog s mem d src n sp raddr t xs'
    (P1: memmove_armv8 ⊆2 prog) (P0: memcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e708, s)) (MDL: models arm8typctx s)
    (X0: s R_X0 = d) (X1: s R_X1 = src) (X2: s R_X2 = n) (MEM: s V_MEM64 = mem)
    (SP: s R_SP = sp) (X30: s R_X30 = raddr)
    (POS: 0 < n) (SMALL: n <= 128) (ND: d + n < 2^64) (NS: src + n < 2^64)
    (DISJ: src + n <= d \/ d + n <= src),
  satisfies_all prog (memcpy_invs mem d src n sp raddr) (memcpy_exits mem d src n sp raddr) (xs'::t).
Proof.
  intros. eapply (r708 prog _ _ mem d src n sp raddr P1); try eassumption.
  - intros [[a|i] s1] t1 t2; reflexivity.
  - intros [[a|i] s1] t1 t2; reflexivity.
  - reflexivity.
  - noaddr.
  - noaddr.
  - intros s1 t1 xs1 START HP. unfold Pb in HP.
    destruct HP as (M & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    eapply memcpy_partial_correctness; try eassumption.
    unfold memcpy_pre. tauto.
  - unfold Pb. split; [exact MDL|]. repeat split; try assumption; lia.
Qed.

Theorem memmove_disjoint_large_partial_correctness:
  ∀ prog s mem d src n sp raddr t xs'
    (P1: memmove_armv8 ⊆2 prog) (P0: memcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e708, s)) (MDL: models arm8typctx s)
    (X0: s R_X0 = d) (X1: s R_X1 = src) (X2: s R_X2 = n) (MEM: s V_MEM64 = mem)
    (SP: s R_SP = sp) (X30: s R_X30 = raddr)
    (LARGE: 128 < n) (NB: n < 2^62) (ND: d + n < 2^64) (NS: src + n < 2^64)
    (DISJ: src + n <= d \/ d + n <= src),
  satisfies_all prog (mcl_invs mem d src n sp raddr) (mcl_exits mem d src n sp raddr) (xs'::t).
Proof.
  intros. eapply (r708 prog _ _ mem d src n sp raddr P1); try eassumption.
  - intros [[a|i] s1] t1 t2; reflexivity.
  - intros [[a|i] s1] t1 t2; reflexivity.
  - reflexivity.
  - noaddr.
  - noaddr.
  - intros s1 t1 xs1 START HP. unfold Pb in HP.
    destruct HP as (M & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    eapply memcpy_large_partial_correctness; try eassumption.
    unfold mcl_pre. tauto.
  - unfold Pb. split; [exact MDL|]. repeat split; try assumption; lia.
Qed.

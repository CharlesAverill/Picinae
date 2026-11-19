(* strspn -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/string/strspn.c (casts dropped and pointer dereferences
   written with [0] so this comment stays well formed):
       #define BITOP(a,b,op) \
        ((a)[(size_t)(b)/(8*sizeof *(a))] op (size_t)1<<((size_t)(b)%(8*sizeof *(a))))
       size_t strspn(const char *s, const char *c) {
           const char *a = s;
           size_t byteset[32/sizeof(size_t)] = { 0 };
           if (!c[0]) return 0;
           if (!c[1]) {
               for (; s[0] == c[0]; s++);
               return s-a;
           }
           for (; c[0] && BITOP(byteset, c[0], |=); c++);
           for (; s[0] && BITOP(byteset, s[0], &); s++);
           return s-a;
       }
   compiled as a leaf with a 32-byte frame (sub sp,sp,#0x20) holding the
   table; the table is zeroed by ldp/stp q30,q31 from a 32-byte all-zero
   .rodata constant at 0x19e6b0 (ELF 0x9e6b0, verified zero in the binary).
   Paths: c[0] = 0 (return 0), single-byte set (0x15f340 cmp loop), table
   build (0x15f314) and table scan (0x15f360, tbnz).  All paths are covered.

   SPECIFICATION (man 3 strspn, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            size_t strspn(const char *s, const char *accept);
     DESCRIPTION
            The strspn() function calculates the length (in bytes) of the
            initial segment of s which consists entirely of bytes in accept.
     RETURN VALUE
            The strspn() function returns the number of bytes in the initial
            segment of s which consist only of bytes from accept.

PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strspn at 0x5f2e8 (ELF vaddr); 0x15f2e8 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strspn_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s (p), X1 = accept (c), SP = sp, X30 = raddr; memory mem.
   PRECONDITION (ss_pre sp mem p c Ks Lc), stated explicitly:
            - Ks = strlen(p): bytes p..p+Ks-1 nonzero, byte p+Ks = 0;
            - Lc = strlen(c): bytes c..c+Lc-1 nonzero, byte c+Lc = 0;
            - the 32 bytes at 0x19e6b0 are zero (mem Ⓧ[0x19e6b0] = 0 and
              mem Ⓧ[0x19e6c0] = 0: the .rodata constant, as in the binary);
            - 32 <= sp < 2^64; p+Ks+33 <= sp and c+Lc+33 <= sp (both strings,
              with their NULs, lie below the 32-byte frame sp-32..sp-1).
   Output:  If execution reaches the RET (0x15f380), with M the final memory:
            X0 = K for some K <= Ks such that every byte p[i], i < K, occurs
            in c[0..Lc) (cs_in), and either K = Ks or p[K] does not occur in
            c[0..Lc) -- i.e. K = strspn(p, c);  SP = sp, X30 = raddr;
            M[a] = mem[a] for every address a outside sp-32..sp-1 (ss_post).
            X19..X29 and Z8..Z15 are never written
            (strspn_preserves_other_callee_saved).  Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strspn_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require Import strcspn_defs strcspn_proof.
From Grok.proofs Require Import strspn_defs.
Import ARM8Notations.
Open Scope N.

Ltac llia := repeat match goal with
  | H: context [getmem _ _ _ _ _] |- _ => clear H
  | H: models _ _ |- _ => clear H
  | H: nilfree _ _ _ |- _ => clear H
  | H: ss_pre _ _ _ _ _ _ |- _ => clear H
  | H: ∀ _, _ |- _ => clear H
  | H: ?f ?v = _ |- _ => match type of f with store => clear H | var -> N => clear H end
  end; lia.

Lemma z_mem_out: ∀ sp mem a, 32 <= sp -> sp < 2^64 -> a < 2^64 -> (a < sp - 32 \/ sp <= a) ->
  (mem [Ⓧ sp ⊖ 32 := 0] [Ⓧ sp ⊖ 16 := 0]) Ⓑ[a] = mem Ⓑ[a].
Proof.
  intros sp mem a S1 S2 A O. rewrite !(msub_small 64 sp) by L64.
  repeat rd1; first [reflexivity | exfalso; L64].
Qed.

Lemma z_mem: ∀ sp mem c, 32 <= sp -> sp < 2^64 -> ss_mem sp mem c 0 (mem [Ⓧ sp ⊖ 32 := 0] [Ⓧ sp ⊖ 16 := 0]).
Proof.
  intros sp mem c S1 S2. split.
  - intros a A O. apply z_mem_out; assumption.
  - intros w W. change (bset _ _ (N.to_nat 0) _) with 0. apply zero_q; [L64|]. intros i I.
    rewrite !(msub_small 64 sp) by L64.
    repeat rd1; first [unfold byte; rewrite N.shiftr_0_l; reflexivity | exfalso; L64].
Qed.


Lemma sm_test: ∀ sp mem c L M (b:N),
  ss_mem sp mem c L M -> b / 64 < 4 ->
  (((M Ⓠ[sp - 32 + (b >> 6 << 3)] >> b mod 64) mod 2 =? 0) = true -> ~ cs_in mem c L b) /\
  (((M Ⓠ[sp - 32 + (b >> 6 << 3)] >> b mod 64) mod 2 =? 0) = false -> cs_in mem c L b).
Proof.
  intros sp mem c L M b [_ B] BL.
  rewrite b_idx, B by exact BL. rewrite N.shiftr_div_pow2, <- N.testbit_spec'.
  pose proof (N.div_mod b 64 ltac:(discriminate)) as DM.
  pose proof (N.mod_lt b 64 ltac:(discriminate)) as ML.
  pose proof (bset_bit mem c (N.to_nat L) (b / 64) (b mod 64) ML) as BB.
  rewrite N2Nat.id, <- DM in BB. unfold cs_in. split; intro H.
  - intro IN. apply BB in IN. rewrite IN in H. simpl in H. discriminate.
  - apply BB. destruct N.testbit; [reflexivity | discriminate].
Qed.

Lemma sm_step: ∀ sp mem c j M (b:N),
  ss_mem sp mem c j M -> 32 <= sp -> sp < 2^64 ->
  mem Ⓑ[c + j] = b -> b / 64 < 4 ->
  ss_mem sp mem c (j + 1)
    (M [Ⓠ sp - 32 + (b >> 6 << 3) := 1 << b mod 64 .| M Ⓠ[sp - 32 + (b >> 6 << 3)] ]).
Proof.
  intros sp mem c j M b [F B] S1 S2 EB BL.
  rewrite b_idx. split.
  - intros a A O. rewrite read_out by L64. apply F; assumption.
  - intros w W. rewrite N.add_1_r, N2Nat.inj_succ. cbn [bset]. rewrite N2Nat.id, EB.
    destruct (N.eqb_spec (b / 64) w) as [E|E].
    + subst w. rewrite getmem_setmem by L64. rewrite B by exact W.
      rewrite N.shiftl_1_l, N.lor_comm. apply N.mod_small. apply lor_bound; [apply bset_lt | apply pow_lt64].
    + rewrite <- B by exact W. destruct (N.lt_ge_cases w (b / 64)).
      * apply getmem_setmem_above; L64.
      * apply getmem_setmem_below; L64.
Qed.

Lemma sm_out: ∀ sp mem c j M a, ss_mem sp mem c j M -> a < 2^64 -> (a < sp - 32 \/ sp <= a) -> M Ⓑ[a] = mem Ⓑ[a].
Proof. intros sp mem c j M a [F _] A O. apply F; assumption. Qed.

Lemma ss_case_15f2e8: ∀ sp mem raddr p c Ks Lc (s1:store) (t:list (exit*store)),
  ss_pre sp mem p c Ks Lc ->
  raddr < 18446744073709551616 -> p < 18446744073709551616 -> c < 18446744073709551616 ->
  models arm8typctx s1 ->
  ss_invs sp mem raddr p c Ks Lc Prop (fun _ P => P) (fun _ P => P) True s1 0x15f2e8 ->
  nextinv strspn_armv8.strspn_armv8 (ss_invs0 sp mem raddr p c Ks Lc) (ss_exits sp mem raddr p c Ks Lc) false ((Addr 0x15f2e8, s1) :: t).
Proof.
  intros sp mem raddr p c Ks Lc s1 t PRE0 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & R0 & R1 & SPlo & SPhi & BP & BC).
  repeat arm8_step.
  all: rewrite R0, R1 in *.
  all: nrm.
  all: clear MDL1.
  all: assert (SPh: sp < 18446744073709551616) by exact SPhi.
  all: assert (A1: 1 + c < 18446744073709551616) by (clear - BC SPh; llia).
  2-3: assert (LP: 1 <= Lc) by (destruct (N.eq_dec Lc 0) as [E|E];
         [exfalso; subst Lc; rewrite N.add_0_r in Zc; rewrite Zc in *; match goal with H: ~ (?a = _) |- _ => lazymatch a with getmem _ _ _ _ _ => fail | _ => exact (H eq_refl) end end | llia]).
  2-3: assert (A2: 1 + c < sp - 32 \/ sp <= 1 + c) by (left; clear - BC LP; llia).
  2: match goal with H: getmem _ _ 1 (_ [Ⓧ _ := _] [Ⓧ _ := _]) ?a = _ |- _ =>
         rewrite (z_mem_out sp mem a SPlo SPhi A1 A2) in H end.
  - assert (Lc = 0) by (destruct (N.eq_dec Lc 0) as [E|E]; [exact E | exfalso; apply (NFc 0); [llia | rewrite N.add_0_r; sassumption]]). subst Lc.
    splits; [exists 0; splits; first [llia | sreflexivity | (intros; llia) | (right; intros (i & I & _); llia)] | sreflexivity | sassumption |].
    intros a A O. apply z_mem_out; sassumption.
  - assert (Lc = 1).
    { destruct (N.lt_trichotomy Lc 1) as [LT|[EQ|GT]]; [llia | exact EQ |].
      exfalso. apply (NFc 1); [llia | rewrite N.add_comm; sassumption]. }
    exists 0. splits; first [llia | sreflexivity | sassumption | (rewrite N.add_0_r; reflexivity) | (intros; llia) |
      (intros a A O; apply z_mem_out; sassumption)].
  - exists 0. splits; first [llia | sreflexivity | sassumption | (apply msub_small; L64) | (apply z_mem; sassumption) | (rewrite N.add_0_r; reflexivity)].
Qed.

Lemma ss_case_15f314: ∀ sp mem raddr p c Ks Lc (s1:store) (t:list (exit*store)),
  ss_pre sp mem p c Ks Lc ->
  raddr < 18446744073709551616 -> p < 18446744073709551616 -> c < 18446744073709551616 ->
  models arm8typctx s1 ->
  ss_invs sp mem raddr p c Ks Lc Prop (fun _ P => P) (fun _ P => P) True s1 0x15f314 ->
  nextinv strspn_armv8.strspn_armv8 (ss_invs0 sp mem raddr p c Ks Lc) (ss_exits sp mem raddr p c Ks Lc) false ((Addr 0x15f314, s1) :: t).
Proof.
  intros sp mem raddr p c Ks Lc s1 t PRE0 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (j & JL & X1 & X5 & X6 & X0 & SP & X30 & SM).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & R0 & R1 & SPlo & SPhi & BP & BC).
  repeat arm8_step.
  all: clear MDL1 R0 R1.
  all: nrm.
  all: assert (CJ: c + j + 33 <= sp) by llia.
  all: rewrite (sm_out sp mem c j (s1 V_MEM64) (c + j)) in * by first [exact SM | L64 | (left; L64)].
  - assert (j = Lc) by (destruct (N.lt_ge_cases j Lc) as [LT|GE]; [exfalso; apply (NFc j LT); sassumption | llia]). subst j.
    exists 0. splits; first [llia | (rewrite N.add_0_r; reflexivity) | sassumption | sreflexivity | exact SM | (intros; llia)].
  - assert (JL2: j < Lc) by (destruct (N.lt_ge_cases j Lc) as [LT|GE]; [exact LT |
      exfalso; assert (j = Lc) by llia; subst j; match goal with H: ~ (?a = _) |- _ => lazymatch a with getmem _ _ _ mem _ => exact (H Zc) end end]).
    exists (j + 1). splits; first [llia | sreflexivity | sassumption |
      (match goal with |- ?x mod _ = _ => rewrite (N.mod_small x) by L64; llia end) |
      (apply sm_step; [exact SM | L64 | L64 | reflexivity | apply b_div_lt]) ].
Qed.

Lemma ss_case_15f340: ∀ sp mem raddr p c Ks Lc (s1:store) (t:list (exit*store)),
  ss_pre sp mem p c Ks Lc ->
  raddr < 18446744073709551616 -> p < 18446744073709551616 -> c < 18446744073709551616 ->
  models arm8typctx s1 ->
  ss_invs sp mem raddr p c Ks Lc Prop (fun _ P => P) (fun _ P => P) True s1 0x15f340 ->
  nextinv strspn_armv8.strspn_armv8 (ss_invs0 sp mem raddr p c Ks Lc) (ss_exits sp mem raddr p c Ks Lc) false ((Addr 0x15f340, s1) :: t).
Proof.
  intros sp mem raddr p c Ks Lc s1 t PRE0 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (k & L1 & KK & X1 & X0 & X3 & SP & X30 & EQ & OUT).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & R0 & R1 & SPlo & SPhi & BP & BC).
  repeat arm8_step.
  all: clear MDL1 R0 R1.
  all: nrm.
  all: subst Lc.
  all: assert (CJ: p + k + 33 <= sp) by llia.
  all: rewrite (OUT (p + k)) in * by first [L64 | (left; L64)].
  all: assert (C0: mem Ⓑ[c] <> 0) by (pose proof (NFc 0 ltac:(lia)) as C; rewrite N.add_0_r in C; exact C).
  - assert (KK2: k < Ks) by (destruct (N.lt_ge_cases k Ks) as [LT|GE]; [exact LT |
      exfalso; assert (k = Ks) by llia; subst k; apply C0; etransitivity; [symmetry; eassumption | exact Zp]]).
    exists (k + 1). splits; first [llia | sreflexivity | sassumption | exact OUT |
      (match goal with |- ?x mod _ = _ => rewrite (N.mod_small x) by L64; llia end) |
      (intros i I; destruct (N.lt_ge_cases i k); [apply EQ; llia | replace i with k by llia; sassumption]) ].
  - splits; [| sreflexivity | sassumption | exact OUT].
    exists k. splits.
    + llia.
    + rewrite N.mod_small by L64. reflexivity.
    + intros i I. exists 0. split; [llia|]. rewrite N.add_0_r. symmetry. apply EQ. exact I.
    + right. intros (i & I & E). assert (i = 0) by llia. subst i. rewrite N.add_0_r in E.
      match goal with H: ~ (?a = _) |- _ => lazymatch a with getmem _ _ _ mem (p + k) => apply H; symmetry; exact E end end.
Qed.

Lemma ss_case_15f360: ∀ sp mem raddr p c Ks Lc (s1:store) (t:list (exit*store)),
  ss_pre sp mem p c Ks Lc ->
  raddr < 18446744073709551616 -> p < 18446744073709551616 -> c < 18446744073709551616 ->
  models arm8typctx s1 ->
  ss_invs sp mem raddr p c Ks Lc Prop (fun _ P => P) (fun _ P => P) True s1 0x15f360 ->
  nextinv strspn_armv8.strspn_armv8 (ss_invs0 sp mem raddr p c Ks Lc) (ss_exits sp mem raddr p c Ks Lc) false ((Addr 0x15f360, s1) :: t).
Proof.
  intros sp mem raddr p c Ks Lc s1 t PRE0 W30 W0 W1 MDL1 PRE. hnf in PRE.
  destruct PRE as (k & KK & X3 & X0 & SP & X30 & IN & SM).
  pose proof PRE0 as (NFp & Zp & NFc & Zc & R0 & R1 & SPlo & SPhi & BP & BC).
  repeat arm8_step.
  all: clear MDL1 R0 R1.
  all: nrm.
  all: assert (CJ: p + k + 33 <= sp) by llia.
  all: rewrite (sm_out sp mem c Lc (s1 V_MEM64) (p + k)) in * by first [exact SM | L64 | (left; L64)].
  all: rewrite ?(msub_small 64 sp 32) in * by L64.
  all: pose proof (sm_test sp mem c Lc (s1 V_MEM64) (mem Ⓑ[p + k]) SM (b_div_lt _ _)) as [T1 T2].
  all: try (assert (KK2: k < Ks) by (destruct (N.lt_ge_cases k Ks) as [LT|GE]; [exact LT |
      exfalso; assert (k = Ks) by llia; subst k; match goal with H: ~ (?a = _) |- _ => lazymatch a with getmem _ _ _ ?m _ => is_var m; exact (H Zp) end end])).
  all: try (assert (k = Ks) by (destruct (N.lt_ge_cases k Ks) as [LT|GE]; [exfalso; apply (NFp k LT); sassumption | llia]); subst k).
  all: try match goal with H: _ mod 2 = 0 |- _ => specialize (T1 (proj2 (N.eqb_eq _ _) H)) end.
  all: try match goal with H: ~ (_ mod 2 = 0) |- _ => specialize (T2 (proj2 (N.eqb_neq _ _) H)) end.
  all: match goal with
    | |- (∃ K, _ /\ ?x mod _ = K /\ _) /\ _ =>
        splits; [| sreflexivity | sassumption | (intros a A O; apply (sm_out sp mem c Lc (s1 V_MEM64) a SM A O))];
        exists x; splits; [llia | (rewrite N.mod_small by L64; reflexivity) | exact IN | first [(left; reflexivity) | (right; exact T1)]]
    | |- ∃ _, _ =>
        exists (k + 1); splits; [llia | (match goal with |- ?x mod _ = _ => rewrite (N.mod_small x) by L64; llia end) |
          sassumption | sreflexivity | sassumption |
          (intros i I; destruct (N.lt_ge_cases i k); [apply IN; llia | replace i with k by llia; exact T2]) | exact SM]
    end.
Qed.

Theorem strspn_partial_correctness:
  ∀ prog s sp mem raddr p c Ks Lc t xs'
    (PRE0: ss_pre sp mem p c Ks Lc)
    (PROG: strspn_armv8.strspn_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15f2e8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c),
  satisfies_all prog (ss_invs0 sp mem raddr p c Ks Lc) (ss_exits sp mem raddr p c Ks Lc) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  pose proof (MDL R_X1 64 eq_refl) as W1. rewrite X1 in W1. simpl in W1.
  eapply satisfies_all_pmono with (p1:=strspn_armv8.strspn_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ss_invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START PRE0 W30 W0 W1.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strspn_armv8.welltyped. intro MDL1.
  clear - PRE MDL1 PRE0 W30 W0 W1. rename t1 into t.
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W30, W0, W1. clear WW.
  destruct_inv 64 PRE.
  - eapply ss_case_15f2e8; eassumption.
  - eapply ss_case_15f314; eassumption.
  - eapply ss_case_15f340; eassumption.
  - eapply ss_case_15f360; eassumption.
Qed.

(* SP is restored (ss_post) but is assigned, so it is not in this list. *)
Theorem strspn_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 :: R_X29 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates strspn_armv8.strspn_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

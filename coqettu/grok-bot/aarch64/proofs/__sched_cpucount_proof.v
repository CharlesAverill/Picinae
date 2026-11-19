(* __sched_cpucount -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, nested loop)

   SEMANTICS
   ---------
   musl's C source is

       int __sched_cpucount(size_t size, const cpu_set_t *set)
       {
           size_t i, j, cnt=0;
           const unsigned char *p = set;   (cast to bytes)
           for (i=0; i<size; i++) for (j=0; j<8; j++)
               if (p[i] & (1<<j)) cnt++;
           return cnt;
       }

   SPECIFICATION
   -------------
   CPU_COUNT_S (glibc/Linux man-pages): the number of CPUs (set bits) in the
   first size bytes of the set.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            __sched_cpucount at 0x50ef4 (ELF vaddr); 0x150ef4 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter, options --globalAddressing --typeCheck,
            project aarch64/ghidra2; see ../lifted/__sched_cpucount_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = size, X1 = set; X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x150f30): X0 = (the number of set
            bits in the bytes m[set], ..., m[set+size-1], addresses mod 2^64)
            mod 2^64 (the binary's 64-bit counter; the mod only matters for
            size >= 2^61).  Memory, SP, X30 and the AAPCS64 callee-saved
            registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import __sched_cpucount_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBits.
Import ARM8Notations.
Open Scope N.

(* Set bits among the low j bits of v. *)
Fixpoint bitsum (v:N) (j:nat) : N :=
  match j with O => 0 | S j' => bitsum v j' + (v >> N.of_nat j') mod 2 end.

(* Set bits in the first k bytes at p. *)
Fixpoint cpucnt (m:memory) (p:addr) (k:nat) : N :=
  match k with O => 0 | S k' => cpucnt m p k' + bitsum (m Ⓑ[p + N.of_nat k']) 8 end.

Lemma bitsum_S: ∀ v j, bitsum v (S j) = bitsum v j + (v >> N.of_nat j) mod 2.
Proof. reflexivity. Qed.

Lemma ashiftr32_small: ∀ x n, x < 2^31 -> ashiftr 32 x n = x >> n.
Proof.
  intros. rewrite ashiftr_nonneg; rewrite N.mod_small; try assumption; try reflexivity.
  1,2: eapply N.lt_trans; [eassumption|reflexivity].
Qed.

(* One step of the inner loop: asr w3,w4,w2 ; and w3,w3,#1 on a byte. *)
Lemma cpu_bit: ∀ b j, b < 2^8 -> (j < 8)%nat ->
  ashiftr 32 ((b >> 0) mod 2^32) ((N.of_nat j >> 0) mod 2^32 .& 31) mod 2 = (b >> N.of_nat j) mod 2.
Proof.
  intros b j B J. rewrite !N.shiftr_0_r.
  rewrite (N.mod_small b) by (eapply N.lt_trans; [eassumption|reflexivity]).
  rewrite (N.mod_small (N.of_nat j)) by lia.
  replace (N.of_nat j .& 31) with (N.of_nat j) by (do 8 (destruct j as [|j]; [reflexivity|]); lia).
  rewrite ashiftr32_small by (eapply N.lt_trans; [eassumption|reflexivity]). reflexivity.
Qed.

Theorem __sched_cpucount_nwc: ∀ s2 s1, __sched_cpucount_armv8 s1 = __sched_cpucount_armv8 s2.
Proof. reflexivity. Qed.

Theorem __sched_cpucount_welltyped: welltyped_prog arm8typctx __sched_cpucount_armv8.
Proof. Picinae_typecheck. Qed.

Theorem __sched_cpucount_preserves_memory:
  forall_endstates __sched_cpucount_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem __sched_cpucount_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates __sched_cpucount_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem __sched_cpucount_preserves_x30:
  forall_endstates __sched_cpucount_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr n p : N).
  Definition __sched_cpucount_post (s:store) :=
    s R_X0 = cpucnt mem p (N.to_nat n) mod 2^64 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x150ef4 => Inv 0 (s R_X0 = n /\ s R_X1 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x150f04 => Inv 0 (∃ k:nat, N.of_nat k <= n /\ n < 2^64 /\ p < 2^64 /\
                     s R_X1 = p ⊕ N.of_nat k /\ s R_X5 = n ⊕ p /\
                     s R_X0 = cpucnt mem p k mod 2^64 /\
                     s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x150f14 => Inv 0 (∃ (k j:nat), N.of_nat k < n /\ n < 2^64 /\ p < 2^64 /\ (j < 8)%nat /\
                     s R_X1 = p ⊕ N.of_nat k /\ s R_X5 = n ⊕ p /\
                     s R_X4 = mem Ⓑ[p + N.of_nat k] /\ s R_X2 = N.of_nat j /\
                     s R_X0 = (cpucnt mem p k + bitsum (mem Ⓑ[p + N.of_nat k]) j) mod 2^64 /\
                     s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x150f30 => Post 0 (__sched_cpucount_post s)
    | _ => NoInv
    end.
  Definition __sched_cpucount_exits := make_exits 0 __sched_cpucount_armv8 invs.
  Definition __sched_cpucount_invs := make_invs 0 __sched_cpucount_armv8 invs.
End Invariants.

Theorem __sched_cpucount_partial_correctness:
  ∀ prog s sp mem raddr n p t xs'
    (PROG: __sched_cpucount_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x150ef4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = n) (X1: s R_X1 = p),
  satisfies_all prog (__sched_cpucount_invs sp mem raddr n p) (__sched_cpucount_exits sp mem raddr n p) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=__sched_cpucount_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold __sched_cpucount_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply __sched_cpucount_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as N64. pose proof (MDL1 R_X1 64 eq_refl) as P64.
    rewrite X0 in N64. rewrite X1 in P64.
    repeat arm8_step.
    exists 0%nat. splits; try assumption; try reflexivity.
    + lia.
    + cbn [N.of_nat]. rewrite N.add_0_r, N.mod_small; [reflexivity|assumption].
  - destruct PRE as (k & KLE & N64 & P64 & X1 & X5 & X0 & MEM & SP & X30).
    assert (KM: N.of_nat k mod 2^64 = N.of_nat k) by (apply N.mod_small; lia).
    repeat arm8_step; rewrite KM in BC.
    + apply N.eqb_eq in BC. splits; try assumption.
      rewrite <- BC, Nat2N.id. assumption.
    + apply N.eqb_neq in BC. exists k, 0%nat. splits; try assumption; try reflexivity; try lia.
      rewrite X0. cbn [bitsum]. rewrite N.add_0_r. reflexivity.
  - destruct PRE as (k & j & KLT & N64 & P64 & JLT & X1 & X5 & X4 & X2 & X0 & MEM & SP & X30).
    repeat arm8_step; rewrite cpu_bit by (apply byte_lt8 || assumption).
    + apply N.eqb_eq in BC. assert (J7: j = 7%nat) by lia. subst j.
      exists (S k). splits; try assumption.
      * lia.
      * rewrite Nat2N.inj_succ. f_equal. lia.
      * change (cpucnt mem p (S k)) with (cpucnt mem p k + bitsum (mem Ⓑ[p + N.of_nat k]) 8).
        rewrite (bitsum_S _ 7). rewrite N.add_assoc. reflexivity.
    + apply N.eqb_neq in BC. exists k, (S j). splits; try assumption; try reflexivity.
      * lia.
      * rewrite Nat2N.inj_succ, N.mod_small by lia. lia.
      * rewrite bitsum_S, N.add_assoc. reflexivity.
Qed.

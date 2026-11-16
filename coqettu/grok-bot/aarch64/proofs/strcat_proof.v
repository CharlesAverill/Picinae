(* strcat -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls strlen, strcpy -> stpcpy)

   SEMANTICS
   ---------
   musl's src/string/strcat.c:
       char *strcat(char *restrict dest, const char *restrict src) {
           strcpy(dest + strlen(dest), src);
           return dest;
       }
   compiled as a 48-byte frame (stp x29,x30,[sp,#-48]! / str x19 / str x1),
   bl strlen (0x15efa8), bl strcpy (0x15eccc, which calls __stpcpy 0x15e950),
   mov x0,x19 and the frame restore.  All three callees are re-proved here
   inside the combined program strcat_prog.

   SPECIFICATION (man 3 strcat, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <string.h>
            char *strcat(char *restrict dst, const char *restrict src);
     DESCRIPTION
            This function catenates the string pointed to by src, after the
            string pointed to by dst (overwriting its terminating null byte).
            The programmer is responsible for allocating a destination buffer
            large enough, that is, strlen(dst) + strlen(src) + 1.
     RETURN VALUE
            strcat() returns dst.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            strcat at 0x5eb98 (ELF vaddr); 0x15eb98 in Ghidra (image base 0x100000);
            callees strlen 0x5efa8, strcpy 0x5eccc, stpcpy 0x5e950 (+0x100000 in Ghidra)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/strcat_armv8.v,
            strcpy_armv8.v, stpcpy_armv8.v, strlen_armv8.v (combined as strcat_prog).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dst (d), X1 = src (q), SP = sp, X29 = x29, X19 = x19,
            X30 = return address raddr; memory mem.
   PRECONDITION (strcat_pre sp mem d q Ld Lq), stated explicitly:
            - d holds a string of length Ld: bytes d..d+Ld-1 nonzero, byte d+Ld = 0;
            - q holds a string of length Lq: bytes q..q+Lq-1 nonzero, byte q+Lq = 0;
            - 80 <= sp < 2^64, and both the destination range d..d+Ld+Lq and
              the source range q..q+Lq lie strictly below sp-80, i.e. below all
              stack frames used by strcat (sp-48..sp) and strcpy (sp-80..sp-48);
            - the written range d+Ld..d+Ld+Lq does not overlap the source
              (q+Lq < d+Ld or d+Ld+Lq < q).
            The C standard makes overlapping src/dst undefined behaviour
            (restrict), and a destination buffer overlapping the callee frames
            is not valid caller memory, so this precondition only excludes
            undefined behaviour.  It is needed because strcpy reloads its saved
            X30 from its frame after the copy.
   Output:  If execution reaches strcat's RET (0x15ebc8), then with
            C = mem with x29, raddr, x19, q stored at sp-48, sp-40, sp-32, sp-8
            and F = C with sp-48, 0x15ebbc, d stored at sp-80, sp-72, sp-64
            (the two saved frames):
            memory = bcp F (d+Ld) q (Lq+1)  (bytes q[0..Lq], terminator
            included, copied in order to d+Ld; see lib/GrokStr.v),
            X0 = d, SP = sp, X29 = x29, X30 = raddr, X19 = x19.
            Partial correctness only.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require strcat_armv8 strcpy_armv8 stpcpy_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame.
Import ARM8Notations.
Open Scope N.

Definition strcat_prog : program :=
  updateall2 (updateall2 (updateall2 strcat_armv8.strcat_armv8 strcpy_armv8.strcpy_armv8)
    stpcpy_armv8.stpcpy_armv8) strlen_armv8.strlen_armv8.

Ltac contains_tac SC :=
  repeat first
  [ exact SC | discriminate SC | (rewrite SC; reflexivity)
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].

Lemma strcat_prog_contains2: strcpy_armv8.strcpy_armv8 ⊆2 strcat_prog.
Proof.
  intros s a insn SC. unfold strcat_prog, updateall2, updateall, strlen_armv8.strlen_armv8, stpcpy_armv8.stpcpy_armv8.
  contains_tac SC.
Qed.

Theorem strcat_prog_welltyped: welltyped_prog arm8typctx strcat_prog.
Proof.
  intros s a. unfold strcat_prog, updateall2, updateall.
  destruct (strlen_armv8.strlen_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (strlen_armv8.welltyped s a) as WT. rewrite T0 in WT. exact WT.
  destruct (stpcpy_armv8.stpcpy_armv8 s a) as [[sz q]|] eqn:T1.
    pose proof (stpcpy_armv8.welltyped s a) as WT. rewrite T1 in WT. exact WT.
  destruct (strcpy_armv8.strcpy_armv8 s a) as [[sz q]|] eqn:T2.
    pose proof (strcpy_armv8.welltyped s a) as WT. rewrite T2 in WT. exact WT.
    apply strcat_armv8.welltyped.
Qed.

Lemma strcat_prog_mono: ∀ prog, strcat_armv8.strcat_armv8 ⊆2 prog -> strcpy_armv8.strcpy_armv8 ⊆2 prog ->
  stpcpy_armv8.stpcpy_armv8 ⊆2 prog -> strlen_armv8.strlen_armv8 ⊆2 prog -> strcat_prog ⊆2 prog.
Proof.
  intros prog P3 P2 P1 P0. unfold strcat_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono.
  rewrite <- (updateall2_subset _ _ P1). apply updateall2_mono.
  rewrite <- (updateall2_subset _ _ P2). apply updateall2_mono. exact P3.
Qed.

Definition frame_mem (sp mem raddr x29 x19 : N) := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19].
Definition cat_frame (sp mem raddr q x29 x19 : N) := mem [Ⓠ sp ⊖ 48 := x29] [Ⓠ sp ⊖ 40 := raddr] [Ⓠ sp ⊖ 32 := x19] [Ⓠ sp ⊖ 8 := q].
Definition strcpy_post (sp mem raddr d q x29 x19 : N) (s:store) :=
  ∃ k, bnz (frame_mem sp mem raddr x29 x19) d q k /\
       getmem 64 LittleE 1 (bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat k)) (q + k) = 0 /\
       s V_MEM64 = bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat (k+1)) /\ s R_X0 = d /\ s R_SP = sp /\
       s R_X29 = bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 32] /\
       s R_X30 = bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 24] /\
       s R_X19 = bcp (frame_mem sp mem raddr x29 x19) d q (N.to_nat (k+1)) Ⓠ[sp ⊖ 16].
(* strcat precondition: d and q are NUL-terminated strings of lengths Ld and Lq,
   the destination range [d, d+Ld+Lq] and the source [q, q+Lq] lie strictly below the
   stack frames (sp-80 and up), and the written range [d+Ld, d+Ld+Lq] does not overlap
   the source (overlap is undefined behaviour in C). *)
Definition strcat_pre (sp mem d q Ld Lq : N) :=
  nilfree mem d Ld /\ mem Ⓑ[d + Ld] = 0 /\ nilfree mem q Lq /\ mem Ⓑ[q + Lq] = 0 /\
  80 <= sp /\ sp < 2^64 /\ d + Ld + Lq + 1 <= sp - 80 /\ q + Lq + 1 <= sp - 80 /\
  (q + Lq < d + Ld \/ d + Ld + Lq < q).
(* strcat post: memory = the frame-written memory F with bytes q[0..Lq] copied to d+Ld;
   X0 = d; SP, X29, X30, X19 restored to their entry values. *)
Definition strcat_post (sp mem raddr d q x29 x19 Ld Lq : N) (s:store) :=
  let C := cat_frame sp mem raddr q x29 x19 in
  let F := frame_mem (sp ⊖ 48) C 0x15ebbc (sp ⊖ 48) d in
  s V_MEM64 = bcp F (d + Ld) q (N.to_nat (Lq+1)) /\
  s R_X0 = d /\ s R_SP = sp /\ s R_X29 = x29 /\ s R_X30 = raddr /\ s R_X19 = x19.

Section Invariants.
  Variables (sp mem raddr d q x29 x19 Ld Lq : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strcat *)
    | 0x15eb98 => Inv 3 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15ebc8 => Post 3 (strcat_post sp mem raddr d q x29 x19 Ld Lq s)
    (* strcpy *)
    | 0x15eccc => Inv 2 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15ecec => Post 2 (strcpy_post sp mem raddr d q x29 x19 s)
    (* stpcpy *)
    | 0x15e950 => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e95c => Inv 1 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e990 => Inv 1 (∃ k, msub 64 q d mod 8 = 0 /\ s R_X4 = K8 /\ s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e9ac => Inv 1 (∃ k, s R_X0 = (d + k) mod 2^64 /\ s R_X1 = (q + k) mod 2^64 /\ bnz mem d q k /\
                         s V_MEM64 = bcp mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15e9bc => Post 1 (∃ k, bnz mem d q k /\ getmem 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k) = 0 /\
                          s V_MEM64 = bcp mem d q (N.to_nat (k+1)) /\
                          s R_X0 = (d + k) mod 2^64 /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    (* strlen (string at d) *)
    | 0x15efa8 => Inv 0 (s R_X0 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15efb4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15efd8 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s R_X4 = 0xfefefefefefefeff /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15eff4 => Inv 0 (∃ k, k < 2^64 /\ s R_X0 = d /\ s R_X1 = d ⊕ k /\ nilfree mem d k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | 0x15f000 => Post 0 (∃ k, k < 2^64 /\ s R_X0 = k /\ nilfree mem d k /\ mem Ⓑ[d + k] = 0 /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ s R_X19 = x19)
    | _ => NoInv
    end.
  Definition exits0 := make_exits 0 strcat_prog invs.
  Definition invs0 := make_invs 0 strcat_prog invs.
  Definition exits1 := make_exits 1 strcat_prog invs.
  Definition invs1 := make_invs 1 strcat_prog invs.
  Definition exits2 := make_exits 2 strcat_prog invs.
  Definition invs2 := make_invs 2 strcat_prog invs.
  Definition exits3 := make_exits 3 strcat_prog invs.
  Definition invs3 := make_invs 3 strcat_prog invs.
End Invariants.

Ltac al3 := match goal with AL: msub 64 ?q ?d mod 8 = 0 |- msub 3 ?q ?d = 0 =>
  transitivity (msub 64 q d mod 2^3); [rewrite msub_mod_pow2; reflexivity | exact AL] end.
Ltac modeq := rewrite ?N.Div0.add_mod_idemp_r, ?N.Div0.add_mod_idemp_l; f_equal; lia.

Theorem strlen_correct_in_strcat:
  ∀ prog s t xs'
    (P: strcat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15efa8, s))
    (MDL: models arm8typctx s),
  ∀ q Ld Lq,
  satisfies_all prog
    (invs0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q (s R_X29) (s R_X19) Ld Lq)
    (exits0 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) q (s R_X29) (s R_X19) Ld Lq)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (p := s R_X0).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = p) by reflexivity.
  set (x29 := s R_X29). set (x19 := s R_X19).
  assert (X29: s R_X29 = x29) by reflexivity. assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr p x29 x19.
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (X0 & MEM & SP & X30 & X29 & X19).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    repeat arm8_step.
    exists 0. repeat split; try assumption.
    all: first [ apply nilfree_0 | rewrite N.add_0_r; symmetry; apply N.mod_small; exact P64 ].
  - (* byte loop until X1 is 8-aligned *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists k. repeat split; assumption.
    + apply cbnz32_true in BC0; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC0; [|apply byte_lt32].
      exists k. repeat split; assumption.
  - (* aligned word loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & X4 & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists ((k+8) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le.
      intros i Hi. destruct (N.lt_ge_cases i k). apply NF; assumption.
      pose proof (haszero_test_zero _ (qword_lt64 mem (p+k)) BC (i-k) ltac:(lia)) as H8.
      rewrite byte_of_qword in H8 by lia. replace (p + k + (i - k)) with (p + i) in H8 by lia.
      exact H8.
    + exists k. repeat split; assumption.
  - (* final byte loop *)
    destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + apply cbnz32_true in BC; [|apply byte_lt32].
      exists ((k+1) mod 2^64). repeat split; try assumption.
      apply mp2_mod_lt. apply ptr_adv.
      eapply nilfree_mono. apply mod64_le. apply nilfree_succ; assumption.
    + apply cbnz32_false in BC; [|apply byte_lt32].
      exists k. repeat split; assumption.
Qed.

Theorem stpcpy_correct_in_strcat:
  ∀ prog s t xs' Ld Lq
    (P: strcat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e950, s))
    (MDL: models arm8typctx s),
  satisfies_all prog
    (invs1 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X29) (s R_X19) Ld Lq)
    (exits1 (s R_SP) (s V_MEM64) (s R_X30) (s R_X0) (s R_X1) (s R_X29) (s R_X19) Ld Lq)
    (xs'::t).
Proof.
  intros.
  set (sp := s R_SP). set (mem := s V_MEM64). set (raddr := s R_X30). set (d := s R_X0).
  set (q := s R_X1). set (x29 := s R_X29). set (x19 := s R_X19).
  assert (SP: s R_SP = sp) by reflexivity. assert (MEM: s V_MEM64 = mem) by reflexivity.
  assert (X30: s R_X30 = raddr) by reflexivity. assert (X0: s R_X0 = d) by reflexivity.
  assert (X1: s R_X1 = q) by reflexivity. assert (X29: s R_X29 = x29) by reflexivity.
  assert (X19: s R_X19 = x19) by reflexivity.
  clearbody sp mem raddr d q x29 x19.
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
    pose proof (MDL1 R_X0 64 eq_refl) as BD. pose proof (MDL1 R_X1 64 eq_refl) as BQ.
    rewrite X0 in BD. rewrite X1 in BQ.
    repeat arm8_step.
    + exists 0. apply N.eqb_eq in BC. split.
      * transitivity (msub 64 q d mod 2^3).
        rewrite msub_mod_pow2. reflexivity. apply xor_mod8. exact BC.
      * repeat split; rewrite ?N.add_0_r, ?N.mod_small by assumption; try assumption; try reflexivity.
        intros i I. lia.
    + exists 0.
      repeat split; rewrite ?N.add_0_r, ?N.mod_small by assumption; try assumption; try reflexivity.
      intros i I. lia.
  - destruct PRE as (k & AL & X0 & X1 & NZ & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists k. split. al3. split. reflexivity. repeat split; assumption.
    + exists k. apply N.eqb_eq in BC0. repeat split; try assumption. rewrite bcp_succ. reflexivity.
    + exists (k+1). apply N.eqb_neq in BC0. split. al3. repeat split; try assumption.
      * modeq.
      * modeq.
      * apply bnz_succ; assumption.
      * rewrite bcp_succ. reflexivity.
  - destruct PRE as (k & AL & X4 & X0 & X1 & NZ & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    + exists (k+8). apply N.eqb_eq in BC. split. al3. split. reflexivity. repeat split; try assumption.
      * modeq.
      * modeq.
      * apply (bnz_word mem d q k _ AL eq_refl); [|exact NZ].
        apply haszero_none'; [apply getmem_bound | exact BC].
      * rewrite bcp_word8 by exact AL. reflexivity.
    + exists k. repeat split; assumption.
  - destruct PRE as (k & X0 & X1 & NZ & MEM & SP & X30 & X29 & X19).
    repeat arm8_step.
    all: pose proof (getmem_bound 64 LittleE 1 (bcp mem d q (N.to_nat k)) (q + k)) as B;
         change (2^(1*8)) with (2^8) in B;
         destruct (byte_test _ _ B BC) as [[T NZK] | [T ZK]]; try discriminate T.
    + exists (k+1). repeat split; try assumption.
      * modeq.
      * modeq.
      * apply bnz_succ; assumption.
      * rewrite bcp_succ. reflexivity.
    + exists k. repeat split; try assumption. rewrite bcp_succ. reflexivity.
Qed.

Theorem strcpy_correct_in_strcat:
  ∀ prog s sp mem raddr d q x29 x19 Ld Lq t xs'
    (P: strcat_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eccc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X29: s R_X29 = x29) (X19: s R_X19 = x19),
  satisfies_all prog (invs2 sp mem raddr d q x29 x19 Ld Lq) (exits2 sp mem raddr d q x29 x19 Ld Lq) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs2, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as D64. rewrite X0 in D64. simpl in D64.
  do 5 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcat_prog_welltyped. intro MDL2.
  eapply (perform_call 1). reflexivity.
  intros. eapply stpcpy_correct_in_strcat with (Ld:=Ld) (Lq:=Lq); first [ exact (fun _ _ _ H => H) | eassumption ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcat_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' SP64 D64 X1.
  rename MDL' into MDL. rename s' into s.
  destruct_inv 64 PRE.
  destruct PRE as (k & NZ & Z & MEMc & R0 & SPc & X30c & X29c & X19c).
  repeat arm8_step.
  rewrite X1 in *. exists k. unfold frame_mem, strcpy_post.
  repeat split; try assumption; try reflexivity. all: try (apply N.mod_small; exact SP64).
Qed.

Ltac L64 := change (2^64) with 18446744073709551616 in *; lia.

Ltac memsimp := repeat first [rewrite getmem_setmem by L64 | rewrite getmem_setmem_below by L64 | rewrite getmem_setmem_above by L64].

Lemma first_zero_unique: ∀ (f g: N -> N) L1 L2,
  (∀ i, i < L1 -> f i ≠ 0) -> f L1 = 0 -> (∀ i, i < L2 -> g i ≠ 0) -> g L2 = 0 ->
  (∀ i, i <= L1 -> g i = f i) -> L1 = L2.
Proof.
  intros f g L1 L2 F1 F0 G1 G0 E.
  destruct (N.lt_trichotomy L1 L2) as [H|[H|H]]; [|exact H|].
  - exfalso. apply (G1 L1 H). rewrite E by lia. exact F0.
  - exfalso. apply (F1 L2 H). rewrite <- E by lia. exact G0.
Qed.

Theorem strcat_partial_correctness:
  ∀ prog s sp mem raddr d q x29 x19 Ld Lq t xs'
    (PRE0: strcat_pre sp mem d q Ld Lq)
    (P3: strcat_armv8.strcat_armv8 ⊆2 prog) (P2: strcpy_armv8.strcpy_armv8 ⊆2 prog)
    (P1: stpcpy_armv8.stpcpy_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15eb98, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X29: s R_X29 = x29) (X19: s R_X19 = x19),
  satisfies_all prog (invs3 sp mem raddr d q x29 x19 Ld Lq) (exits3 sp mem raddr d q x29 x19 Ld Lq) (xs'::t).
Proof.
  intros.
  assert (PP: strcat_prog ⊆2 prog) by (apply strcat_prog_mono; assumption).
  eapply satisfies_all_pmono with (p1:=strcat_prog). exact PP.
    intros a s1 t1 EXIT NOCODE. unfold invs3, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X29 X19 START PRE0. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_prog_welltyped. intro MDL1.
  clear - PRE MDL1 PRE0. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30 & X29 & X19).
  pose proof (MDL1 R_SP 64 eq_refl) as SP64. rewrite SP in SP64. simpl in SP64.
  pose proof (MDL1 R_X0 64 eq_refl) as D64. rewrite X0 in D64. simpl in D64.
  pose proof (MDL1 R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL1 R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL1 R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL1 R_X1 64 eq_refl) as Q64. rewrite X1 in Q64. simpl in Q64.
  do 6 arm8_step.
  set (s2 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcat_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply strlen_correct_in_strcat with (q := q) (Ld:=Ld) (Lq:=Lq); first [ exact (fun _ _ _ H => H) | eassumption ].
  reflexivity.
  intros.
  unfold s2 in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcat_prog_welltyped.
  clearbody s2.
  clear - PRE MDL' SP64 D64 Q64 X0 PRE0 W29 W30 W19.
  rename MDL' into MDL. rename s' into s0.
  destruct_inv 64 PRE.
  destruct PRE as (L & LLT & R0 & NF & ZL & MEM & SP & X30 & X29 & X19).
  rename SP into SP1. rename MEM into MEM1.
  do 4 arm8_step.
  rewrite (N.mod_small q) by exact Q64.
  set (s3 := update _ _ _).
  eapply models_after_steps. eassumption. apply strcat_prog_welltyped. intro MDL3.
  eapply (perform_call 2). reflexivity.
  intros. eapply strcpy_correct_in_strcat with (Ld:=Ld) (Lq:=Lq); first [ exact (fun _ _ _ H => H) | eassumption | reflexivity ].
  reflexivity.
  intros.
  unfold s3 in PRE. unfold strcpy_post, frame_mem in PRE. psimpl in PRE.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply strcat_prog_welltyped.
  clearbody s3.
  clear - PRE MDL' SP64 D64 Q64 NF ZL LLT SP1 MEM1 PRE0 W29 W30 W19.
  rename MDL' into MDL0. rename s' into s4.
  destruct_inv 64 PRE.
  destruct PRE as (k & NZ & Z & MEM & R0 & SP & X29 & X30 & X19).
  destruct PRE0 as (NF0 & Z0 & NFq & Zq & SP80 & SPlt & BD & BQ & DISJ).
  assert (WW: ∀ x, x < N.pos (2^64) -> x < 18446744073709551616) by (intros; assumption).
  apply WW in W29, W30, W19. clear WW SP64 D64 Q64.
  change (2^64) with 18446744073709551616 in *.
  assert (MS: ∀ x y, y <= x -> x < 18446744073709551616 -> msub 64 x y = x - y) by (intros; apply msub_small; assumption).
  unfold frame_mem in *.
  rewrite !(MS sp) in * by lia. rewrite !(MS (sp - 48)) in * by lia.
  replace (sp - 48 - 32) with (sp - 80) in * by lia.
  replace (sp - 48 - 24) with (sp - 72) in * by lia.
  replace (sp - 48 - 16) with (sp - 64) in * by lia.
  set (C := mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 32 := x19] [Ⓠ sp - 8 := q]) in *.
  set (F := C [Ⓠ sp - 80 := sp - 48] [Ⓠ sp - 72 := 1436604] [Ⓠ sp - 64 := d]) in *.
  assert (CB: ∀ a, a + 1 <= sp - 80 -> C Ⓑ[a] = mem Ⓑ[a]).
  { intros a A. unfold C. rewrite !getmem_setmem_above by L64. reflexivity. }
  assert (FB: ∀ a, a + 1 <= sp - 80 -> F Ⓑ[a] = mem Ⓑ[a]).
  { intros a A. unfold F. rewrite !getmem_setmem_above by L64. apply CB, A. }
  assert (LE: Ld = L).
  { apply (first_zero_unique (fun i => mem Ⓑ[d+i]) (fun i => C Ⓑ[d+i])); cbv beta; try assumption.
    intros i I. apply CB. lia. }
  subst L.
  assert (EQ: (d + Ld) mod 18446744073709551616 = d + Ld) by (apply N.mod_small; lia).
  rewrite EQ in *.
  assert (KE: Lq = k).
  { apply (first_zero_unique (fun i => mem Ⓑ[q+i]) (fun i => bcp F (d+Ld) q (N.to_nat i) Ⓑ[q+i])); cbv beta; try assumption.
    intros i I. rewrite <- FB by lia.
    destruct DISJ as [DJ|DJ].
    - apply bcp_read_below; rewrite ?N2Nat.id; L64.
    - apply bcp_read_above; rewrite ?N2Nat.id; L64. }
  subst k.
  set (M := bcp F (d + Ld) q (N.to_nat (Lq + 1))) in *.
  assert (MQ: ∀ a, sp - 80 <= a -> a + 8 <= sp -> M Ⓠ[a] = F Ⓠ[a]).
  { intros a A1 A2. unfold M. apply bcp_read_above; rewrite ?N2Nat.id; L64. }
  assert (R72: M Ⓠ[sp - 72] = 1436604).
  { rewrite MQ by lia. unfold F. rewrite getmem_setmem_above by L64. rewrite getmem_setmem by L64. reflexivity. }
  assert (R80: M Ⓠ[sp - 80] = sp - 48).
  { rewrite MQ by lia. unfold F. rewrite !getmem_setmem_above by L64. rewrite getmem_setmem by L64. apply N.mod_small. L64. }
  assert (R64: M Ⓠ[sp - 64] = d).
  { rewrite MQ by lia. unfold F. rewrite getmem_setmem by L64. apply N.mod_small. L64. }
  assert (R48: M Ⓠ[sp - 48] = x29).
  { rewrite MQ by lia. unfold F, C. memsimp. apply N.mod_small. L64. }
  assert (R40: M Ⓠ[sp - 40] = raddr).
  { rewrite MQ by lia. unfold F, C. memsimp. apply N.mod_small. L64. }
  assert (R32: M Ⓠ[sp - 32] = x19).
  { rewrite MQ by lia. unfold F, C. memsimp. apply N.mod_small. L64. }
  rewrite R72 in *. rewrite R80 in *. rewrite R64 in *.
  repeat arm8_step.
  unfold frame_mem, cat_frame. rewrite !(MS sp) by lia. rewrite !(MS (sp - 48)) by lia.
  replace (sp - 48 - 32) with (sp - 80) by lia.
  replace (sp - 48 - 24) with (sp - 72) by lia.
  replace (sp - 48 - 16) with (sp - 64) by lia.
  replace (8 + (sp - 48)) with (sp - 40) by lia.
  replace (16 + (sp - 48)) with (sp - 32) by lia.
  replace (48 + (sp - 48)) with sp by lia.
  splits; try assumption; reflexivity.
Qed.

(* lfind -- linear search of an array

   SEMANTICS
   ---------
   lfind(key, base, nmemb, size, compar) scans base[0], base[1], ... and calls
   compar(key, &base[i]) on each element, returning the first element for which
   compar returns 0, or NULL after *nmemb elements.  It re-reads *nmemb on each
   iteration.  Like bsearch, it is a NON-LEAF function that calls compar
   through a function pointer (CALL R13).  The comparator is modeled exactly as
   in amd64_bsearch_proof.v: arbitrary code cp at every address outside lfind,
   a comparator entry at the fixed address C, and the contract
   lfind_cmp_contract, which perform_call applies at the call site.

   SPECIFICATION (man 3 lsearch, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <search.h>
            void *lfind(const void *key, const void *base, size_t *nmemb,
                     size_t size, int(*compar)(const void *, const void *));

     DESCRIPTION
            lfind() and lsearch() perform a linear search for key in the array base
            which has *nmemb elements of size bytes each.  The comparison  function
            referenced  by  compar is expected to have two arguments which point to
            the key object and to an array member, in that order, and which returns
            zero if the key object matches the array member, and nonzero otherwise.

     RETURN VALUE
            lfind() returns a pointer to a matching member of the array, or NULL if
            no match is found.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol lfind at 0x220d20 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see lfind_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = key, RSI = base, RDX = nmembp (pointer to size_t), RCX = size,
            R8 = compar = C; RSP = sp; N = m[nmembp] (8 bytes).
            Let elt i = base + i*size (mod 2^64).
   Preconditions:  *nmembp lies outside lfind's 64-byte stack frame below sp;
            N < 2^64 - 1; and cp meets lfind_cmp_contract.
   Output:  On return, RSP = sp; RBX, RBP and R12-R15 have their entry values;
            memory differs from m only in the frame; and either
              RAX = elt i where i < N is the FIRST index with cmp key (elt i) = 0, or
              RAX = 0 (NULL) and cmp key (elt i) <> 0 for every i < N.
            This is stronger than the man page, which allows any match.
            (Partial correctness.)
 *)

Require Import Picinae_amd64.
Require Import lfind_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem lfind_nwc: forall s2 s1, lfind_amd64 s1 = lfind_amd64 s2.
Proof. reflexivity. Qed.

Theorem lfind_welltyped: welltyped_prog x64typctx lfind_amd64.
Proof. Picinae_typecheck. Qed.

(* lfind saves and restores the callee-saved registers; see the Post 1 invariant. *)

Definition C := 0x10000000.      (* the comparator's fixed entry address *)
Definition RET_SITE := 2231654.  (* return address of the CALL R13 *)

Definition lfind_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match lfind_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma lfind_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (lfind_with cp).
Proof.
  intros cp WT s a. unfold lfind_with.
  pose proof (lfind_welltyped_lifted s a) as H.
  destruct (lfind_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

Section Invariants.
  Variable cmp : N -> N -> Z.
  Variable sp : N.
  Variable mem : memory.
  Variable key base nmembp size : N.
  Variable rbx rbp r12 r13 r14 r15 : N.

  Definition nmemb := mem Ⓠ[nmembp].
  Definition elt (i:N) := base ⊕ i * size.

  Definition outside (M:memory) :=
    forall a, ~ (msub 64 a (sp ⊖ 64) < 64) -> M Ⓑ[a] = mem Ⓑ[a].

  Definition frame_ok (M:memory) :=
    M Ⓠ[sp ⊖ 48] = rbx /\ M Ⓠ[sp ⊖ 40] = rbp /\ M Ⓠ[sp ⊖ 32] = r12 /\
    M Ⓠ[sp ⊖ 24] = r13 /\ M Ⓠ[sp ⊖ 16] = r14 /\ M Ⓠ[sp ⊖ 8] = r15 /\
    M Ⓠ[nmembp] = nmemb /\ outside M.

  Definition result_ok (r:N) :=
    (exists i, i < nmemb /\ r = elt i /\ cmp key (elt i) = 0%Z /\
               forall j, j < i -> cmp key (elt j) <> 0%Z) \/
    (r = 0 /\ forall i, i < nmemb -> cmp key (elt i) <> 0%Z).

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 268435456 => Inv 0 (s R_RDI = key /\ s R_RSI = base /\ s R_RSP = sp /\
                          s V_MEM64 = mem /\ mem Ⓠ[sp] = RET_SITE /\
                          s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                          s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    | 2231654 => Post 0 (toZ 32 (s R_RAX mod 2^32) = cmp key base /\ s R_RSP = sp ⊕ 8 /\
                         s V_MEM64 = mem /\
                         s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                         s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    | 2231584 => Inv 1 (s R_RSP = sp /\ s V_MEM64 = mem /\ s R_RDI = key /\ s R_RSI = base /\
                        s R_RDX = nmembp /\ s R_RCX = size /\ s R_R8 = C /\
                        s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                        s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    | 2231645 => Inv 1 (exists i,
                   s R_RSP = sp ⊖ 56 /\ s R_R14 = key /\ s R_R13 = C /\ s R_RBP = nmembp /\
                   s R_R15 = size /\ s R_RBX = i /\ s R_R12 = elt i /\ i < nmemb /\
                   (forall j, j < i -> cmp key (elt j) <> 0%Z) /\
                   frame_ok (s V_MEM64))
    | 2231681 => Post 1 (outside (s V_MEM64) /\ s R_RSP = sp /\
                   s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                   s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                   result_ok (s R_RAX))
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (lfind_with cp) invs.
  Definition invs0 cp := make_invs 0 (lfind_with cp) invs.
  Definition exits1 cp := make_exits 1 (lfind_with cp) invs.
  Definition invs1 cp := make_invs 1 (lfind_with cp) invs.
End Invariants.

Section FrameLemmas.
  Variable sp : N.
  Variable mem : memory.


  Lemma outside_setmem8:
    forall M x v, outside sp mem M -> 8 <= x <= 64 -> outside sp mem (M [Ⓠ sp ⊖ x := v]).
  Proof.
    intros M x v O X a NA. rewrite byte_setmem_cases by (discriminate || reflexivity).
    destruct (N.ltb_spec (msub 64 a (sp ⊖ x)) 8) as [H|H].
      exfalso. apply NA. unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
      apply O, NA.
  Qed.

  (* *nmemb lies outside the frame, so frame stores don't change it. *)
  Lemma nmemb_frame:
    forall (M:memory) nmembp x v, sp < 2^64 -> 8 <= x <= 64 ->
    ~ overlap 64 nmembp 8 (sp ⊖ 64) 64 ->
    (M [Ⓠ sp ⊖ x := v]) Ⓠ[nmembp] = M Ⓠ[nmembp].
  Proof.
    intros M nmembp x v SPB X NO. apply getmem_noverlap. intros [i [j [I [J E]]]].
    apply NO. exists i, (64 - x + j). split; [exact I|]. split; [lia|].
    rewrite E. unfold msub. change (2^64) with 18446744073709551616 in *. lia.
  Qed.
  Lemma slot64_frame:
    forall (M:memory) v k, sp < 2^64 -> 8 <= k <= 56 ->
    (M [Ⓠ sp ⊖ 64 := v]) Ⓠ[sp ⊖ k] = M Ⓠ[sp ⊖ k].
  Proof.
    intros M v k SPB K. apply getmem_noverlap. intros [i [j [I [J E]]]].
    unfold msub in E. change (2^64) with 18446744073709551616 in *. lia.
  Qed.
End FrameLemmas.

Lemma toZ32_zero: forall y, y < 2^32 -> (toZ 32 y = 0%Z <-> y = 0).
Proof.
  intros y Y. split; intro H.
  - destruct (N.lt_ge_cases y (2^31)) as [L|L].
      rewrite (proj1 (toZ_nonneg 32 y)) in H by (rewrite N.mod_small; assumption).
      rewrite N.mod_small in H by assumption. lia.
      assert (NEG: Z.lt (toZ 32 y) 0).
        apply Z.nle_gt. intro H1. apply toZ_sign in H1. rewrite N.mod_small in H1 by assumption. simpl in H1. lia.
      lia.
  - subst. reflexivity.
Qed.

Ltac slot_nov :=
  intros [i [j [I [J E]]]]; unfold msub in E; change (2^64) with 18446744073709551616 in *; lia.

Ltac frame_read :=
  repeat match goal with
  | |- context [getmem 64 LittleE 8 (setmem 64 LittleE 8 ?m ?a ?v) ?a] =>
      rewrite (getmem_setmem 64 LittleE 8 m a v) by discriminate
  | |- context [getmem 64 LittleE 8 (setmem 64 LittleE 8 ?m ?a2 ?v) ?a1] =>
      rewrite (getmem_noverlap 64 LittleE LittleE 8 8 m a1 a2 v) by slot_nov
  end.

Definition lfind_cmp_contract (cp: store -> addr -> N * stmt) (cmp:N -> N -> Z) :=
  forall s t xs' sp mem key elt rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr C, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = key -> s R_RSI = elt ->
  s R_RBX = rbx -> s R_RBP = rbp -> s R_R12 = r12 -> s R_R13 = r13 ->
  s R_R14 = r14 -> s R_R15 = r15 -> mem Ⓠ[sp] = RET_SITE ->
  satisfies_all (lfind_with cp)
    (invs0 cmp sp mem key elt 0 0 rbx rbp r12 r13 r14 r15 cp)
    (exits0 cmp sp mem key elt 0 0 rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Theorem lfind_correct:
  forall cp cmp s t xs' sp mem key base nmembp size
         (WT: welltyped_code cp) (CMP: lfind_cmp_contract cp cmp)
         (ENTRY: startof t xs' = (Addr 2231584, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem) (KEY: s R_RDI = key) (BASE: s R_RSI = base)
         (NM: s R_RDX = nmembp) (SZ: s R_RCX = size) (R8: s R_R8 = C)
         (SPB: sp < 2^64) (NNB: mem Ⓠ[nmembp] < 2^64 - 1)
         (NOV: ~ overlap 64 nmembp 8 (sp ⊖ 64) 64),
  satisfies_all (lfind_with cp)
    (invs1 cmp sp mem key base nmembp size (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits1 cmp sp mem key base nmembp size (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply lfind_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT CMP SPB NNB NOV. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  - destruct PRE as (SP & MEM & KEY & BASE & NM & SZ & R8 & RBX & RBP & R12 & R13 & R14 & R15).
    assert (B: base < 2^64) by (rewrite <- BASE; apply (MDL R_RSI 64), eq_refl).
    assert (Bs := conj (MDL R_RBX 64 eq_refl) (conj (MDL R_RBP 64 eq_refl) (conj (MDL R_R12 64 eq_refl)
                  (conj (MDL R_R13 64 eq_refl) (conj (MDL R_R14 64 eq_refl) (MDL R_R15 64 eq_refl)))))).
    rewrite RBX, RBP, R12, R13, R14, R15 in Bs. destruct Bs as (B1 & B2 & B3 & B4 & B5 & B6).
    repeat x64_step.
    all: rewrite ?nmemb_frame in BC by (assumption || lia).
    + apply N.eqb_eq in BC.
      split. repeat apply outside_setmem8; try (intros a _; reflexivity); lia.
      do 7 (split; [reflexivity|]).
      right. split. reflexivity. intros i I. unfold nmemb in I. lia.
    + apply N.eqb_neq in BC. exists 0.
      do 6 (split; [reflexivity|]).
      split. unfold elt. rewrite N.mul_0_l, N.add_0_r, N.mod_small by exact B. reflexivity.
      split. unfold nmemb. lia.
      split. intros j J. lia.
      unfold frame_ok. frame_read.
      rewrite !(N.mod_small _ (2^(8*8))) by (change (2^(8*8)) with (2^64); assumption).
      rewrite !nmemb_frame by (assumption || lia).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      repeat apply outside_setmem8; try (intros a _; reflexivity); lia.
  - destruct PRE as (i & RSP & R14 & R13 & RBP & R15 & RBX & R12 & IN & PREV & FR).
    destruct FR as (F1 & F2 & F3 & F4 & F5 & F6 & FN & OUT).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply lfind_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply CMP; try (eassumption || reflexivity).
      (* the return address CALL pushed *)
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (RAXc & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply lfind_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    assert (OUT': outside sp mem (s' V_MEM64)) by (rewrite MEMc; apply outside_setmem8; [exact OUT|lia]).
    assert (FN': s' V_MEM64 Ⓠ[nmembp] = nmemb mem nmembp) by (rewrite MEMc, nmemb_frame by (assumption || lia); exact FN).
    assert (FR': frame_ok sp mem nmembp rbx0 rbp0 r120 r130 r140 r150 (s' V_MEM64)).
      unfold frame_ok.
      do 6 (split; [rewrite MEMc, slot64_frame by (assumption || lia); assumption|]).
      split; [exact FN'|exact OUT'].
    clear - RAXc RSPc RBXc RBPc R12c R13c R14c R15c MDL' FR' FN' IN PREV SPB NNB NOV.
    rename s' into s. rename MDL' into MDL. rename t' into t.
    destruct FR' as (F1 & F2 & F3 & F4 & F5 & F6 & FN & OUT).
    repeat x64_step.
    all: rewrite ?FN in *.
    all: repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                              | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end;
         repeat match goal with H: context [N.lor] |- _ => progress cbn [N.lor N.lxor] in H
                              | H: context [N.lxor] |- _ => progress cbn [N.lor N.lxor] in H end;
         try discriminate.
    all: try (apply N.eqb_eq in BC; rewrite BC in RAXc; change (toZ 32 0) with 0%Z in RAXc).
    all: try (apply N.eqb_neq in BC;
              assert (NZ: cmp key (elt base size i) <> 0%Z)
                by (rewrite <- RAXc; intro Z0; apply BC; apply toZ32_zero; [apply mp2_mod_lt|exact Z0])).
    all: unfold nmemb in *.
    all: try (exfalso; lia).
    all: assert (I1: 1 ⊕ i = i + 1) by (rewrite N.mod_small; [lia | change (2^64) with 18446744073709551616 in *; lia]).
    all: assert (E1: (elt base size i + size) mod 2^64 = elt base size (i + 1))
           by (unfold elt; rewrite mp2_add_l, N.mul_add_distr_r, N.mul_1_l, N.add_assoc; reflexivity).
    all: try (split; [exact OUT|]; split; [reflexivity|]; do 6 (split; [assumption|])).
    (* found: the first match *)
    all: try (unfold result_ok; left; exists i; split; [unfold nmemb; lia|];
              split; [reflexivity|]; split; [symmetry; exact RAXc|exact PREV]).
    (* NULL after scanning everything *)
    all: try (unfold result_ok; right; split; [reflexivity|]; intros q Q; unfold nmemb in Q;
              destruct (N.lt_ge_cases q i) as [Qi|Qi]; [apply PREV, Qi|];
              assert (q = i) by lia; subst q; exact NZ).
    (* advance to the next element *)
    all: exists (i + 1).
    all: split; [rewrite RSPc; unfold msub; change (2^64) with 18446744073709551616 in *; lia|].
    all: do 4 (split; [assumption || reflexivity|]).
    all: split; [exact I1|]. split; [rewrite E1; reflexivity|].
    all: split; [unfold msub in n; change (2^64) with 18446744073709551616 in *; lia|].
    all: split; [ intros q Q; destruct (N.lt_ge_cases q i) as [Qi|Qi]; [apply PREV, Qi|];
                  assert (q = i) by lia; subst q; exact NZ |].
    all: exact (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj FN OUT))))))).
Time Qed.

(* Non-vacuity: the comparator contract is satisfiable.  The witness places,
   at C, a comparator that returns 0 immediately (cmp = fun _ _ => 0) and a
   Nop everywhere else.  This rules out a contract that is false for every
   cp, which would make lfind_correct hold trivially. *)
Definition ret0 : stmt :=
  Move R_RAX (Word 0 64) $;
  Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
  Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
  Jmp (Var R_RIP).
Definition cp0 (_:store) (a:addr) : N * stmt := if a =? C then (1, ret0) else (1, Nop).

Theorem lfind_cmp_contract_satisfiable:
  exists cp cmp, welltyped_code cp /\ lfind_cmp_contract cp cmp.
Proof.
  exists cp0, (fun _ _ => 0%Z). split.
    intros s a. unfold cp0. destruct (a =? C); apply typchk_stmt_compute; vm_compute; exact I.
  intros s t xs' sp mem key elt rbx rbp r12 r13 r14 r15
    ENTRY MDL RSP MEM KEY ELT RBX RBP R12 R13 R14 R15 RET. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption.
    apply lfind_with_welltyped. intros s0 a0. unfold cp0. destruct (a0 =? C); apply typchk_stmt_compute; vm_compute; exact I.
  intro MDL1. clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (RDI & RSI & RSP & MEM & RET & RBX & RBP & R12 & R13 & R14 & R15).
  x64_step. rewrite RET. unfold RET_SITE. x64_step.
  split. reflexivity. split. reflexivity. split. reflexivity.
  repeat split; assumption.
Qed.

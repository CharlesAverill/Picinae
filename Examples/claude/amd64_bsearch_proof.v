(* bsearch -- binary search of a sorted array

   SEMANTICS
   ---------
   bsearch(key, base, nmemb, size, compar) binary-searches the array
   base[0..nmemb) of size-byte elements.  It keeps a half-open window [l, u),
   initially [0, nmemb), and repeatedly calls compar(key, &base[(l+u)/2]).  A
   negative result shrinks the window to [l, mid), a positive one to
   [mid+1, u), and zero returns &base[mid].  An empty window returns NULL.

   bsearch is a NON-LEAF function that calls compar through a function pointer
   (CALL R14), so the comparator is arbitrary code.  We model it as an
   arbitrary program cmpprog placed at a fixed address C outside bsearch.  The
   verified program is bsearch_with cmpprog (bsearch's lifted code, plus
   cmpprog everywhere else).  The comparator is specified by a contract,
   cmp_contract: called from bsearch's call site, it returns there with RSP
   restored, the callee-saved registers and memory unchanged, and EAX (read as
   a signed int) equal to cmp key elt, for a fixed function cmp.  Following the
   call-return machinery of ../arm8_strcasecmp_proof.v, the comparator is
   subroutine 0 and bsearch is subroutine 1; perform_call applies the
   contract at the call site.

   SPECIFICATION (man 3 bsearch, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <stdlib.h>
            void *bsearch(const void *key, const void *base,
                          size_t nmemb, size_t size,
                          int (*compar)(const void *, const void *));

     DESCRIPTION
            The  bsearch() function searches an array of nmemb objects, the initial
            member of which is pointed to by base, for a member  that  matches  the
            object  pointed  to  by  key.   The size of each member of the array is
            specified by size.

            The contents of the array should be in ascending sorted order according
            to the comparison function referenced by compar.  The compar routine is
            expected to have two arguments which point to the key object and to  an
            array  member,  in  that order, and should return an integer less than,
            equal to, or greater than zero if the  key  object  is  found,  respec-
            tively, to be less than, to match, or be greater than the array member.

     RETURN VALUE
            The  bsearch()  function  returns a pointer to a matching member of the
            array, or NULL if no match is found.  If there  are  multiple  elements
            that match the key, the element returned is unspecified.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol bsearch at 0x143680 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see bsearch_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = key, RSI = base, RDX = nmemb, RCX = size, R8 = compar = C;
            RSP = sp.  Let elt i = base + i*size (mod 2^64).
   Preconditions:  nmemb < 2^63 (so l+u never overflows); the array is
            "sorted according to compar" in the C standard's sense:
            cmp key (elt i) is sign-non-increasing in i (elements less than the
            key, then equal, then greater); and cmpprog meets cmp_contract.
   Output:  On return, RSP = sp; RBX, RBP and R12-R15 have their entry values;
            memory differs from entry memory only in bsearch's 80-byte stack
            frame below sp; and either
              RAX = elt i for some i < nmemb with cmp key (elt i) = 0, or
              RAX = 0 (NULL) and cmp key (elt i) <> 0 for every i < nmemb.
            (Partial correctness.)
 *)

Require Import Picinae_amd64.
Require Import bsearch_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem bsearch_nwc: forall s2 s1, bsearch_amd64 s1 = bsearch_amd64 s2.
Proof. reflexivity. Qed.

Theorem bsearch_welltyped: welltyped_prog x64typctx bsearch_amd64.
Proof. Picinae_typecheck. Qed.

(* bsearch saves and restores the callee-saved registers; see the Post 1 invariant. *)

Definition C := 0x10000000.   (* the comparator's (arbitrary, fixed) entry address *)
Definition RET_SITE := 1324761.  (* return address of the CALL R14 *)

(* bsearch's code, with arbitrary code (cp) at every other address.  cp is
   total: any address outside bsearch holds some instruction, possibly a
   faulting one (an executable that leaves an address unmapped is modeled by
   an instruction raising an exception, which ends the trace without reaching
   an exit, so partial correctness is unaffected). *)
Definition bsearch_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match bsearch_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma bsearch_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (bsearch_with cp).
Proof.
  intros cp WT s a. unfold bsearch_with.
  pose proof (bsearch_welltyped_lifted s a) as H.
  destruct (bsearch_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

Section Invariants.
  Variable cmp : N -> N -> Z.
  Variable sp : N.
  Variable mem : memory.
  Variable key base nmemb size : N.
  Variable rbx rbp r12 r13 r14 r15 : N.   (* callee-saved values on entry *)

  Definition elt (i:N) := base ⊕ i * size.

  (* Memory agrees with the entry memory outside bsearch's 80-byte stack frame
     (6 pushes, 24 bytes of locals, and the CALL's return-address slot). *)
  Definition outside (M:memory) :=
    forall a, ~ (msub 64 a (sp ⊖ 80) < 80) -> M Ⓑ[a] = mem Ⓑ[a].

  (* The frame's contents that bsearch relies on. *)
  Definition frame_ok (M:memory) :=
    M Ⓠ[sp ⊖ 72] = base /\ M Ⓠ[sp ⊖ 64] = size /\
    M Ⓠ[sp ⊖ 48] = rbx /\ M Ⓠ[sp ⊖ 40] = rbp /\ M Ⓠ[sp ⊖ 32] = r12 /\
    M Ⓠ[sp ⊖ 24] = r13 /\ M Ⓠ[sp ⊖ 16] = r14 /\ M Ⓠ[sp ⊖ 8] = r15 /\ outside M.

  Definition result_ok (r:N) :=
    (exists i, i < nmemb /\ r = elt i /\ cmp key (elt i) = 0%Z) \/
    (r = 0 /\ forall i, i < nmemb -> cmp key (elt i) <> 0%Z).

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* comparator (subroutine 0): entry at C, returns to RET_SITE *)
    | 268435456 => Inv 0 (s R_RDI = key /\ s R_RSI = base /\ s R_RSP = sp /\
                          s V_MEM64 = mem /\ mem Ⓠ[sp] = RET_SITE /\
                          s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                          s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    | 1324761 => Post 0 (toZ 32 (s R_RAX mod 2^32) = cmp key base /\ s R_RSP = sp ⊕ 8 /\
                         s V_MEM64 = mem /\
                         s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                         s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    (* bsearch (subroutine 1) *)
    | 1324672 => Inv 1 (s R_RSP = sp /\ s V_MEM64 = mem /\ s R_RDI = key /\ s R_RSI = base /\
                        s R_RDX = nmemb /\ s R_RCX = size /\ s R_R8 = C /\
                        s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                        s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    | 1324731 => Inv 1 (exists l u,
                   s R_RSP = sp ⊖ 72 /\ s R_RBP = key /\ s R_R14 = C /\
                   s R_R12 = u /\ s R_R13 = l /\ l < u <= nmemb /\
                   (forall i, i < l -> (0 < cmp key (elt i))%Z) /\
                   (forall i, u <= i < nmemb -> (cmp key (elt i) < 0)%Z) /\
                   frame_ok (s V_MEM64))
    | 1324793 => Post 1 (outside (s V_MEM64) /\ s R_RSP = sp /\
                   s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                   s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                   result_ok (s R_RAX))
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (bsearch_with cp) invs.
  Definition invs0 cp := make_invs 0 (bsearch_with cp) invs.
  Definition exits1 cp := make_exits 1 (bsearch_with cp) invs.
  Definition invs1 cp := make_invs 1 (bsearch_with cp) invs.
End Invariants.

Section FrameLemmas.
  Variable sp : N.
  Variable mem : memory.

  Lemma outside_refl: outside sp mem mem.
  Proof. intros a _. reflexivity. Qed.

  Lemma outside_setmem8:
    forall M x v, outside sp mem M -> 8 <= x <= 80 ->
    outside sp mem (M [Ⓠ sp ⊖ x := v]).
  Proof.
    intros M x v O X a NA. rewrite byte_setmem_cases by (discriminate || reflexivity).
    destruct (N.ltb_spec (msub 64 a (sp ⊖ x)) 8) as [H|H].
      exfalso. apply NA. unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
      apply O, NA.
  Qed.
  (* The CALL's return-address slot is disjoint from the other frame slots. *)
  Lemma slot80_frame:
    forall (M:memory) v k, sp < 2^64 -> 8 <= k <= 72 ->
    (M [Ⓠ sp ⊖ 80 := v]) Ⓠ[sp ⊖ k] = M Ⓠ[sp ⊖ k].
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

(* Distinct 8-byte stack slots below sp don't overlap. *)
Ltac slot_nov :=
  intros [i [j [I [J E]]]]; unfold msub in E; change (2^64) with 18446744073709551616 in *; lia.

(* Read 8-byte frame slots through a chain of 8-byte slot stores. *)
Ltac frame_read :=
  repeat match goal with
  | |- context [getmem 64 LittleE 8 (setmem 64 LittleE 8 ?m ?a ?v) ?a] =>
      rewrite (getmem_setmem 64 LittleE 8 m a v) by discriminate
  | |- context [getmem 64 LittleE 8 (setmem 64 LittleE 8 ?m ?a2 ?v) ?a1] =>
      rewrite (getmem_noverlap 64 LittleE LittleE 8 8 m a1 a2 v) by slot_nov
  end.

(* The comparator contract: from its entry at C (called by bsearch, so the
   return address RET_SITE is on top of the stack), it reaches RET_SITE in a
   state satisfying its postcondition.  Here "elt" is the address passed in
   RSI (the invariant family's "base" slot is reused for the element). *)
Definition cmp_contract (cp: store -> addr -> N * stmt) (cmp:N -> N -> Z) :=
  forall s t xs' sp mem key elt rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr C, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = key -> s R_RSI = elt ->
  s R_RBX = rbx -> s R_RBP = rbp -> s R_R12 = r12 -> s R_R13 = r13 ->
  s R_R14 = r14 -> s R_R15 = r15 -> mem Ⓠ[sp] = RET_SITE ->
  satisfies_all (bsearch_with cp)
    (invs0 cmp sp mem key elt 0 0 rbx rbp r12 r13 r14 r15 cp)
    (exits0 cmp sp mem key elt 0 0 rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Theorem bsearch_correct:
  forall cp cmp s t xs' sp mem key base nmemb size
         (WT: welltyped_code cp) (CMP: cmp_contract cp cmp)
         (ENTRY: startof t xs' = (Addr 1324672, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem) (KEY: s R_RDI = key) (BASE: s R_RSI = base)
         (NM: s R_RDX = nmemb) (SZ: s R_RCX = size) (R8: s R_R8 = C)
         (NMB: nmemb < 2^63) (SPB: sp < 2^64)
         (SORTED: forall i j, i <= j < nmemb ->
                  ((0 < cmp key (elt base size j))%Z -> (0 < cmp key (elt base size i))%Z) /\
                  ((cmp key (elt base size i) < 0)%Z -> (cmp key (elt base size j) < 0)%Z)),
  satisfies_all (bsearch_with cp)
    (invs1 cmp sp mem key base nmemb size (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits1 cmp sp mem key base nmemb size (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply bsearch_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT CMP NMB SORTED SPB. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.

  - (* entry *)
    destruct PRE as (SP & MEM & KEY & BASE & NM & SZ & R8 & RBX & RBP & R12 & R13 & R14 & R15).
    pose proof SPB as SPL.
    assert (B1: base < 2^64) by (rewrite <- BASE; apply (MDL R_RSI 64), eq_refl).
    assert (B2: size < 2^64) by (rewrite <- SZ; apply (MDL R_RCX 64), eq_refl).
    assert (B3: rbx0 < 2^64) by (rewrite <- RBX; apply (MDL R_RBX 64), eq_refl).
    assert (B4: rbp0 < 2^64) by (rewrite <- RBP; apply (MDL R_RBP 64), eq_refl).
    assert (B5: r120 < 2^64) by (rewrite <- R12; apply (MDL R_R12 64), eq_refl).
    assert (B6: r130 < 2^64) by (rewrite <- R13; apply (MDL R_R13 64), eq_refl).
    assert (B7: r140 < 2^64) by (rewrite <- R14; apply (MDL R_R14 64), eq_refl).
    assert (B8: r150 < 2^64) by (rewrite <- R15; apply (MDL R_R15 64), eq_refl).
    repeat x64_step.
    + (* nmemb = 0: return NULL *)
      apply N.eqb_eq in BC.
      repeat split; try reflexivity.
        repeat apply outside_setmem8; try apply outside_refl; lia.
        right. split. reflexivity. intros i I. lia.
    + (* enter the loop with l = 0, u = nmemb *)
      apply N.eqb_neq in BC.
      exists 0, nmemb. repeat split; try reflexivity; try lia.
      all: unfold frame_ok; frame_read.
      all: try (apply N.mod_small; change (2^(8*8)) with (2^64); assumption).
      repeat apply outside_setmem8; try apply outside_refl; lia.
  - (* loop head: compute mid and call compar(key, elt mid) *)
    destruct PRE as (l & u & RSP & RBP & R14 & R12 & R13 & LU & LOW & HIGH & FR).
    destruct FR as (FB & FS & F1 & F2 & F3 & F4 & F5 & F6 & OUT).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply bsearch_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply CMP; try (eassumption || reflexivity).
      (* the return address CALL pushed *)
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (RAXc & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    rewrite FS, FB in RAXc, R15c.
    assert (LUs: l + u < 2^64) by (change (2^63) with 9223372036854775808 in NMB; change (2^64) with 18446744073709551616; lia).
    rewrite (N.mod_small (l + u)) in RAXc, R15c, RBXc by exact LUs.
    set (mid := (l + u) >> 1) in *.
    assert (EM: (size * mid + base) mod 2^64 = elt base size mid)
      by (unfold elt; rewrite N.add_comm, N.mul_comm; reflexivity).
    rewrite EM in RAXc, R15c.
    assert (MID: l <= mid < u).
      subst mid. rewrite N.shiftr_div_pow2. change (2^1) with 2. split.
        apply N.div_le_lower_bound; lia.
        apply N.div_lt_upper_bound; lia.
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply bsearch_with_welltyped, WT.
set (t' := t2++t0++_::t) in *. clearbody s1 t' mid. 
    assert (OUT': outside sp mem (s' V_MEM64)) by (rewrite MEMc; apply outside_setmem8; [exact OUT|lia]).
    assert (FR': frame_ok sp mem base size rbx0 rbp0 r120 r130 r140 r150 (s' V_MEM64)).
      unfold frame_ok. rewrite MEMc. rewrite !slot80_frame by (assumption || lia).
      refine (conj FB (conj FS (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 _)))))))).
      rewrite <- MEMc. exact OUT'.
    clear - RAXc RSPc RBXc RBPc R12c R13c R14c R15c MDL' FR' LU LOW HIGH MID NMB SORTED SPB.
    rename s' into s. rename MDL' into MDL. rename t' into t.
    destruct FR' as (FB & FS & F1 & F2 & F3 & F4 & F5 & F6 & OUT).
    repeat x64_step.
    (* the sign test on the comparator's result *)
    all: rewrite ?N.shiftr_0_r, ?N.land_diag in BC; unfold slt in BC;
         change (toZ 32 0) with 0%Z in BC; rewrite RAXc in BC.
    all: first [ apply Z.ltb_lt in BC | apply Z.ltb_ge in BC ].
    (* the window tests *)
    all: repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                              | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end;
         repeat match goal with H: context [N.lor] |- _ => progress cbn [N.lor N.lxor] in H
                              | H: context [N.lxor] |- _ => progress cbn [N.lor N.lxor] in H end;
         try discriminate.
    (* the zero test on the comparator's result *)
    all: try (apply N.eqb_eq in BC0; rewrite BC0 in RAXc; change (toZ 32 0) with 0%Z in RAXc).
    all: try (apply N.eqb_neq in BC0;
              assert (NZ: cmp key (elt base size mid) <> 0%Z)
                by (rewrite <- RAXc; intro Z0; apply BC0; apply toZ32_zero; [apply mp2_mod_lt|exact Z0])).
    all: try (exfalso; lia).
    all: try (split; [exact OUT|]; split; [reflexivity|]; do 6 (split; [assumption|])).
    all: assert (MN: mid < nmemb) by lia.
    (* returned NULL: nothing in [0, nmemb) matches *)
    all: try (unfold result_ok; right; split; [reflexivity|]; intros q Q;
              destruct (N.lt_ge_cases q l) as [Ql|Ql]; [specialize (LOW q Ql); lia|];
              destruct (N.lt_ge_cases q u) as [Qu|Qu]; [|specialize (HIGH q (conj Qu Q)); lia];
              destruct (N.le_ge_cases mid q) as [Mq|Mq];
              [ destruct (SORTED mid q (conj Mq Q)) as [_ S2]
              | destruct (SORTED q mid (conj Mq MN)) as [S1 _] ];
              first [ specialize (S2 ltac:(lia)); lia | specialize (S1 ltac:(lia)); lia | lia
                    | assert (q = mid) by lia; subst q; lia ]).
    (* found: the element at mid matches *)
    all: try (unfold result_ok; left; exists mid; split; [exact MN|]; split; [reflexivity|]; lia).
    (* loop back with the window halved *)
    all: try (do 2 eexists;
         split; [rewrite RSPc; unfold msub; change (2^64) with 18446744073709551616 in *; lia|];
         split; [assumption|]; split; [assumption|];
         split; [reflexivity|]; split; [reflexivity|];
         assert (M1: 1 ⊕ mid = mid + 1) by (rewrite N.mod_small; [lia | change (2^64) with 18446744073709551616; change (2^63) with 9223372036854775808 in NMB; lia]);
         rewrite ?M1;
         split; [lia|];
         split; [ intros q Q; destruct (N.lt_ge_cases q l) as [Ql|Ql]; [apply LOW, Ql|];
                  first [ exfalso; lia
                        | assert (Hq: q <= mid < nmemb) by lia; destruct (SORTED q mid Hq) as [S1 _];
                          first [ apply S1; lia | assert (q = mid) by lia; subst q; lia ] ] |];
         split; [ intros q Q; destruct (N.lt_ge_cases q u) as [Qu|Qu]; [|apply HIGH; lia];
                  first [ exfalso; lia
                        | assert (Hq: mid <= q < nmemb) by lia; destruct (SORTED mid q Hq) as [_ S2];
                          first [ apply S2; lia | assert (q = mid) by lia; subst q; lia ] ] |];
         exact (conj FB (conj FS (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 OUT))))))))).
Time Qed.

(* Non-vacuity: the comparator contract is satisfiable.  The witness places,
   at C, a comparator that returns 0 immediately (cmp = fun _ _ => 0) and a
   Nop everywhere else.  This rules out a contract that is false for every
   cp, which would make bsearch_correct hold trivially. *)
Definition ret0 : stmt :=
  Move R_RAX (Word 0 64) $;
  Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
  Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
  Jmp (Var R_RIP).
Definition cp0 (_:store) (a:addr) : N * stmt := if a =? C then (1, ret0) else (1, Nop).

Theorem cmp_contract_satisfiable:
  exists cp cmp, welltyped_code cp /\ cmp_contract cp cmp.
Proof.
  exists cp0, (fun _ _ => 0%Z). split.
    intros s a. unfold cp0. destruct (a =? C); apply typchk_stmt_compute; vm_compute; exact I.
  intros s t xs' sp mem key elt rbx rbp r12 r13 r14 r15
    ENTRY MDL RSP MEM KEY ELT RBX RBP R12 R13 R14 R15 RET. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption.
    apply bsearch_with_welltyped. intros s0 a0. unfold cp0. destruct (a0 =? C); apply typchk_stmt_compute; vm_compute; exact I.
  intro MDL1. clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (RDI & RSI & RSP & MEM & RET & RBX & RBP & R12 & R13 & R14 & R15).
  x64_step. rewrite RET. unfold RET_SITE. x64_step.
  split. reflexivity. split. reflexivity. split. reflexivity.
  repeat split; assumption.
Qed.

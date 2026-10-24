(* strtok_r -- extract tokens from strings (reentrant)

   SEMANTICS
   ---------
   strtok_r(str, delim, saveptr) starts at s = str, or at s = *saveptr when
   str is NULL.  It skips the leading delimiters: k = strspn(s, delim) and
   t = s+k.  If t[0] is the terminator, it sets *saveptr := t and returns
   NULL.  Otherwise the token runs for n = strcspn(t, delim) bytes.  If t[n]
   is a delimiter, it is overwritten with NUL and *saveptr := t+n+1;
   otherwise *saveptr := t+n (the terminator).  strtok_r returns t.  (When
   s[0] is already the terminator, glibc skips the strspn call; the
   specification covers that case with k = 0.)
   glibc's __strtok_r is a NON-LEAF function: it calls strspn and strcspn
   through the PLT (CALL 0x128410, CALL 0x128570).  Their IFUNC-selected
   targets are not part of this program, so the proof places arbitrary code
   cp at every address outside strtok_r and assumes only contracts for the
   code entered at the two PLT stubs: they return strspn/strcspn in RAX, as
   perform_call consumes them.

   SPECIFICATION (man 3 strtok, Linux man-pages, Ubuntu 22.04)
   ------------------------------------------------------------
     SYNOPSIS
            #include <string.h>

            char *strtok_r(char *str, const char *delim, char **saveptr);

     DESCRIPTION
            The  strtok()  function breaks a string into a sequence of zero or more
            nonempty tokens.  On the first call  to  strtok(),  the  string  to  be
            parsed should be specified in str.  In each subsequent call that should
            parse the same string, str must be NULL.
            [...]
            The start of the next token is
            determined by scanning forward for the next nondelimiter byte  in  str.
            If  such  a  byte is found, it is taken as the start of the next token.
            If no such byte is found, then there are no more tokens,  and  strtok()
            returns NULL.
            [...]
            The end of each token is found by scanning  forward  until  either  the
            next  delimiter byte is found or until the terminating null byte ('\0')
            is encountered.  If a delimiter byte is found, it is overwritten with a
            null  byte to terminate the current token, and strtok() saves a pointer
            to the following byte; that pointer will be used as the starting  point
            when  searching  for  the next token.  In this case, strtok() returns a
            pointer to the start of the found token.
            [...]
            The  strtok_r()  function  is  a  reentrant  version  of strtok().  The
            saveptr argument is a pointer to a char * variable that is used  inter-
            nally  by  strtok_r()  in  order to maintain context between successive
            calls that parse the same string.

     RETURN VALUE
            The strtok() and strtok_r() functions return a pointer to the next  to-
            ken, or NULL if there are no more tokens.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol strtok_r (__strtok_r) at 0x1a9350 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh (global addressing); see strtok_r_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = str, RSI = delim, RDX = saveptr, RSP = sp, memory m.
            s = str if str <> NULL, else m[saveptr] (8 bytes).
            The frame is the 48 bytes below sp (four saved registers, padding,
            and the return address of each call).
   Preconditions:  *saveptr (8 bytes) lies outside the frame; the strings s
            and delim (up to and including their NULs) lie outside the frame;
            and cp meets both callee contracts.
   Output:  On return, RSP = sp, RBX, RBP and R12-R15 have their entry values,
            and, writing M' for the final memory and "=f" for "equal at every
            byte outside the frame", for k = strspn(s, delim), t = s+k:
              t[0] = NUL:  RAX = 0 (NULL) and M' =f m with *saveptr := t;
              t[0] <> NUL: RAX = t, and for n = strcspn(t, delim):
                 t[n] = NUL:  M' =f m with *saveptr := t+n;
                 t[n] <> NUL: M' =f m with t[n] := NUL and then
                              *saveptr := t+n+1.
            (strspn/strcspn are computed on m.  Partial correctness.)
   Callee model:  the contracts also require the callees to leave memory
            unchanged.  Real code may scribble below its own stack pointer;
            that region is dead to strtok_r.
 *)

Require Import Picinae_amd64.
Require Import strtok_r_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring.
Import ListNotations.
Open Scope N.

Theorem strtok_r_nwc: forall s2 s1, strtok_r_amd64 s1 = strtok_r_amd64 s2.
Proof. reflexivity. Qed.

Theorem strtok_r_welltyped: welltyped_prog x64typctx strtok_r_amd64.
Proof. Picinae_typecheck. Qed.

Definition P_SPN := 0x128410.   (* PLT stub for strspn *)
Definition P_CSPN := 0x128570.  (* PLT stub for strcspn *)
Definition RET_SPN := 0x1a937c.
Definition RET_CSPN := 0x1a9392.

Definition strtok_r_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match strtok_r_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma strtok_r_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (strtok_r_with cp).
Proof.
  intros cp WT s a. unfold strtok_r_with.
  pose proof (strtok_r_welltyped s a) as H.
  destruct (strtok_r_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

(* The frame window: the 48 bytes below the entry sp. *)
Definition fr (sp:N) := sp ⊖ 48.

(* The string strtok_r starts from. *)
Definition start (m:memory) (str saveptr:N) := if str =? 0 then m Ⓠ[saveptr] else str.

Definition strtok_ok (sp:N) (m:memory) (str delim saveptr r:N) (M:memory) :=
  let s := start m str saveptr in
  exists k, spn m s delim k /\
  let t := s ⊕ k in
  (m Ⓑ[t] = 0 /\ r = 0 /\ agree (fr sp) 48 M (m [Ⓠ saveptr := t])) \/
  (m Ⓑ[t] <> 0 /\ r = t /\ exists n, cspn m t delim n /\
     ((m Ⓑ[t ⊕ n] = 0 /\ agree (fr sp) 48 M (m [Ⓠ saveptr := t ⊕ n])) \/
      (m Ⓑ[t ⊕ n] <> 0 /\ agree (fr sp) 48 M (m [Ⓑ t ⊕ n := 0] [Ⓠ saveptr := t ⊕ n ⊕ 1])))).

Section Invariants.
  Variable sp : N.
  Variable mem : memory.
  Variable p d sv : N.
  Variable rbx rbp r12 r13 r14 r15 : N.

  (* The four saved registers, and everything outside the frame unchanged. *)
  Definition frame_ok (M:memory) :=
    M Ⓠ[sp ⊖ 8] = r13 /\ M Ⓠ[sp ⊖ 16] = r12 /\ M Ⓠ[sp ⊖ 24] = rbp /\ M Ⓠ[sp ⊖ 32] = rbx /\
    agree (fr sp) 48 M mem.

  Definition callee_pre (s:store) :=
    s R_RDI = p /\ s R_RSI = d /\ s R_RSP = sp /\ s V_MEM64 = mem /\
    s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
    s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.
  Definition callee_post (s:store) :=
    s R_RSP = sp ⊕ 8 /\ s V_MEM64 = mem /\
    s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
    s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strspn (subroutine 0) and strcspn (subroutine 1) *)
    | 0x128410 => Inv 0 (callee_pre s /\ mem Ⓠ[sp] = RET_SPN)
    | 0x1a937c => Post 0 (spn mem p d (s R_RAX) /\ callee_post s)
    | 0x128570 => Inv 1 (callee_pre s /\ mem Ⓠ[sp] = RET_CSPN)
    | 0x1a9392 => Post 1 (cspn mem p d (s R_RAX) /\ callee_post s)
    (* strtok_r (subroutine 2) *)
    | 0x1a9350 => Inv 2 (s R_RSP = sp /\ s V_MEM64 = mem /\
                         s R_RDI = p /\ s R_RSI = d /\ s R_RDX = sv /\
                         s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                         s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    | 0x1a936c => Inv 2 (s R_RSP = sp ⊖ 40 /\ s R_RBX = start mem p sv /\
                         s R_RBP = d /\ s R_R13 = sv /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                         frame_ok (s V_MEM64))
    | 0x1a9371 => Inv 2 (s R_RSP = sp ⊖ 40 /\ s R_RBX = start mem p sv /\
                         s R_RBP = d /\ s R_R13 = sv /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                         mem Ⓑ[start mem p sv] <> 0 /\
                         frame_ok (s V_MEM64))
    | 0x1a9387 => Inv 2 (exists k, spn mem (start mem p sv) d k /\
                         s R_RSP = sp ⊖ 40 /\ s R_R12 = start mem p sv ⊕ k /\
                         s R_RBP = d /\ s R_R13 = sv /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                         mem Ⓑ[start mem p sv ⊕ k] <> 0 /\
                         frame_ok (s V_MEM64))
    | 0x1a93b3 => Post 2 (s R_RSP = sp /\
                          s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                          s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                          strtok_ok sp mem p d sv (s R_RAX) (s V_MEM64))
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (strtok_r_with cp) invs.
  Definition invs0 cp := make_invs 0 (strtok_r_with cp) invs.
  Definition exits1 cp := make_exits 1 (strtok_r_with cp) invs.
  Definition invs1 cp := make_invs 1 (strtok_r_with cp) invs.
  Definition exits2 cp := make_exits 2 (strtok_r_with cp) invs.
  Definition invs2 cp := make_invs 2 (strtok_r_with cp) invs.
End Invariants.

(* What the code at the two PLT stubs must do.  Every conjunct of each entry
   invariant is a hypothesis, so the contracts do not force the entry check to
   fail. *)
Definition spn_contract (cp: store -> addr -> N * stmt) :=
  forall s t xs' sp mem str d rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_SPN, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = str -> s R_RSI = d ->
  s R_RBX = rbx -> s R_RBP = rbp -> s R_R12 = r12 -> s R_R13 = r13 ->
  s R_R14 = r14 -> s R_R15 = r15 -> mem Ⓠ[sp] = RET_SPN ->
  satisfies_all (strtok_r_with cp)
    (invs0 sp mem str d 0 rbx rbp r12 r13 r14 r15 cp)
    (exits0 sp mem str d 0 rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Definition cspn_contract (cp: store -> addr -> N * stmt) :=
  forall s t xs' sp mem str d rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_CSPN, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = str -> s R_RSI = d ->
  s R_RBX = rbx -> s R_RBP = rbp -> s R_R12 = r12 -> s R_R13 = r13 ->
  s R_R14 = r14 -> s R_R15 = r15 -> mem Ⓠ[sp] = RET_CSPN ->
  satisfies_all (strtok_r_with cp)
    (invs1 sp mem str d 0 rbx rbp r12 r13 r14 r15 cp)
    (exits1 sp mem str d 0 rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Lemma slot_shift:
  forall sp x j, x <= 48 -> (sp ⊖ x + j) mod 2^64 = (sp ⊖ 48 + (48 - x + j)) mod 2^64.
Proof.
  intros sp x j X. unfold msub. rewrite !N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small x), (N.mod_small 48) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma rsp_back: forall sp, sp ⊖ 48 ⊕ 8 = sp ⊖ 40.
Proof.
  intro sp. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small 48), (N.mod_small 40) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma frame_nov:
  forall a sp x, 8 <= x <= 48 -> ~ overlap 64 a 8 (fr sp) 48 -> ~ overlap 64 a 8 (sp ⊖ x) 8.
Proof.
  intros a sp x X NO [i [j [I [J E]]]]. apply NO. exists i, (48 - x + j).
  split; [exact I|]. split; [lia|]. rewrite E. apply slot_shift. lia.
Qed.

Lemma byte_frame_nov:
  forall a sp x, 8 <= x <= 48 -> ~ inwin (fr sp) 48 a -> ~ overlap 64 a 1 (sp ⊖ x) 8.
Proof.
  intros a sp x X NI [i [j [I [J E]]]]. apply NI. unfold inwin, fr.
  assert (i = 0) by lia. subst i. rewrite N.add_0_r in E.
  rewrite (msub_add_l a (sp ⊖ 48) (48 - x + j)). lia.
    change (2^64) with 18446744073709551616; lia.
  rewrite E. apply slot_shift. lia.
Qed.

Lemma agree_frame8:
  forall sp x M m v, sp < 2^64 -> 8 <= x <= 48 -> agree (fr sp) 48 M m ->
  agree (fr sp) 48 (M [Ⓠ sp ⊖ x := v]) m.
Proof.
  intros. apply agree_setwin; try assumption; try (change (2^64) with 18446744073709551616; lia).
  unfold fr, msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

(* The suffix of a string that lies outside the frame lies outside the frame. *)
Lemma strfree_shift:
  forall lo len m s k, strfree lo len m s -> (forall i, i < k -> m Ⓑ[s ⊕ i] <> 0) ->
  strfree lo len m (s ⊕ k).
Proof.
  intros lo len m s k SF PRE j NZ.
  rewrite N.add_mod_idemp_l by discriminate. rewrite <- N.add_assoc.
  apply SF. intros i I. destruct (N.lt_ge_cases i k) as [Ik|Ik]. apply PRE, Ik.
  specialize (NZ (i - k) ltac:(lia)). rewrite N.add_mod_idemp_l, <- N.add_assoc in NZ by discriminate.
  replace (k + (i - k)) with i in NZ by lia. exact NZ.
Qed.

Ltac slot_nov :=
  intros [i [j [I [J E]]]]; clear - I J E; unfold msub in E; change (2^64) with 18446744073709551616 in *; lia.

Ltac frame_read :=
  repeat match goal with
  | |- context [getmem 64 LittleE 8 (setmem 64 LittleE 8 ?m ?a ?v) ?a] =>
      rewrite (getmem_setmem 64 LittleE 8 m a v) by discriminate
  | |- context [getmem 64 LittleE 8 (setmem 64 LittleE 8 ?m ?a2 ?v) ?a1] =>
      rewrite (getmem_noverlap 64 LittleE LittleE 8 8 m a1 a2 v) by slot_nov
  end.

Theorem strtok_r_correct:
  forall cp s t xs' sp mem str delim saveptr
         (WT: welltyped_code cp) (SPN: spn_contract cp) (CSPN: cspn_contract cp)
         (ENTRY: startof t xs' = (Addr 0x1a9350, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem)
         (RDI: s R_RDI = str) (RSI: s R_RSI = delim) (RDX: s R_RDX = saveptr)
         (SPB: sp < 2^64)
         (NOV: ~ overlap 64 saveptr 8 (fr sp) 48)
         (SFS: strfree (fr sp) 48 mem (start mem str saveptr))
         (SFD: strfree (fr sp) 48 mem delim),
  satisfies_all (strtok_r_with cp)
    (invs2 sp mem str delim saveptr (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits2 sp mem str delim saveptr (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strtok_r_with_welltyped, WT. intro MDL1.
  assert (STB: start mem str saveptr < 2^64).
    unfold start. destruct (str =? 0). apply getmem_bound. rewrite <- RDI. apply (MDL R_RDI 64), eq_refl.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT SPN CSPN SPB NOV SFS SFD STB. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (RSP & MEM & RDI & RSI & RDX & RBX & RBP & R12 & R13 & R14 & R15).
    assert (Bs := conj (MDL R_RBX 64 eq_refl) (conj (MDL R_RBP 64 eq_refl) (conj (MDL R_R12 64 eq_refl)
                  (MDL R_R13 64 eq_refl)))).
    rewrite RBX, RBP, R12, R13 in Bs. destruct Bs as (B1 & B2 & B3 & B4).
    assert (FR: frame_ok sp mem rbx0 rbp0 r120 r130
                  (mem [Ⓠ sp ⊖ 8 := r130] [Ⓠ sp ⊖ 16 := r120] [Ⓠ sp ⊖ 24 := rbp0] [Ⓠ sp ⊖ 32 := rbx0])).
      unfold frame_ok. frame_read.
      rewrite !(N.mod_small _ (2^(8*8))) by (change (2^(8*8)) with (2^64); assumption).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      repeat apply agree_frame8; try (assumption || (clear; lia)). apply agree_refl.
    repeat x64_step.
    all: unfold start; rewrite BC; cbv iota.
    all: split; [reflexivity|].
    all: split; [rewrite ?getmem_noverlap by (apply frame_nov; (assumption || (clear; lia))); reflexivity|].
    all: split; [reflexivity|]. all: split; [reflexivity|].
    all: split; [assumption|]. all: split; [assumption|].
    all: exact FR.
  - (* 0x1a936c: test the first byte *)
    destruct PRE as (RSP & RBX & RBP & R13 & R14 & R15 & F1 & F2 & F3 & F4 & AG).
    set (S := start mem str saveptr) in *.
    assert (S0: S ⊕ 0 = S) by (rewrite N.add_0_r; apply N.mod_small, STB).
    assert (BYTE0: s V_MEM64 Ⓑ[S] = mem Ⓑ[S]).
      apply AG. rewrite <- S0. apply SFS. intros j J. lia.
    repeat x64_step.
    all: rewrite BYTE0 in BC.
    + (* empty: *saveptr := s, NULL *)
      apply N.eqb_eq in BC.
      split. reflexivity.
      do 4 (split; [rewrite getmem_noverlap by (apply noverlap_sym, frame_nov; (assumption || (clear; lia))); assumption|]).
      split. assumption. split. assumption.
      unfold strtok_ok. cbv zeta. change (start mem str saveptr) with S.
      exists 0. split.
        split. intros k K. lia. rewrite S0, BC. intros [NZ _]. apply NZ. reflexivity.
      left. rewrite S0. split. exact BC. split. reflexivity.
      apply agree_set; try (change (2^64) with 18446744073709551616; lia). exact AG.
    + apply N.eqb_neq in BC.
      do 6 (split; [(reflexivity || assumption)|]). split. exact BC.
      exact (conj F1 (conj F2 (conj F3 (conj F4 AG)))).
  - (* 0x1a9371: call strspn *)
    destruct PRE as (RSP & RBX & RBP & R13 & R14 & R15 & NZ & F1 & F2 & F3 & F4 & AG).
    set (S := start mem str saveptr) in *.
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply strtok_r_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply SPN; try (eassumption || reflexivity).
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (SP0 & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply strtok_r_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M := s V_MEM64 [Ⓠ sp ⊖ 48 := 1741692]) in *.
    assert (AGc: agree (fr sp) 48 M mem) by (apply agree_frame8; (assumption || (clear; lia))).
    assert (SPm: spn mem S delim (s' R_RAX)) by (eapply spn_agree; eassumption).
    assert (NIW := spn_end_free _ _ _ _ _ _ SFS SPm).
    assert (BYTE: M Ⓑ[S ⊕ s' R_RAX] = mem Ⓑ[S ⊕ s' R_RAX]) by (apply AGc, NIW).
    assert (G1: M Ⓠ[sp ⊖ 8] = r130) by (unfold M; rewrite getmem_noverlap by slot_nov; exact F1).
    assert (G2: M Ⓠ[sp ⊖ 16] = r120) by (unfold M; rewrite getmem_noverlap by slot_nov; exact F2).
    assert (G3: M Ⓠ[sp ⊖ 24] = rbp0) by (unfold M; rewrite getmem_noverlap by slot_nov; exact F3).
    assert (G4: M Ⓠ[sp ⊖ 32] = rbx0) by (unfold M; rewrite getmem_noverlap by slot_nov; exact F4).
    remember (s' R_RAX) as k eqn:RAXk. symmetry in RAXk.
    clearbody M.
    clear - RAXk RSPc MEMc RBXc RBPc R13c R14c R15c MDL' AGc SPm NIW BYTE G1 G2 G3 G4 SPB NOV SFS SFD STB.
    rename s' into s. rename MDL' into MDL. rename t' into t.
    repeat x64_step.
    all: try rewrite <- (getmem_mod_l _ _ _ M (S+k)) in BC; rewrite BYTE in BC.
    + (* only delimiters left: *saveptr := t, NULL *)
      apply N.eqb_eq in BC.
      assert (W: forall X, X [Ⓠ saveptr := S + k] = X [Ⓠ saveptr := S ⊕ k])
        by (intro X; rewrite <- (setmem_mod_r 64 LittleE 8 X saveptr (S+k)); reflexivity).
      rewrite W. split. reflexivity.
      do 4 (split; [rewrite getmem_noverlap by (apply noverlap_sym, frame_nov; (assumption || (clear; lia))); assumption|]).
      split. assumption. split. assumption.
      unfold strtok_ok. cbv zeta. change (start mem str saveptr) with S.
      exists k. split. exact SPm. left. split. exact BC. split. reflexivity.
      apply agree_set; try (change (2^64) with 18446744073709551616; lia). exact AGc.
    + apply N.eqb_neq in BC.
      exists k. change (start mem str saveptr) with S.
      split. exact SPm. split.
      rewrite RSPc, rsp_back. reflexivity.
      split. reflexivity.
      do 4 (split; [assumption|]). split. exact BC.
      exact (conj G1 (conj G2 (conj G3 (conj G4 AGc)))).
  - (* 0x1a9387: call strcspn *)
    destruct PRE as (k & SPk & RSP & R12 & RBP & R13 & R14 & R15 & NZ & F1 & F2 & F3 & F4 & AG).
    set (S := start mem str saveptr) in *.
    assert (SFT: strfree (fr sp) 48 mem (S ⊕ k)) by (apply strfree_shift; [exact SFS | apply SPk]).
    set (T := S ⊕ k) in *.
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply strtok_r_with_welltyped, WT. intro MDL1.
    eapply (perform_call 1). reflexivity.
    intros. eapply CSPN; try (eassumption || reflexivity).
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (CS & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply strtok_r_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M := s V_MEM64 [Ⓠ sp ⊖ 48 := 1741714]) in *.
    assert (AGc: agree (fr sp) 48 M mem) by (apply agree_frame8; (assumption || (clear; lia))).
    assert (CSm: cspn mem T delim (s' R_RAX)) by (eapply cspn_agree; eassumption).
    assert (NIW := cspn_end_free _ _ _ _ _ _ SFT CSm).
    assert (BYTE: M Ⓑ[T ⊕ s' R_RAX] = mem Ⓑ[T ⊕ s' R_RAX]) by (apply AGc, NIW).
    assert (G1: M Ⓠ[sp ⊖ 8] = r130) by (unfold M; rewrite getmem_noverlap by slot_nov; exact F1).
    assert (G2: M Ⓠ[sp ⊖ 16] = r120) by (unfold M; rewrite getmem_noverlap by slot_nov; exact F2).
    assert (G3: M Ⓠ[sp ⊖ 24] = rbp0) by (unfold M; rewrite getmem_noverlap by slot_nov; exact F3).
    assert (G4: M Ⓠ[sp ⊖ 32] = rbx0) by (unfold M; rewrite getmem_noverlap by slot_nov; exact F4).
    remember (s' R_RAX) as n eqn:RAXn. symmetry in RAXn.
    assert (TE: T = S ⊕ k) by reflexivity.
    clearbody M T.
    try rewrite R12 in R12c.
    clear - RAXn RSPc MEMc RBPc R12c R13c R14c R15c MDL' AGc SPk CSm NIW BYTE G1 G2 G3 G4 NZ SPB NOV TE.
    rename s' into s. rename MDL' into MDL. rename t' into t.
    repeat x64_step.
    all: try rewrite <- (getmem_mod_l _ _ _ M (T+n)) in BC; rewrite BYTE in BC.
    + (* the token runs to the end: *saveptr := t+n *)
      apply N.eqb_eq in BC.
      assert (W: forall X, X [Ⓠ saveptr := T + n] = X [Ⓠ saveptr := T ⊕ n])
        by (intro X; rewrite <- (setmem_mod_r 64 LittleE 8 X saveptr (T+n)); reflexivity).
      rewrite W. split. reflexivity.
      do 4 (split; [rewrite getmem_noverlap by (apply noverlap_sym, frame_nov; (assumption || (clear; lia))); assumption|]).
      split. assumption. split. assumption.
      unfold strtok_ok. cbv zeta. change (start mem str saveptr) with S.
      exists k. split. exact SPk. rewrite <- TE.
      right. split. exact NZ. split. reflexivity. exists n. split. exact CSm.
      left. split. exact BC.
      apply agree_set; try (change (2^64) with 18446744073709551616; lia). exact AGc.
    + (* a delimiter ends the token: t[n] := NUL, *saveptr := t+n+1 *)
      apply N.eqb_neq in BC.
      assert (A: forall X v, X [Ⓑ T + n := v] = X [Ⓑ T ⊕ n := v])
        by (intros; rewrite setmem_mod_l; reflexivity).
      assert (W: forall X, X [Ⓠ saveptr := 1 + T + n] = X [Ⓠ saveptr := T ⊕ n ⊕ 1]).
        intro X. rewrite <- (setmem_mod_r _ _ _ X _ (1 + T + n)), <- (setmem_mod_r _ _ _ X _ (T ⊕ n ⊕ 1)).
        f_equal. change (8*8) with 64. rewrite N.mod_mod, N.add_mod_idemp_l by discriminate.
        f_equal. lia.
      rewrite A, W. split. reflexivity.
      do 4 (split; [rewrite !getmem_noverlap
                      by (apply noverlap_sym; first [apply frame_nov | apply byte_frame_nov];
                          (assumption || (clear; lia))); assumption|]).
      split. assumption. split. assumption.
      unfold strtok_ok. cbv zeta. change (start mem str saveptr) with S.
      exists k. split. exact SPk. rewrite <- TE.
      right. split. exact NZ. split. reflexivity. exists n. split. exact CSm.
      right. split. exact BC.
      apply agree_set; try (change (2^64) with 18446744073709551616; lia).
      apply agree_set; try (change (2^64) with 18446744073709551616; lia). exact AGc.
Time Qed.

(* Non-vacuity: the two callee contracts are not contradictory, even
   together.  The witness spins at each PLT stub forever.  This is weaker
   evidence than terminating strspn/strcspn implementations, but it rules out
   contracts that are false for every cp, which would make strtok_r_correct
   hold trivially. *)
Definition cp_spin (_:store) (a:addr) : N * stmt :=
  if a =? P_SPN then (1, Jmp (Word P_SPN 64)) else (1, Jmp (Word P_CSPN 64)).

Lemma cp_spin_welltyped: welltyped_code cp_spin.
Proof.
  intros s a. unfold cp_spin. destruct (a =? P_SPN); apply typchk_stmt_compute; vm_compute; exact I.
Qed.

Theorem strtok_r_contracts_satisfiable:
  exists cp, welltyped_code cp /\ spn_contract cp /\ cspn_contract cp.
Proof.
  exists cp_spin. split. exact cp_spin_welltyped. split.
  all: intros s t xs' sp mem str d rbx rbp r12 r13 r14 r15
         ENTRY MDL RSP MEM RDI RSI RBX RBP R12 R13 R14 R15 RET; apply prove_invs;
       [ simpl; rewrite ENTRY; x64_step; repeat split; assumption |].
  all: intros; erewrite startof_prefix in ENTRY; try eassumption;
       eapply models_at_invariant; try eassumption;
       [ apply strtok_r_with_welltyped, cp_spin_welltyped |].
  all: intro MDL1; clear - PRE MDL1; rename t1 into t; destruct_inv 64 PRE.
  all: destruct PRE as ((RDI & RSI & RSP & MEM & RBX & RBP & R12 & R13 & R14 & R15) & RET).
  all: x64_step; repeat split; assumption.
Qed.

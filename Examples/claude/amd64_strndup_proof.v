(* strndup -- duplicate at most n bytes of a string

   SEMANTICS
   ---------
   strndup(s, maxlen) computes n = strnlen(s, maxlen) and calls malloc(n+1).
   If malloc returns NULL, strndup returns NULL.  Otherwise it stores the
   terminating NUL at d[n] itself and TAIL-CALLS memcpy(d, s, n) (JMP to the
   memcpy PLT stub), so memcpy returns d directly to strndup's caller.
   glibc's __strndup is a NON-LEAF function with three callees, all reached
   through the PLT:
     strnlen (CALL 0x128390), malloc (CALL 0x128380), memcpy (JMP 0x128620).
   As in amd64_strdup_proof.v, the proof places arbitrary code cp outside
   strndup, assumes contracts for strnlen and malloc, and ends at the jump
   into memcpy, stating memcpy's arguments exactly.  malloc is modeled with an
   abstract heap region (see amd64_strdup_proof.v).

   SPECIFICATION (man 3 strndup, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------
            char *strndup(const char *s, size_t n);

            The strndup() function is similar, but copies at most n bytes.  If
            s is longer than n, only n bytes are copied, and a terminating null
            byte ('\0') is added.

            On success, the strdup() function returns a pointer to the
            duplicated string.  It returns NULL if insufficient memory was
            available, with errno set to indicate the cause of the error.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol strndup (__strndup) at 0x1a85b0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh (global addressing); see strndup_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = maxlen < 2^64 - 1, RSP = sp, memory m.  The frame
            is the 32 bytes below sp.
   Preconditions:  the bytes strnlen reads (s[0..maxlen) up to and including
            the first NUL) lie outside the frame; the frame and the return
            address (the 40 bytes from sp-32) lie outside the heap; and cp
            meets the strnlen and malloc contracts.
   Output:  For n = strnlen(s, maxlen) (n <= maxlen, s[0..n) nonzero, and
            s[n] = 0 if n < maxlen), exactly one of two exits is reached:
              RET:  RAX = 0 (malloc returned NULL);
              JMP memcpy:  RDI = d <> 0 with [d, d+n+1) inside the heap,
                    d[n] = 0, RSI = s, RDX = n, RSP = sp (so memcpy returns d
                    to strndup's caller).
            At either exit, RBX, RBP and R12-R15 have their entry values, and
            every byte outside the heap and the frame equals its value in m.
            (Partial correctness.)
   Callee model:  the strnlen contract requires the callee to leave memory
            unchanged, and the malloc contract allows changes only inside the
            heap.
 *)

Require Import Picinae_amd64.
Require Import strndup_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring.
Import ListNotations.
Open Scope N.

Theorem strndup_nwc: forall s2 s1, strndup_amd64 s1 = strndup_amd64 s2.
Proof. reflexivity. Qed.

Theorem strndup_welltyped: welltyped_prog x64typctx strndup_amd64.
Proof. Picinae_typecheck. Qed.

Definition P_STRNLEN := 0x128390.
Definition P_MALLOC := 0x128380.
Definition P_MEMCPY := 0x128620.
Definition RET_STRNLEN := 0x1a85c3.
Definition RET_MALLOC := 0x1a85cf.

Definition strndup_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match strndup_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma strndup_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (strndup_with cp).
Proof.
  intros cp WT s a. unfold strndup_with.
  pose proof (strndup_welltyped s a) as H.
  destruct (strndup_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

Definition fr (sp:N) := sp ⊖ 32.

(* n = strnlen(p, mx). *)
Definition snlen (m:memory) p mx n :=
  n <= mx /\ (forall k, k < n -> m Ⓑ[p ⊕ k] <> 0) /\ (n < mx -> m Ⓑ[p ⊕ n] = 0).

(* The bytes strnlen(p, mx) reads lie outside the window. *)
Definition bfree lo len (m:memory) p mx :=
  forall k, k < mx -> (forall j, j < k -> m Ⓑ[p ⊕ j] <> 0) -> ~ inwin lo len (p ⊕ k).

Lemma snlen_agree:
  forall lo len M m p mx n, agree lo len M m -> bfree lo len m p mx -> snlen M p mx n -> snlen m p mx n.
Proof.
  intros lo len M m p mx n A BF [NM [PRE END]].
  assert (EQ': forall j i, i <= j -> i <= n -> i < mx -> M Ⓑ[p ⊕ i] = m Ⓑ[p ⊕ i]).
  { induction j as [|j IH] using N.peano_ind; intros i IJ IN IM.
    - apply A, BF. exact IM. intros k K. lia.
    - destruct (N.le_gt_cases i j) as [H|H]. apply IH; assumption.
      apply A, BF. exact IM. intros k K. rewrite <- (IH k) by lia. apply PRE. lia. }
  assert (EQ: forall j, j <= n -> j < mx -> M Ⓑ[p ⊕ j] = m Ⓑ[p ⊕ j]) by (intros j J JM; apply (EQ' j j); lia).
  split. exact NM. split.
  - intros k K. rewrite <- EQ by lia. apply PRE, K.
  - intro NL. rewrite <- EQ by lia. apply END, NL.
Qed.

Section Invariants.
  Variable heap : N -> Prop.
  Variable sp : N.
  Variable mem : memory.
  Variable p : N.
  Variable mx : N.
  Variable rbx rbp r12 r13 r14 r15 : N.

  Definition saved (s:store) :=
    s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
    s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.

  (* Every (canonical) byte outside the heap and the frame is unchanged. *)
  Definition unchanged_outside (M:memory) :=
    forall a, a < 2^64 -> ~ heap a -> ~ inwin (fr sp) 32 a -> M Ⓑ[a] = mem Ⓑ[a].

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strnlen (subroutine 0) *)
    | 0x128390 => Inv 0 (s R_RDI = p /\ s R_RSI = mx /\ s R_RSP = sp /\ s V_MEM64 = mem /\
                         mem Ⓠ[sp] = RET_STRNLEN /\ saved s)
    | 0x1a85c3 => Post 0 (snlen mem p mx (s R_RAX) /\ s R_RSP = sp ⊕ 8 /\ s V_MEM64 = mem /\ saved s)
    (* malloc (subroutine 1); p is the requested size *)
    | 0x128380 => Inv 1 (s R_RDI = p /\ s R_RSP = sp /\ s V_MEM64 = mem /\
                         mem Ⓠ[sp] = RET_MALLOC /\ saved s)
    | 0x1a85cf => Post 1 (s R_RSP = sp ⊕ 8 /\ saved s /\
                          (forall a, ~ heap a -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]) /\
                          (s R_RAX = 0 \/ forall i, i < p -> heap (s R_RAX ⊕ i)))
    (* strndup (subroutine 2) *)
    | 0x1a85b0 => Inv 2 (s R_RSP = sp /\ s V_MEM64 = mem /\ s R_RDI = p /\ s R_RSI = mx /\ saved s)
    | 0x1a85c7 => Inv 2 (exists n, snlen mem p mx n /\
                         s R_RSP = sp ⊖ 24 /\ s R_RDI = n ⊕ 1 /\ s R_RAX = n /\ s R_RBP = p /\
                         s R_RBX = rbx /\ s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                         s V_MEM64 Ⓠ[sp ⊖ 8] = r12 /\ s V_MEM64 Ⓠ[sp ⊖ 16] = rbp /\
                         agree (fr sp) 32 (s V_MEM64) mem)
    | 0x1a85f4 => Post 2 (s R_RSP = sp /\ s R_RAX = 0 /\ saved s /\ unchanged_outside (s V_MEM64))
    | 0x128620 => Post 2 (exists n, snlen mem p mx n /\
                          s R_RDI <> 0 /\ (forall i, i < n + 1 -> heap (s R_RDI ⊕ i)) /\
                          s V_MEM64 Ⓑ[s R_RDI ⊕ n] = 0 /\
                          s R_RSI = p /\ s R_RDX = n /\ s R_RSP = sp /\
                          saved s /\ unchanged_outside (s V_MEM64))
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (strndup_with cp) invs.
  Definition invs0 cp := make_invs 0 (strndup_with cp) invs.
  Definition exits1 cp := make_exits 1 (strndup_with cp) invs.
  Definition invs1 cp := make_invs 1 (strndup_with cp) invs.
  Definition exits2 cp := make_exits 2 (strndup_with cp) invs.
  Definition invs2 cp := make_invs 2 (strndup_with cp) invs.
End Invariants.

(* Callee contracts.  Every conjunct of each entry invariant is a
   hypothesis, so the contracts do not force the entry check to fail. *)
Definition strnlen_contract (cp: store -> addr -> N * stmt) (heap: N -> Prop) :=
  forall s t xs' sp mem str mx rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_STRNLEN, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = str -> s R_RSI = mx ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_STRNLEN ->
  satisfies_all (strndup_with cp)
    (invs0 heap sp mem str mx rbx rbp r12 r13 r14 r15 cp)
    (exits0 heap sp mem str mx rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Definition malloc_contract (cp: store -> addr -> N * stmt) (heap: N -> Prop) :=
  forall s t xs' sp mem size rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_MALLOC, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = size ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_MALLOC ->
  satisfies_all (strndup_with cp)
    (invs1 heap sp mem size 0 rbx rbp r12 r13 r14 r15 cp)
    (exits1 heap sp mem size 0 rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Lemma frame_nov:
  forall a sp x, 8 <= x <= 32 -> ~ overlap 64 a 8 (fr sp) 32 -> ~ overlap 64 a 8 (sp ⊖ x) 8.
Proof.
  intros a sp x X NO [i [j [I [J E]]]]. apply NO. exists i, (32 - x + j).
  split; [exact I|]. split; [lia|]. rewrite E. clear - X. unfold fr, msub.
  rewrite !N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small x), (N.mod_small 32) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma agree_frame8:
  forall sp x M m v, 8 <= x <= 32 -> agree (fr sp) 32 M m ->
  agree (fr sp) 32 (M [Ⓠ sp ⊖ x := v]) m.
Proof.
  intros. apply agree_setwin; try assumption; try (change (2^64) with 18446744073709551616; lia).
  clear - H. unfold fr, msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma getmem8_agree:
  forall (M1 M2:memory) a, (forall a', msub 64 a' a < 8 -> M1 Ⓑ[a'] = M2 Ⓑ[a']) -> M1 Ⓠ[a] = M2 Ⓠ[a].
Proof.
  intros M1 M2 a H. apply getmem_frame_mem. intros a' A. rewrite <- !(getmem_1 64 LittleE). apply H, A.
Qed.

(* A slot of the frame lies in the 40 bytes from sp-32. *)
Lemma slot_in40:
  forall sp x a, 8 <= x <= 32 -> msub 64 a (sp ⊖ x) < 8 -> msub 64 a (fr sp) < 40.
Proof.
  intros sp x a X A. unfold fr. clear - X A. unfold msub in *.
  change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma rsp_back: forall sp, sp ⊖ 32 ⊕ 8 = sp ⊖ 24.
Proof.
  intro sp. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small 32), (N.mod_small 24) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Ltac slot_nov :=
  intros [i [j [I [J E]]]]; clear - I J E; unfold msub in E; change (2^64) with 18446744073709551616 in *; lia.

Lemma msub_lt1_eq: forall a x, msub 64 a x < 1 -> a mod 2^64 = x mod 2^64.
Proof.
  intros a x H. assert (E: msub 64 a x = 0) by lia.
  rewrite <- (msub_add 64 a x), E, N.add_0_l. reflexivity.
Qed.

Lemma byte_set_other:
  forall (M:memory) x a v, ~ (msub 64 a x < 1) -> (setmem 64 LittleE 1 M x v) Ⓑ[a] = M Ⓑ[a].
Proof.
  intros M x a v H. rewrite byte_setmem_cases by lia.
  destruct (N.ltb_spec (msub 64 a x) 1). contradiction. reflexivity.
Qed.

(* A byte at heap address x does not touch a canonical non-heap byte. *)
Lemma msub_ne_heap:
  forall (heap:N->Prop) x a, heap (x mod 2^64) -> ~ heap a -> a < 2^64 -> ~ (msub 64 a x < 1).
Proof.
  intros heap x a HX NH AB H. apply NH. replace a with (x mod 2^64). exact HX.
  assert (E: msub 64 a x = 0) by lia.
  unfold msub in E. change (2^64) with 18446744073709551616 in *.
  rewrite <- (N.mod_small a 18446744073709551616) by exact AB.
  pose proof (N.mod_lt x 18446744073709551616 ltac:(discriminate)).
  lia.
Qed.

Theorem strndup_correct:
  forall cp heap s t xs' sp mem str mx
         (WT: welltyped_code cp) (STRNLEN: strnlen_contract cp heap) (MALLOC: malloc_contract cp heap)
         (ENTRY: startof t xs' = (Addr 0x1a85b0, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem) (RDI: s R_RDI = str) (RSI: s R_RSI = mx)
         (SPB: sp < 2^64) (MXB: mx < 2^64 - 1)
         (SFS: bfree (fr sp) 32 mem str mx)
         (HF: forall a, msub 64 a (fr sp) < 40 -> ~ heap a),
  satisfies_all (strndup_with cp)
    (invs2 heap sp mem str mx (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits2 heap sp mem str mx (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strndup_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT STRNLEN MALLOC SPB MXB SFS HF. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  - (* entry: call strnlen *)
    destruct PRE as (RSP & MEM & RDI & RSI & RBX & RBP & R12 & R13 & R14 & R15).
    assert (B1 := MDL R_R12 64 eq_refl). assert (B2 := MDL R_RBP 64 eq_refl).
    rewrite R12 in B1. rewrite RBP in B2.
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply strndup_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply STRNLEN; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (SL & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply strndup_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M := mem [Ⓠ sp ⊖ 8 := r120] [Ⓠ sp ⊖ 16 := rbp0] [Ⓠ sp ⊖ 32 := 1738179]) in *.
    assert (AGc: agree (fr sp) 32 M mem).
      repeat apply agree_frame8; try (clear; lia). apply agree_refl.
    assert (SLm: snlen mem str mx (s' R_RAX)) by (eapply snlen_agree; eassumption).
    assert (G1: M Ⓠ[sp ⊖ 8] = r120).
      unfold M. rewrite getmem_noverlap by slot_nov. rewrite getmem_noverlap by slot_nov.
      rewrite getmem_setmem by discriminate. apply N.mod_small. exact B1.
    assert (G2: M Ⓠ[sp ⊖ 16] = rbp0).
      unfold M. rewrite getmem_noverlap by slot_nov. rewrite getmem_setmem by discriminate.
      apply N.mod_small. exact B2.
    remember (s' R_RAX) as n eqn:RAXn. symmetry in RAXn.
    clearbody M.
    try rewrite RBX in RBXc. try rewrite R13 in R13c. try rewrite R14 in R14c. try rewrite R15 in R15c.
    clear - RAXn RSPc MEMc RBXc RBPc R12c R13c R14c R15c MDL' AGc SLm G1 G2.
    repeat x64_step.
    exists n. split. exact SLm. split. rewrite RSPc, rsp_back. reflexivity.
    split. f_equal. apply N.add_comm.
    do 6 (split; [first [assumption | reflexivity]|]).
    rewrite MEMc. split. exact G1. split. exact G2. exact AGc.
  - (* 0x1a85c7: MOV R12,RAX; call malloc *)
    destruct PRE as (n & SL & RSP & RDI & RAX & RBP & RBX & R13 & R14 & R15 & F1 & F2 & AG).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply strndup_with_welltyped, WT. intro MDL1.
    eapply (perform_call 1). reflexivity.
    intros. eapply MALLOC; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (RSPc & (RBXc & RBPc & R12c & R13c & R14c & R15c) & HM & RES).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply strndup_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M := s V_MEM64 [Ⓠ sp ⊖ 32 := 1738191]) in *.
    assert (AGc: agree (fr sp) 32 M mem) by (apply agree_frame8; [clear; lia | exact AG]).
    assert (G1: s' V_MEM64 Ⓠ[sp ⊖ 8] = r120).
      rewrite (getmem8_agree _ M).
        unfold M. rewrite getmem_noverlap by slot_nov. exact F1.
      intros a' A. apply HM, HF. eapply slot_in40; [|exact A]. clear; lia.
    assert (G2: s' V_MEM64 Ⓠ[sp ⊖ 16] = rbp0).
      rewrite (getmem8_agree _ M).
        unfold M. rewrite getmem_noverlap by slot_nov. exact F2.
      intros a' A. apply HM, HF. eapply slot_in40; [|exact A]. clear; lia.
    assert (OUT: unchanged_outside heap sp mem (s' V_MEM64)).
      intros a AB NH NW. rewrite (HM a NH). apply AGc, NW.
    assert (NB: n < 2^64 - 1) by (destruct SL as [NM _]; lia).
    assert (N1: 1 ⊕ n = n + 1) by (rewrite N.add_comm; apply N.mod_small; lia).
    clearbody M.
    try rewrite RBX in RBXc. try rewrite R13 in R13c. try rewrite R14 in R14c. try rewrite R15 in R15c.
    try rewrite RBP in RBPc. try rewrite R12 in R12c.
    rewrite N1 in RES.
    clear - RSPc RBXc RBPc R12c R13c R14c R15c RES MDL' G1 G2 OUT SL SPB HF NB.
    repeat x64_step.
    + (* malloc returned NULL *)
      split. first [reflexivity | apply N.mod_small, SPB]. split. reflexivity.
      split; [|exact OUT].
      unfold saved. cbn [update iseq vareq]. rewrite G1, G2.
      repeat split; assumption.
    + (* d[n] := 0, then tail call memcpy(d, s, n) *)
      apply N.eqb_neq in BC. destruct RES as [R0|HB]; [contradiction|].
      set (d := s' R_RAX) in *.
      assert (HN: heap ((d + n) mod 2^64)) by (apply HB; lia).
      assert (NOT: forall a', msub 64 a' (fr sp) < 40 -> ~ (msub 64 a' (d + n) < 1)).
      { intros a' A I. apply (HF ((d + n) mod 2^64)); [|exact HN].
        apply msub_lt1_eq in I. rewrite <- I, !msub_mod_l by reflexivity. exact A. }
      assert (SL1: forall x, 8 <= x <= 32 -> (s' V_MEM64 [Ⓑ d + n := 0]) Ⓠ[sp ⊖ x] = s' V_MEM64 Ⓠ[sp ⊖ x]).
      { intros x X. apply getmem8_agree. intros a' A. apply byte_set_other, NOT.
        eapply slot_in40; eassumption. }
      exists n. split. exact SL. split. exact BC. split. exact HB.
      split. replace (d ⊕ n) with ((d + n) mod 2^64) by reflexivity.
        rewrite getmem_mod_l, getmem_setmem by discriminate. reflexivity.
      split. reflexivity. split. reflexivity. split. reflexivity.
      split.
      * unfold saved. cbn [update iseq vareq].
        rewrite (SL1 16), (SL1 8) by lia. rewrite G1, G2.
        repeat split; assumption.
      * intros a AB NH NW. rewrite byte_set_other. apply OUT; assumption.
        apply (msub_ne_heap heap (d + n) a); assumption.
Time Qed.

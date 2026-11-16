(* strncpy -- copy a fixed-size string (musl x86_64, C), composed with
   stpncpy (and, transitively, the assembly memset)

   SEMANTICS
   ---------
   musl's strncpy (src/string/strncpy.c) is

       __stpncpy(d, s, n);
       return d;

   The binary saves RBX, keeps d there across the CALL to stpncpy
   (0x124040) and returns it.  stpncpy's contract (stpncpy_proof.v, itself
   composed with memset's) is used through call_leaf_ni.

   SPECIFICATION (man 3 strncpy, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *strncpy(char dst[restrict .dsize],
                          const char *restrict src, size_t dsize);

     DESCRIPTION
            These functions copy non-null bytes from the string pointed to
            by src into the array pointed to by dst.  If the source has too
            few non-null bytes to fill the destination, the functions pad
            the destination with trailing null bytes.  If the destination
            buffer, limited by its size, isn't large enough to hold the copy,
            the resulting character sequence is truncated.

     RETURN VALUE
            strncpy()
                   returns dst.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strncpy at 0x65b39, stpncpy at 0x24040, memset at 0x66095
            (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strncpy_amd64.v etc.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dst, RSI = src, RDX = n; RSP = rsp; m = memory; DF clear.
            Precondition (strncpy_ok): n < 2^63, and the n bytes at dst, the
            n bytes at src and the 32 bytes below rsp are pairwise disjoint.
   Output:  At the RET (0x165b46): RAX = dst; for some K <= n with
            src[0..K) nonzero and (K = n or src[K] = 0): dst[i] = src[i] for
            i < K and dst[i] = 0 for K <= i < n; every byte outside dst[0..n)
            and the 32 bytes below rsp is unchanged.  RSP = rsp; RBX, RBP,
            R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strncpy_amd64 CoqEtTu.programs.stpncpy_amd64 CoqEtTu.programs.memset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_memcpy_sets.
Require Import CoqEtTu.proofs.memset_proof CoqEtTu.proofs.stpncpy_proof.
Open Scope N.

Definition strncpy_program : program := updateall2 strncpy_amd64 stpncpy_program.

Theorem strncpy_welltyped: welltyped_prog x64typctx strncpy_amd64.
Proof. exact strncpy_amd64.welltyped. Qed.

Lemma strncpy_program_welltyped: welltyped_prog x64typctx strncpy_program.
Proof.
  intros s a. unfold strncpy_program, updateall2, updateall.
  destruct (stpncpy_program s a) as [[sz q]|] eqn:SC.
    pose proof (stpncpy_program_welltyped s a) as WT. rewrite SC in WT. exact WT.
    apply strncpy_welltyped.
Qed.

Lemma stpncpy_in_program: stpncpy_amd64 ⊆2 stpncpy_program.
Proof.
  intros s a insn SC. unfold stpncpy_program, updateall2, updateall.
  destruct (memset_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold stpncpy_amd64, memset_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Definition strncpy_ok (d src n rsp:N) :=
  nov d src n /\ ~ overlap 64 d n (rsp ⊖ 32) 32 /\ ~ overlap 64 src n (rsp ⊖ 32) 32 /\ n < 2^63.

Lemma strncpy_ok_stpncpy: forall d src n rsp, strncpy_ok d src n rsp -> stpncpy_ok d src n (rsp ⊖ 16).
Proof.
  intros d src n rsp [NOV [ND [NS NB]]]. split. exact NOV. split; [|split; [|exact NB]].
  - intros [x [y [X [Y E]]]]. apply ND. exists x, y. split. exact X. split. lia. mlia64.
  - intros [x [y [X [Y E]]]]. apply NS. exists x, y. split. exact X. split. lia. mlia64.
Qed.

Definition strncpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165b46 => true
  | _ => false end | _ => false end.

Definition strncpy_post (s0:store) (m d src n:N) (s:store) :=
  s R_RAX = d /\
  (exists K, K <= n /\ nz m src K /\ (K = n \/ m Ⓑ[src ⊕ K] = 0) /\
     (forall i, i < K -> s V_MEM64 Ⓑ[d ⊕ i] = m Ⓑ[src ⊕ i]) /\
     (forall i, K <= i < n -> s V_MEM64 Ⓑ[d ⊕ i] = 0)) /\
  (forall b, ~ (msub 64 b d < n) -> 32 <= msub 64 b (s0 R_RSP ⊖ 32) -> s V_MEM64 Ⓑ[b] = m Ⓑ[b]) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strncpy_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165b39 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ s R_DF = 0 /\ callee_saved_eq s0 s /\
                      strncpy_ok d src n (s0 R_RSP) /\ s0 R_RSP < 2^64)
  | 0x165b3d => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] /\ s R_RDI = d /\ s R_RSI = src /\
                      s R_RDX = n /\ s R_RBX = d /\ s R_RSP = s0 R_RSP ⊖ 8 /\ s R_DF = 0 /\
                      s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
                      s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15 /\
                      strncpy_ok d src n (s0 R_RSP) /\ s0 R_RSP < 2^64 /\ s0 R_RBX < 2^64)
  | 0x165b46 => Some (strncpy_post s0 m d src n s)
  | _ => None
  end | _ => None end.

(* the two pushes leave the n-byte areas alone *)
Lemma push2_area:
  forall m x n rsp v1 v2 i, ~ overlap 64 x n (rsp ⊖ 32) 32 -> i < n ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2]) Ⓑ[x ⊕ i] = m Ⓑ[x ⊕ i].
Proof.
  intros m x n rsp v1 v2 i NOV I.
  rewrite getmem_noverlap. rewrite getmem_noverlap. reflexivity.
  - intros [a [y [A [Y E]]]]. apply NOV. exists i, (24 + y). split. lia. split. lia. mlia64.
  - intros [a [y [A [Y E]]]]. apply NOV. exists i, (16 + y). split. lia. split. lia. mlia64.
Qed.

Lemma stack_q_frame:
  forall d n rsp k a, ~ overlap 64 d n (rsp ⊖ 32) 32 -> (k = 8 \/ k = 16) ->
  msub 64 a (msub 64 rsp k) < 8 -> ~ (msub 64 a d < n) /\ 16 <= msub 64 a (rsp ⊖ 16 ⊖ 16).
Proof.
  intros d n rsp k a NOV K A. split.
  - intro H. apply NOV. exists (msub 64 a d), (32 - k + msub 64 a (msub 64 rsp k)).
    split. exact H. split. lia. mlia64.
  - mlia64.
Qed.

Lemma outer_frame:
  forall b rsp, 32 <= msub 64 b (rsp ⊖ 32) -> 16 <= msub 64 b (rsp ⊖ 16 ⊖ 16) /\
                ~ overlap 64 b 1 (rsp ⊖ 16) 8 /\ ~ overlap 64 b 1 (rsp ⊖ 8) 8.
Proof.
  intros b rsp B. split. mlia64. split.
  - intros [x [y [X [Y E]]]]. mlia64.
  - intros [x [y [X [Y E]]]]. mlia64.
Qed.

Theorem strncpy_correct:
  forall prog s t s' x' m d src n
         (STRNCPY: strncpy_amd64 ⊆2 prog) (STPNCPY: stpncpy_amd64 ⊆2 prog) (MEMSET: memset_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165b39, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (DF: s R_DF = 0) (OK: strncpy_ok d src n (s R_RSP)),
  satisfies_all prog (strncpy_invs s m d src n) strncpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n STRNCPY STPNCPY MEMSET ENTRY MDL MEM D S Nn DF OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strncpy_program).
    unfold strncpy_program, stpncpy_program. apply updateall2_lub. assumption. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strncpy_invs.
    unfold strncpy_program, stpncpy_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src n MDL MEM D S Nn DF OK RB RBXB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncpy_program_welltyped. intro MDL1.
  clear - PRE MDL1 RB RBXB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP [DF [CS [OK RB']]]]]]]].
    repeat x64_step.
    destruct CS as (B & BP & B12 & B13 & B14 & B15). rewrite B. conj_tac.
  - destruct PRE as [MEM [RDI [RSI [RDX [RBX [RSP [DF [BP [R12 [R13 [R14 [R15 [OK [RB' RBXB']]]]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strncpy_program _ _ _ _ s2 nil _ s1 t MDL1 strncpy_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strncpy_program stpncpy_program _ _
              (stpncpy_invs s2 (s2 V_MEM64) d src n) stpncpy_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold stpncpy_invs.
      unfold stpncpy_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply stpncpy_correct; first
        [ apply stpncpy_in_program | apply subset_updateall2 | assumption | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; assumption)
        | (unfold s2; rewrite update_frame, update_updated by discriminate;
           replace (s0 R_RSP ⊖ 8 ⊖ 8) with (s0 R_RSP ⊖ 16) by mlia64;
           apply strncpy_ok_stpncpy; assumption) ].
    + intros a s t' NC. unfold strncpy_invs, strncpy_exit.
      unfold stpncpy_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold stpncpy_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (stpncpy_exit _) eqn:EX; [|destruct PRE].
      unfold stpncpy_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strncpy_program_welltyped).
      intro MDL3.
      destruct PRE as [[K [KN [NZ [KS [RAX [CPY ZER]]]]]] [FR [RSP' CS']]].
      unfold s2 in *.
      rewrite update_updated in NZ, KS, CPY, FR.
      rewrite update_frame, update_updated in RSP', FR by discriminate.
      pose proof OK as [NOVds [ND [NS NB]]].
      set (m2 := m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := 1465154]) in *.
      assert (RQ: forall k, k = 8 \/ k = 16 -> s' V_MEM64 Ⓠ[s0 R_RSP ⊖ k] = m2 Ⓠ[s0 R_RSP ⊖ k]).
      { intros k Kk. apply getmem_frame_mem. intros a A.
        rewrite <- !getmem_1 with (e:=LittleE).
        destruct (stack_q_frame d n (s0 R_RSP) k a ND Kk A) as [F1 F2]. apply FR; assumption. }
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 1465154).
      { rewrite RQ by (right; reflexivity). subst m2. rewrite getmem_setmem by discriminate. reflexivity. }
      assert (R8: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBX).
      { rewrite RQ by (left; reflexivity). subst m2.
        rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia64).
        rewrite getmem_setmem by discriminate. apply N.mod_small; assumption. }
      x64_step. rewrite RA. repeat x64_step.
      assert (RBXs: s' R_RBX = d) by (rewrite (proj1 CS'), !update_frame by discriminate; exact RBX).
      assert (CSb: s' R_RBP = s0 R_RBP /\ s' R_R12 = s0 R_R12 /\ s' R_R13 = s0 R_R13 /\
                   s' R_R14 = s0 R_R14 /\ s' R_R15 = s0 R_R15) by
        (destruct CS' as (_ & B1 & B2 & B3 & B4 & B5); rewrite B1, B2, B3, B4, B5;
         rewrite !update_frame by discriminate; repeat split; assumption).
      split. exact RBXs.
      split.
      { exists K. split. assumption.
        split. intros i I. rewrite <- (push2_area m src n (s0 R_RSP) (s0 R_RBX) 1465154 i NS) by lia.
          apply NZ, I.
        split. destruct (N.eq_dec K n) as [E|NE]. left. exact E. right.
          destruct KS as [KS|KS]. contradiction.
          rewrite <- (push2_area m src n (s0 R_RSP) (s0 R_RBX) 1465154 K NS) by lia. exact KS.
        split. intros i I. rewrite (CPY i I).
          apply (push2_area m src n (s0 R_RSP) (s0 R_RBX) 1465154 i NS). lia.
        exact ZER. }
      split. intros b B1 B2. destruct (outer_frame b (s0 R_RSP) B2) as [F1 [F2 F3]].
        rewrite (FR b B1 F1). subst m2.
        rewrite getmem_noverlap by exact F2. apply getmem_noverlap. exact F3.
      split. apply N.mod_small; exact RB.
      destruct CSb as (C1 & C2 & C3 & C4 & C5).
      repeat split; rewrite ?update_frame by discriminate;
        first [ assumption | rewrite update_updated; exact R8 ].
Qed.

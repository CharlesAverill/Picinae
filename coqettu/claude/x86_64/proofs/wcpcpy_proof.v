(* wcpcpy -- copy a wide string, returning a pointer to its end (musl
   x86_64, C), composed with wcscpy and wcslen

   SEMANTICS
   ---------
   musl's wcpcpy (src/string/wcpcpy.c) is

       return wcscpy(d, s) + wcslen(s);

   The binary saves RBP and RBX (= s), CALLs wcscpy (0x13c350), keeps its
   result (d) in RBP, CALLs wcslen (0x13c380) on s and returns RBP + 4 RAX.
   Both callees' contracts (wcscpy_proof.v, wcslen_proof.v) are used
   through call_leaf_ni.

   SPECIFICATION (man 3 wcpcpy, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     wchar_t *wcpcpy(wchar_t *restrict dest, const wchar_t *restrict src);
     wcpcpy is the wide-character equivalent of stpcpy: it copies the wide
     string src, including its terminating L'\0', to dest and returns a
     pointer to the end of the copied string in dest (its terminating
     L'\0').  The strings must not overlap.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcpcpy at 0x65dd5, wcscpy at 0x3c350, wcslen at 0x3c380 (Ghidra
            image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcpcpy_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.  (wcscpy's contract is by a second Claude session.)

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dest, RSI = src; RSP = rsp; m = memory.  Precondition
            (wcpcpy_ok): src is a wide string of length L with 4(L+1) < 2^63;
            the 4(L+1) bytes at dest, the 4(L+1) bytes at src and the 32
            bytes below rsp are pairwise disjoint.
   Output:  At the RET (0x165df9): RAX = dest + 4L (mod 2^64); dest[i] =
            src[i] for i <= L (32-bit words); every byte outside the 4(L+1)
            bytes at dest and the 32 bytes below rsp is unchanged.  RSP =
            rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcpcpy_amd64 CoqEtTu.programs.wcslen_amd64
               CoqEtTu.programs.wcscpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_wcopy.
Require Import CoqEtTu.proofs.wcslen_proof CoqEtTu.proofs.wcscpy_proof.
Open Scope N.

Definition wcpcpy_program : program :=
  updateall2 (updateall2 wcpcpy_amd64 wcslen_amd64) wcscpy_amd64.

Theorem wcpcpy_welltyped: welltyped_prog x64typctx wcpcpy_amd64.
Proof. exact wcpcpy_amd64.welltyped. Qed.

Lemma wcpcpy_program_welltyped: welltyped_prog x64typctx wcpcpy_program.
Proof.
  intros s a. unfold wcpcpy_program, updateall2, updateall.
  destruct (wcscpy_amd64 s a) as [[sz q]|] eqn:SC.
    pose proof (wcscpy_welltyped s a) as WT. rewrite SC in WT. exact WT.
  destruct (wcslen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (wcslen_welltyped s a) as WT. rewrite SL in WT. exact WT.
  apply wcpcpy_welltyped.
Qed.

Lemma wcslen_in_wcpcpy: wcslen_amd64 ⊆2 wcpcpy_program.
Proof.
  intros s a insn SL. unfold wcpcpy_program, updateall2, updateall.
  destruct (wcscpy_amd64 s a) eqn:SC.
  - exfalso. revert SC SL. unfold wcscpy_amd64, wcslen_amd64.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  - rewrite SL. reflexivity.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition wcpcpy_ok (m d src rsp:N) :=
  exists L, nzw m src L /\ m Ⓓ[src ⊕ 4*L] = 0 /\ 4*(L+1) < 2^63 /\
    ~ overlap 64 d (4*(L+1)) src (4*(L+1)) /\
    ~ overlap 64 d (4*(L+1)) (rsp ⊖ 32) 32 /\ ~ overlap 64 src (4*(L+1)) (rsp ⊖ 32) 32.

Definition wcpcpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165df9 => true
  | _ => false end | _ => false end.

Definition wcpcpy_post (s0:store) (m d src:N) (s:store) :=
  (exists L, nzw m src L /\ m Ⓓ[src ⊕ 4*L] = 0 /\ s R_RAX = d ⊕ 4*L /\
     (forall i, i < L + 1 -> s V_MEM64 Ⓓ[d ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]) /\
     (forall b, ~ (msub 64 b d < 4*(L+1)) -> 32 <= msub 64 b (s0 R_RSP ⊖ 32) ->
                s V_MEM64 Ⓑ[b] = m Ⓑ[b])) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition cs4 (s0 s:store) :=
  s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition mpush (s0:store) (m:N) := m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBX].

Definition wcpcpy_invs (s0:store) (m d src:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165dd5 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165dde => Some (s V_MEM64 = mpush s0 m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RBX = src /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs4 s0 s)
  | 0x165de9 => Some (exists L, nzw m src L /\ m Ⓓ[src ⊕ 4*L] = 0 /\
                      (forall i, i < L + 1 -> s V_MEM64 Ⓓ[d ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]) /\
                      (forall b, ~ (msub 64 b d < 4*(L+1)) -> 32 <= msub 64 b (s0 R_RSP ⊖ 32) ->
                                 s V_MEM64 Ⓑ[b] = m Ⓑ[b]) /\
                      (forall b, ~ (msub 64 b d < 4*(L+1)) -> msub 64 b (s0 R_RSP ⊖ 16) < 16 ->
                                 s V_MEM64 Ⓑ[b] = mpush s0 m Ⓑ[b]) /\
                      s R_RDI = src /\ s R_RBP = d /\ s R_RBX = src /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs4 s0 s)
  | 0x165df9 => Some (wcpcpy_post s0 m d src s)
  | _ => None
  end | _ => None end.

(* ---- address facts, each proved in an empty context ---- *)

Lemma push3_32:
  forall m rsp v1 v2 v3 b, 32 <= msub 64 b (rsp ⊖ 32) ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 32 := v3]) Ⓑ[b] = m Ⓑ[b].
Proof.
  intros m rsp v1 v2 v3 b O.
  rewrite (stack_store_frame _ rsp 32 v3 b 32) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 16 v2 b 32) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 8 v1 b 32) by (assumption || lia).
  reflexivity.
Qed.

Lemma word_byte32:
  forall x N rsp i a, ~ overlap 64 x (4*N) (rsp ⊖ 32) 32 -> i < N -> msub 64 a (x ⊕ 4*i) < 4 ->
  32 <= msub 64 a (rsp ⊖ 32).
Proof.
  intros x N rsp i a NOV I A.
  destruct (N.le_gt_cases 32 (msub 64 a (rsp ⊖ 32))) as [H|H]. exact H. exfalso.
  apply NOV. exists (4*i + msub 64 a (x ⊕ 4*i)), (msub 64 a (rsp ⊖ 32)).
  split. lia. split. exact H. mlia.
Qed.

Lemma push3_word:
  forall m rsp v1 v2 v3 x N i, ~ overlap 64 x (4*N) (rsp ⊖ 32) 32 -> i < N ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 32 := v3]) Ⓓ[x ⊕ 4*i] = m Ⓓ[x ⊕ 4*i].
Proof.
  intros m rsp v1 v2 v3 x N i NOV I. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply push3_32. exact (word_byte32 x N rsp i a NOV I A).
Qed.

Lemma slot_out:
  forall dd N rsp j a, ~ overlap 64 dd N (rsp ⊖ 32) 32 -> (j = 8 \/ j = 16 \/ j = 32) ->
  msub 64 a (rsp ⊖ j) < 8 -> ~ (msub 64 a dd < N).
Proof.
  intros dd N rsp j a NOV J A H. apply NOV. exists (msub 64 a dd), (32 - j + msub 64 a (rsp ⊖ j)).
  split. exact H. split. destruct J as [J|[J|J]]; subst j; lia.
  destruct J as [J|[J|J]]; subst j; mlia.
Qed.

Lemma src_not_dst:
  forall d s N i a, ~ overlap 64 d (4*N) s (4*N) -> i < N -> msub 64 a (s ⊕ 4*i) < 4 -> ~ (msub 64 a d < 4*N).
Proof.
  intros d s N i a NOV I A H. apply NOV. exists (msub 64 a d), (4*i + msub 64 a (s ⊕ 4*i)).
  split. exact H. split. lia. mlia.
Qed.

Lemma f32_ra: forall b rsp, 32 <= msub 64 b (rsp ⊖ 32) -> ~ overlap 64 b 1 (rsp ⊖ 32) 8.
Proof. intros b rsp B [x [y [X [Y E]]]]. mlia. Qed.

Lemma f16_ra: forall b rsp, msub 64 b (rsp ⊖ 16) < 16 -> ~ overlap 64 b 1 (rsp ⊖ 32) 8.
Proof. intros b rsp B [x [y [X [Y E]]]]. mlia. Qed.

Lemma slot16: forall a rsp j, (j = 8 \/ j = 16) -> msub 64 a (rsp ⊖ j) < 8 -> msub 64 a (rsp ⊖ 16) < 16.
Proof. intros a rsp j J A. destruct J; subst j; mlia. Qed.

Lemma qslot:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 32) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma mpush_rbx: forall s0 m, s0 R_RBX < 2^64 -> mpush s0 m Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBX.
Proof. intros. unfold mpush. rewrite getmem_setmem by discriminate. apply N.mod_small. assumption. Qed.

Lemma mpush_rbp: forall s0 m, s0 R_RBP < 2^64 -> mpush s0 m Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBP.
Proof.
  intros. unfold mpush. rewrite getmem_noverlap by exact (qslot _ 8 16 eq_refl).
  rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma wnilfree_nzw: forall m p k, wnilfree m p k <-> nzw m p k.
Proof. intros. reflexivity. Qed.

Lemma len_unique:
  forall m p k L, wnilfree m p k -> m Ⓓ[p ⊕ 4*k] = 0 -> nzw m p L -> m Ⓓ[p ⊕ 4*L] = 0 -> k = L.
Proof.
  intros m p k L NK ZK NL ZL. destruct (N.lt_trichotomy k L) as [H|[H|H]].
  - exfalso. apply (NL k H ZK).
  - exact H.
  - exfalso. apply (NK L H ZL).
Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem wcpcpy_correct:
  forall prog s t s' x' m d src
         (WCPCPY: wcpcpy_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog) (WCSCPY: wcscpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165dd5, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src)
         (OK: wcpcpy_ok m d src (s R_RSP)),
  satisfies_all prog (wcpcpy_invs s m d src) wcpcpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src WCPCPY WCSLEN WCSCPY ENTRY MDL MEM D S OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcpcpy_program).
    unfold wcpcpy_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcpcpy_invs.
    unfold wcpcpy_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src MDL MEM D S OK RB RBXB RBPB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcpcpy_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB. rename t1 into t.
  pose proof OK as (L0 & NZ0 & Z0 & LB & NDS & OVd & OVs).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [RSP CS]]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1.
    split. reflexivity. split. exact D.
    conj_tac. unfold cs4. repeat split; rewrite ?update_frame by discriminate; assumption.
  - destruct PRE as [MEM [RDI [RSI [RBX [RSP CS]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcpcpy_program _ _ _ _ s2 nil _ s1 t MDL1 wcpcpy_program_welltyped).
    intro MDL2.
    set (M2 := mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := 1465827]) in *.
    assert (S2M: s2 V_MEM64 = M2) by (unfold s2; apply update_updated).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 32) by (unfold s2; rewrite update_frame by discriminate; apply update_updated).
    assert (SRCW: forall i, i < L0 + 1 -> M2 Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i])
      by (intros i I; unfold M2, mpush; exact (push3_word m _ _ _ _ src (L0 + 1) i OVs I)).
    eapply (call_leaf_ni wcpcpy_program wcscpy_amd64 _ _
              (wcscpy_invs s2 (s2 V_MEM64) d src L0) wcscpy_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcscpy_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcscpy_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) | idtac ].
      rewrite S2M. split; [|split; [|split]].
      * intros i I. rewrite SRCW by (clear - I; lia). apply NZ0, I.
      * rewrite SRCW by (clear; lia). exact Z0.
      * exact NDS.
      * exact LB.
    + intros a s t' NC. unfold wcpcpy_invs, wcpcpy_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcscpy_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wcscpy_exit _) eqn:EX; [|destruct PRE].
      unfold wcscpy_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcpcpy_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [[CPY FRM] [RSP' CS']]].
      rewrite S2M in CPY, FRM. rewrite S2R in RSP'.
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 32] = 1465827).
      { transitivity (M2 Ⓠ[s0 R_RSP ⊖ 32]).
        - apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
          apply FRM. exact (slot_out _ _ _ 32 a OVd ltac:(right; right; reflexivity) A).
        - unfold M2. rewrite getmem_setmem by discriminate. reflexivity. }
      x64_step. rewrite RA. repeat x64_step.
      assert (RBXs: s' R_RBX = src) by (rewrite (proj1 CS'); unfold s2; reg; exact RBX).
      exists L0. split. exact NZ0. split. exact Z0.
      split. intros i I. rewrite CPY by exact I. apply SRCW, I.
      split. intros b B1 B2. rewrite (FRM b B1). unfold M2, mpush. apply push3_32. exact B2.
      split. intros b B1 B2. rewrite (FRM b B1). unfold M2. apply getmem_noverlap. exact (f16_ra b _ B2).
      split. exact RBXs. split. first [exact RAX' | reflexivity]. split. exact RBXs. split. reflexivity.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). destruct CS as (B2 & B3 & B4 & B5).
      unfold cs4. reg. rewrite C2, C3, C4, C5. unfold s2. reg. repeat split; assumption.
  - destruct PRE as [L [NZ [ZL [CP [FR [FP [RDI [RBP [RBX [RSP CS]]]]]]]]]].
    assert (LE: L = L0) by
      (apply (len_unique m src L L0); [exact NZ | exact ZL | exact NZ0 | exact Z0]). subst L.
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s3 := S) end.
    apply (models_after_steps wcpcpy_program _ _ _ _ s3 nil _ s1 t MDL1 wcpcpy_program_welltyped).
    intro MDL2.
    set (M3 := s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 1465838]) in *.
    assert (S3M: s3 V_MEM64 = M3) by (unfold s3; apply update_updated).
    assert (SRC3: forall i, i < L0 + 1 -> M3 Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]).
    { intros i I. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
      pose proof (word_byte32 src (L0 + 1) _ i a OVs I A) as H32.
      unfold M3. rewrite getmem_noverlap by exact (f32_ra a _ H32).
      exact (FR a (src_not_dst d src (L0 + 1) i a NDS I A) H32). }
    eapply (call_leaf_ni wcpcpy_program wcslen_amd64 _ _ (wcslen_invs s3 (s3 V_MEM64) src) wcslen_exit).
    + apply wcslen_in_wcpcpy.
    + intros a s t' EXIT NOCODE. unfold wcslen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcslen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s3; reg; assumption) ].
    + intros a s t' NC. unfold wcpcpy_invs, wcpcpy_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcslen_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wcslen_exit _) eqn:EX; [|destruct PRE].
      unfold wcslen_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcpcpy_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [NF [Z RAX]]] [MEM' [RSP' CS']]].
      rewrite S3M in MEM', NF, Z. unfold s3 in RSP'. rewrite update_frame, update_updated in RSP' by discriminate.
      assert (KL: k = L0).
      { apply (len_unique M3 src k L0 NF Z).
        - intros i I. rewrite SRC3 by (clear - I; lia). apply NZ0, I.
        - rewrite SRC3 by (clear; lia). exact Z0. }
      subst k. rewrite (wcslen_ret L0 ltac:(clear - LB; lia)) in RAX.
      assert (SL: forall j, (j = 8 \/ j = 16) -> M3 Ⓠ[s0 R_RSP ⊖ j] = mpush s0 m Ⓠ[s0 R_RSP ⊖ j]).
      { intros j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
        pose proof (slot16 a _ j J A) as A16.
        unfold M3. rewrite getmem_noverlap by exact (f16_ra a _ A16).
        apply FP. apply (slot_out d (4*(L0+1)) _ j a OVd). destruct J as [J|J]; [left|right; left]; exact J. exact A. exact A16. }
      assert (RA: M3 Ⓠ[s0 R_RSP ⊖ 32] = 1465838) by (unfold M3; rewrite getmem_setmem by discriminate; reflexivity).
      x64_step. rewrite RA. repeat x64_step.
      rewrite ?(SL 16), ?(SL 8) by (first [left; reflexivity | right; reflexivity]).
      rewrite ?mpush_rbx, ?mpush_rbp by assumption.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5).
      unfold s3 in C1, C2, C3, C4, C5. rewrite !update_frame in C1, C2, C3, C4, C5 by discriminate.
      split.
      { exists L0. split. exact NZ0. split. exact Z0.
        split. rewrite C1, RBP, N.mul_comm. reflexivity.
        split.
        - intros i I. transitivity (s1 V_MEM64 Ⓓ[d ⊕ 4*i]).
          + apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
            unfold M3. apply getmem_noverlap. exact (f32_ra a _ (word_byte32 d (L0 + 1) _ i a OVd I A)).
          + apply CP, I.
        - intros b B1 B2. unfold M3. rewrite getmem_noverlap by exact (f32_ra b _ B2). exact (FR b B1 B2). }
      split. apply N.mod_small. exact RB.
      destruct CS as (B2 & B3 & B4 & B5).
      unfold callee_saved_eq. reg. rewrite C2, C3, C4, C5. repeat split; sassumption.
Qed.

(* strrchr -- locate the last occurrence of a byte in a string (musl x86_64,
   C), composed with strlen (a call) and memrchr (a tail call)

   SEMANTICS
   ---------
   musl's strrchr (src/string/strrchr.c) is

       char *strrchr(const char *s, int c)
       {
           return __memrchr(s, c, strlen(s) + 1);
       }

   The binary spills s and c to its frame, CALLs strlen (0x1348c0), reloads
   them, pops its frame and JMPs to memrchr (0x1347a0) with n = strlen(s)+1,
   so memrchr's RET returns to strrchr's caller.  strlen's contract
   (strlen_proof.v) is used through call_leaf_ni and memrchr's
   (memrchr_proof.v) through tail_leaf (lib/x64_tail.v).

   SPECIFICATION (man 3 strrchr, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     char *strrchr(const char *s, int c);
     strrchr returns a pointer to the last occurrence of the character c
     (a byte) in the string s, or NULL if it does not occur.  The
     terminating null byte is considered part of the string, so for c = '\0'
     the result points to the terminator.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strrchr at 0x65bc2, strlen at 0x348c0, memrchr at 0x347a0 (Ghidra
            image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strrchr_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, ESI = c (c8 = c mod 256); RSP = rsp; m = memory.
            Precondition (srch_ok): s is a string of length L whose L+1
            bytes do not overlap the 32 bytes below rsp (strrchr's spills and
            the CALL).
   Output:  At memrchr's RET (0x1347da), which returns to strrchr's caller:
            memrchr_result m s c8 (L+1) RAX, i.e. RAX = s + K for the largest
            K <= L with s[K] = c8, or RAX = 0 if no s[i] (i <= L) is c8.
            Nothing outside the 32 bytes below rsp changes; RSP = rsp; RBX,
            RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strrchr_amd64 CoqEtTu.programs.strlen_amd64 CoqEtTu.programs.memrchr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.memrchr_proof.
Open Scope N.

Definition strrchr_program : program :=
  updateall2 (updateall2 strrchr_amd64 strlen_amd64) memrchr_amd64.

Theorem strrchr_welltyped: welltyped_prog x64typctx strrchr_amd64.
Proof. exact strrchr_amd64.welltyped. Qed.

Lemma strrchr_program_welltyped: welltyped_prog x64typctx strrchr_program.
Proof.
  intros s a. unfold strrchr_program, updateall2, updateall.
  destruct (memrchr_amd64 s a) as [[sz q]|] eqn:SC.
    pose proof (memrchr_welltyped s a) as WT. rewrite SC in WT. exact WT.
  destruct (strlen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (strlen_welltyped s a) as WT. rewrite SL in WT. exact WT.
  apply strrchr_welltyped.
Qed.

Lemma strlen_in_strrchr: strlen_amd64 ⊆2 strrchr_program.
Proof.
  intros s a insn SL. unfold strrchr_program, updateall2, updateall.
  destruct (memrchr_amd64 s a) eqn:SC.
  - exfalso. revert SC SL. unfold memrchr_amd64, strlen_amd64.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  - rewrite SL. reflexivity.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition srch_ok (m p rsp:N) :=
  exists L, nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ ~ overlap 64 p (L + 1) (rsp ⊖ 32) 32.

Definition strrchr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1347da => true
  | _ => false end | _ => false end.

Definition strrchr_post (s0:store) (m p c:N) (s:store) :=
  (exists L, nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ memrchr_result m p (c mod 2^8) (L + 1) (s R_RAX)) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 32 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strrchr_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165bc2 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1347da => Some (strrchr_post s0 m p c s)
  | _ => None
  end | _ => None end.

Lemma outside32:
  forall x n rsp i, ~ overlap 64 x n (rsp ⊖ 32) 32 -> i < n -> 32 <= msub 64 (x ⊕ i) (rsp ⊖ 32).
Proof.
  intros x n rsp i NOV I. assert (BB: rsp ⊖ 32 < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ 32) in *. clearbody b.
  destruct (N.le_gt_cases 32 (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D. mlia.
Qed.

(* the three stack stores before strlen: c (4 bytes), s, the return address *)
Lemma spill_frame:
  forall m rsp c p v b, 32 <= msub 64 b (rsp ⊖ 32) ->
  (m [Ⓓrsp ⊖ 12 := c] [Ⓠrsp ⊖ 24 := p] [Ⓠrsp ⊖ 32 := v]) Ⓑ[b] = m Ⓑ[b].
Proof.
  intros m rsp c p v b O.
  rewrite (stack_store_frame _ rsp 32 v b 32) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 24 p b 32) by (assumption || lia).
  apply getmem_noverlap. intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma spill_stack_frame:
  forall m rsp c p v, stack_frame m (m [Ⓓrsp ⊖ 12 := c] [Ⓠrsp ⊖ 24 := p] [Ⓠrsp ⊖ 32 := v]) rsp 32.
Proof. intros m rsp c p v b B. apply spill_frame. exact B. Qed.

Lemma nilfree_unique:
  forall m p a b, nilfree m p a -> m Ⓑ[p ⊕ a] = 0 -> nilfree m p b -> m Ⓑ[p ⊕ b] = 0 -> a = b.
Proof.
  intros m p a b NA ZA NB ZB. destruct (N.lt_trichotomy a b) as [H|[H|H]].
  - exfalso. exact (NB a H ZA).
  - exact H.
  - exfalso. exact (NA b H ZB).
Qed.

Lemma memrchr_result_transfer:
  forall M m p c n r, (forall i, i < n -> M Ⓑ[p ⊕ i] = m Ⓑ[p ⊕ i]) ->
  memrchr_result M p c n r -> memrchr_result m p c n r.
Proof.
  intros M m p c n r SAME [[K [KN [HK [AB R]]]]|[AB R]].
  - left. exists K. split. exact KN. split. rewrite <- SAME by exact KN. exact HK.
    split. intros i I. rewrite <- SAME by lia. apply AB, I. exact R.
  - right. split. intros i I. rewrite <- SAME by lia. apply AB, I. exact R.
Qed.

Lemma qslot12:
  forall rsp, ~ overlap 64 (rsp ⊖ 12) 4 (rsp ⊖ 24) 8 /\ ~ overlap 64 (rsp ⊖ 12) 4 (rsp ⊖ 32) 8.
Proof. intros. split; intros [x [y [X [Y E]]]]; mlia. Qed.

Lemma len_fits: forall p n rsp, ~ overlap 64 p n (rsp ⊖ 32) 32 -> n < 2^64.
Proof.
  intros p n rsp NOV. destruct (N.lt_ge_cases (msub 64 (rsp ⊖ 32) p) n) as [H|H].
  - exfalso. apply NOV. exists (msub 64 (rsp ⊖ 32) p), 0. split. exact H. split. lia.
    rewrite N.add_0_r, add_msub. reflexivity.
  - eapply N.le_lt_trans. exact H. apply msub_lt.
Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem strrchr_correct:
  forall prog s t s' x' m p c
         (STRRCHR: strrchr_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog) (MEMRCHR: memrchr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165bc2, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (OK: srch_ok m p (s R_RSP)),
  satisfies_all prog (strrchr_invs s m p c) strrchr_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c STRRCHR STRLEN MEMRCHR ENTRY MDL MEM P C OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strrchr_program).
    unfold strrchr_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strrchr_invs.
    unfold strrchr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C OK RB PB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strrchr_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB PB. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [P [C [RSP CS]]]].
  x64_step. x64_step. x64_step. x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
  apply (models_after_steps strrchr_program _ _ _ _ s2 tm _ s1 t MDL1 strrchr_program_welltyped).
  intro MDL2.
  set (M2 := m [Ⓓs0 R_RSP ⊖ 12 := c] [Ⓠs0 R_RSP ⊖ 24 := p] [Ⓠs0 R_RSP ⊖ 32 := 1465299]) in *.
  assert (S2M: s2 V_MEM64 = M2) by (unfold s2; apply update_updated).
  pose proof OK as (L & NL & ZL & NOV).
  assert (SAME: forall i, i < L + 1 -> M2 Ⓑ[p ⊕ i] = m Ⓑ[p ⊕ i])
    by (intros i I; apply spill_frame, (outside32 p (L + 1)); assumption).
  eapply (call_leaf_ni strrchr_program strlen_amd64 _ _ (strlen_invs s2 (s2 V_MEM64) p) strlen_exit).
  - apply strlen_in_strrchr.
  - intros a s t' EXIT NOCODE. unfold strlen_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x' s'] START. apply strlen_correct; first
      [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
  - intros a s t' NC. unfold strrchr_invs, strrchr_exit.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity)
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold strlen_exit in X. addr_cases X. discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
  - intros a' s' t2 ENTRY' UT PRE.
    unfold get_postcondition in PRE.
    destruct (strlen_exit _) eqn:EX; [|destruct PRE].
    unfold strlen_exit in EX. addr_cases EX.
    simpl in PRE.
    rewrite app_assoc.
    apply (models_after_steps _ _ _ _ _ s' (t2 ++ tm) _ s1 t MDL1 strrchr_program_welltyped).
    intro MDL3.
    destruct PRE as [[k [RAX [NF Z]]] [MEM' [RSP' CS']]].
    rewrite S2M in MEM', NF, Z. unfold s2 in RSP'. rewrite update_frame, update_updated in RSP' by discriminate.
    assert (KE: k = L).
    { apply (nilfree_unique M2 p k L NF Z).
      - intros i I. rewrite SAME by lia. apply NL, I.
      - rewrite SAME by lia. exact ZL. }
    subst k.
    unfold M2 in MEM'.
    x64_step. x64_step. x64_step. x64_step. x64_step. x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s3 := S); set (tn := T1) end.
    apply (models_after_steps _ _ _ _ _ s3 tn _ s' _ MDL3 strrchr_program_welltyped).
    intro MDL4.
    pose proof (len_fits p (L + 1) _ NOV) as LF.
    assert (C8: (c mod 2^32) mod 2^8 = c mod 2^8) by (rewrite mp2_mod_mod_min; reflexivity).
    eapply (tail_leaf_ni strrchr_program memrchr_amd64 _ _
              (memrchr_invs s3 (s3 V_MEM64) p (c mod 2^32) (1 ⊕ L)) memrchr_exit).
    + apply subset_updateall2.
    + intros a s t'' EXIT NOCODE. unfold memrchr_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t'' [x'' s''] START. apply memrchr_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s3; reg; reflexivity) ].
    + intros a s t'' NC X2. unfold strrchr_invs, strrchr_exit. unfold memrchr_exit in X2.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros a s t'' X2. unfold strrchr_exit, strrchr_invs, memrchr_invs. unfold memrchr_exit in X2.
      repeat first
      [ discriminate X2
      | (split; [reflexivity|]; unfold post_or_true, true_inv; intro POST)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
      destruct POST as [RES [PM [PR PC]]].
      assert (S3M: s3 V_MEM64 = M2) by (unfold s3; reg; unfold M2; reflexivity).
      rewrite S3M in RES, PM. rewrite C8 in RES.
      assert (E1: 1 ⊕ L = L + 1) by (rewrite (N.add_comm 1 L); apply N.mod_small, LF).
      rewrite E1 in RES.
      split. exists L. split. exact NL. split. exact ZL.
        exact (memrchr_result_transfer M2 m p _ _ _ SAME RES).
      split. rewrite PM. apply spill_stack_frame.
      split. rewrite PR. unfold s3. reg. apply N.mod_small, RB.
      eapply callee_saved_eq_trans. exact CS.
      eapply callee_saved_eq_trans; [|eapply callee_saved_eq_trans; [exact CS'|]].
      * unfold s2. repeat split; reg; reflexivity.
      * eapply callee_saved_eq_trans; [|exact PC]. unfold s3. repeat split; reg; reflexivity.
    + intros [[a|i] s] t''; reflexivity.
    + intros [[a|i] s] t''; reflexivity.
    + intros a s t'' X. unfold memrchr_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
Qed.

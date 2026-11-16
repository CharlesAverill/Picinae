(* strcat -- concatenate two strings (musl x86_64, C), composed with strlen
   and strcpy (and, transitively, stpcpy)

   SEMANTICS
   ---------
   musl's strcat (src/string/strcat.c) is

       strcpy(dest + strlen(dest), src);
       return dest;

   The binary saves RBX (dest), spills src to its frame, CALLs strlen
   (0x1348c0), then CALLs strcpy (0x1659c7) on dest+strlen(dest).  Both
   callees' contracts (strlen_proof.v, strcpy_proof.v -- the latter itself
   composed with stpcpy) are used through call_leaf_ni: one caller, two
   different callees, one of them composite.

   SPECIFICATION (man 3 strcat, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *strcat(char *restrict dst, const char *restrict src);

     DESCRIPTION
            strcat()
                   This function catenates the string pointed to by src,
                   after the string pointed to by dst (overwriting its
                   terminating null byte).  The programmer is responsible for
                   allocating a destination buffer large enough, that is,
                   strlen(dst) + strlen(src) + 1.

     RETURN VALUE
            strcpy()
            strcat()
                   These functions return dst.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strcat at 0x6598c, strlen at 0x348c0, strcpy at 0x659c7, stpcpy at
            0x347e0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strcat_amd64.v etc.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dst, RSI = src; RSP = rsp; m = memory.  Precondition
            (strcat_ok): dst and src are strings of lengths Ld and Ls; the
            Ls+1 bytes at dst+Ld do not overlap the Ls+1 bytes at src; the
            Ld+Ls+1 bytes at dst and the Ls+1 bytes at src do not overlap the
            48 bytes below rsp (strcat's, strcpy's and stpcpy's stack).
   Output:  At the RET (0x1659b4): RAX = dst; dst[Ld+i] = src[i] for i <= Ls;
            every byte outside dst[Ld .. Ld+Ls] and the 48 bytes below rsp is
            unchanged.  RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strcat_amd64 CoqEtTu.programs.strlen_amd64
               CoqEtTu.programs.strcpy_amd64 CoqEtTu.programs.stpcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_memcpy_sets.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.stpcpy_proof CoqEtTu.proofs.strcpy_proof.
Open Scope N.

Definition strcat_program : program :=
  updateall2 (updateall2 strcat_amd64 strlen_amd64) strcpy_program.

Theorem strcat_welltyped: welltyped_prog x64typctx strcat_amd64.
Proof. exact strcat_amd64.welltyped. Qed.

Lemma strcat_program_welltyped: welltyped_prog x64typctx strcat_program.
Proof.
  intros s a. unfold strcat_program, updateall2, updateall.
  destruct (strcpy_program s a) as [[sz q]|] eqn:SC.
    pose proof (strcpy_program_welltyped s a) as WT. rewrite SC in WT. exact WT.
  destruct (strlen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (strlen_welltyped s a) as WT. rewrite SL in WT. exact WT.
  apply strcat_welltyped.
Qed.

Lemma strcpy_in_program: strcpy_amd64 ⊆2 strcpy_program.
Proof.
  intros s a insn SC. unfold strcpy_program, updateall2, updateall.
  destruct (stpcpy_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold strcpy_amd64, stpcpy_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma strlen_in_strcat: strlen_amd64 ⊆2 strcat_program.
Proof.
  intros s a insn SL. unfold strcat_program, updateall2, updateall.
  destruct (strcpy_program s a) eqn:SC.
  - exfalso. revert SC SL. unfold strcpy_program, updateall2, updateall, strcpy_amd64, stpcpy_amd64, strlen_amd64.
    cbv beta.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  - rewrite SL. reflexivity.
Qed.

Definition strcat_ok (m d src rsp:N) :=
  exists Ld Ls, nilfree m d Ld /\ m Ⓑ[d ⊕ Ld] = 0 /\ nilfree m src Ls /\ m Ⓑ[src ⊕ Ls] = 0 /\
    nov (d ⊕ Ld) src (Ls + 1) /\ Ld + Ls + 1 < 2^63 /\
    ~ overlap 64 d (Ld + Ls + 1) (rsp ⊖ 48) 48 /\ ~ overlap 64 src (Ls + 1) (rsp ⊖ 48) 48.

Definition strcat_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1659b4 => true
  | _ => false end | _ => false end.

Definition strcat_post (s0:store) (m d src:N) (s:store) :=
  s R_RAX = d /\
  (exists Ld Ls, nilfree m d Ld /\ m Ⓑ[d ⊕ Ld] = 0 /\ nilfree m src Ls /\ m Ⓑ[src ⊕ Ls] = 0 /\
     (forall i, i < Ls + 1 -> s V_MEM64 Ⓑ[d ⊕ (Ld + i)] = m Ⓑ[src ⊕ i]) /\
     (forall b, ~ (msub 64 b (d ⊕ Ld) < Ls + 1) -> 48 <= msub 64 b (s0 R_RSP ⊖ 48) ->
                s V_MEM64 Ⓑ[b] = m Ⓑ[b])) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition cs_but_rbx (s0 s:store) :=
  s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
  s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition strcat_invs (s0:store) (m d src:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x16598c => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ strcat_ok m d src (s0 R_RSP) /\
                      s0 R_RSP < 2^64 /\ s0 R_RBX < 2^64)
  | 0x165999 => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := src] /\
                      s R_RDI = d /\ s R_RBX = d /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs_but_rbx s0 s /\
                      strcat_ok m d src (s0 R_RSP) /\ src < 2^64 /\ s0 R_RSP < 2^64 /\ s0 R_RBX < 2^64)
  | 0x1659a7 => Some (exists Ld, nilfree m d Ld /\ m Ⓑ[d ⊕ Ld] = 0 /\
                      s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := src]
                                    [Ⓠs0 R_RSP ⊖ 32 := 0x16599e] /\
                      s R_RDI = d ⊕ Ld /\ s R_RSI = src /\ s R_RBX = d /\ s R_RSP = s0 R_RSP ⊖ 24 /\
                      cs_but_rbx s0 s /\ strcat_ok m d src (s0 R_RSP) /\ src < 2^64 /\ s0 R_RSP < 2^64 /\
                      s0 R_RBX < 2^64)
  | 0x1659b4 => Some (strcat_post s0 m d src s)
  | _ => None
  end | _ => None end.

Lemma cs_but_rbx_callee:
  forall s0 s1 s, cs_but_rbx s0 s1 -> callee_saved_eq s1 s -> cs_but_rbx s0 s.
Proof. intros s0 s1 s (B1&B2&B3&B4&B5) (_&C1&C2&C3&C4&C5). repeat split; congruence. Qed.

Lemma nilfree_unique:
  forall m p a b, nilfree m p a -> m Ⓑ[p ⊕ a] = 0 -> nilfree m p b -> m Ⓑ[p ⊕ b] = 0 -> a = b.
Proof.
  intros m p a b NA ZA NB ZB. destruct (N.lt_trichotomy a b) as [H|[H|H]].
  - exfalso. exact (NB a H ZA).
  - exact H.
  - exfalso. exact (NA b H ZB).
Qed.

(* bytes of a range clear of the 48 bytes below rsp *)
Lemma outside48:
  forall x n rsp i, ~ overlap 64 x n (rsp ⊖ 48) 48 -> i < n -> 48 <= msub 64 (x ⊕ i) (rsp ⊖ 48).
Proof.
  intros x n rsp i NOV I. assert (BB: rsp ⊖ 48 < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ 48) in *. clearbody b.
  destruct (N.le_gt_cases 48 (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D.
  unfold msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma push3_frame:
  forall m rsp v1 v2 v3 b, 48 <= msub 64 b (rsp ⊖ 48) ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 32 := v3]) Ⓑ[b] = m Ⓑ[b].
Proof.
  intros m rsp v1 v2 v3 b O.
  rewrite (stack_store_frame _ rsp 32 v3 b 48) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 16 v2 b 48) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 8 v1 b 48) by (assumption || lia).
  reflexivity.
Qed.

Lemma push3_off:
  forall m rsp v1 v2 v3 x n i, ~ overlap 64 x n (rsp ⊖ 48) 48 -> i < n ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 32 := v3]) Ⓑ[x ⊕ i] = m Ⓑ[x ⊕ i].
Proof.
  intros m rsp v1 v2 v3 x n i NOV I. apply push3_frame. exact (outside48 x n rsp i NOV I).
Qed.

Lemma sub_nov:
  forall x n b o L W, ~ overlap 64 x n b W -> o + L <= n -> ~ overlap 64 (x ⊕ o) L b W.
Proof.
  intros x n b o L W NOV OL [i [j [I [J E]]]]. apply NOV. exists (o + i), j.
  split. lia. split. exact J. rewrite <- E, N.add_mod_idemp_l by discriminate. f_equal. lia.
Qed.

Lemma nov48_16:
  forall x n rsp, ~ overlap 64 x n (rsp ⊖ 48) 48 -> ~ overlap 64 x n (rsp ⊖ 32 ⊖ 16) 16.
Proof.
  intros x n rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. exact I. split. lia.
  rewrite E. f_equal. f_equal. mlia64.
Qed.

(* an 8-byte stack slot at rsp-k (k in {8,32}) is outside the copy and inside
   strcpy's preserved frame *)
Lemma stack_q48:
  forall d n rsp k a o L, ~ overlap 64 d n (rsp ⊖ 48) 48 -> (k = 8 \/ k = 32) ->
  msub 64 a (rsp ⊖ k) < 8 -> o + L <= n ->
  ~ (msub 64 a (d ⊕ o) < L) /\ 16 <= msub 64 a (rsp ⊖ 32 ⊖ 16).
Proof.
  intros d n rsp k a o L NOV K A OL. split.
  - intro H. apply (sub_nov d n _ o L 48 NOV OL).
    assert (DB: d ⊕ o < 2^64) by (apply N.mod_lt; discriminate).
    set (d' := d ⊕ o) in *. clearbody d'.
    exists (msub 64 a d'), (48 - k + msub 64 a (rsp ⊖ k)).
    split. exact H. split. destruct K; subst k; lia. destruct K; subst k; mlia64.
  - destruct K; subst k; mlia64.
Qed.

Lemma qslot:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 48) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia64.
Qed.

Lemma frame48_16: forall b rsp, 48 <= msub 64 b (rsp ⊖ 48) -> 16 <= msub 64 b (rsp ⊖ 32 ⊖ 16).
Proof. intros. mlia64. Qed.

Lemma addr_split: forall d L k, (d ⊕ L) ⊕ k = d ⊕ (L + k).
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia. Qed.

Lemma lt1_le: forall i L, i < L + 1 -> i <= L.
Proof. intros. lia. Qed.

Theorem strcat_correct:
  forall prog s t s' x' m d src
         (STRCAT: strcat_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (STRCPY: strcpy_amd64 ⊆2 prog) (STPCPY: stpcpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x16598c, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src)
         (OK: strcat_ok m d src (s R_RSP)),
  satisfies_all prog (strcat_invs s m d src) strcat_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src STRCAT STRLEN STRCPY STPCPY ENTRY MDL MEM D S OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strcat_program).
    unfold strcat_program, strcpy_program. apply updateall2_lub. apply updateall2_lub; assumption.
    apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strcat_invs.
    unfold strcat_program, strcpy_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src MDL MEM D S OK RB RBXB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcat_program_welltyped. intro MDL1.
  clear - PRE MDL1 RB RBXB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [RSP [CS [OK [RB' RBXB']]]]]]].
    repeat x64_step.
    destruct CS as (B & BP & B12 & B13 & B14 & B15). rewrite B. conj_tac.
    unfold cs_but_rbx; repeat split; rewrite ?update_frame by discriminate; assumption.
    rewrite <- S. apply (MDL1 R_RSI 64). reflexivity.
  - (* call strlen(dst) *)
    destruct PRE as [MEM [RDI [RBX [RSP [CS [OK [SB [RB' RBXB']]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcat_program _ _ _ _ s2 nil _ s1 t MDL1 strcat_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strcat_program strlen_amd64 _ _ (strlen_invs s2 (s2 V_MEM64) d) strlen_exit).
    + apply strlen_in_strcat.
    + intros a s t' EXIT NOCODE. unfold strlen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strlen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; assumption) ].
    + intros a s t' NC. unfold strcat_invs, strcat_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold strlen_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (strlen_exit _) eqn:EX; [|destruct PRE].
      unfold strlen_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcat_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [RAX [NF Z]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame, update_updated in RSP' by discriminate.
      rewrite update_updated in MEM', NF, Z.
      destruct CS' as (C0&C1&C2&C3&C4&C5).
      rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      pose proof OK as (Ld0 & Ls & NF0 & Z0 & NFs & Zs & NOV & LB & OVd & OVs).
      assert (KE: k = Ld0).
      { apply (nilfree_unique _ d k Ld0 NF Z).
        - intros i I. rewrite push3_off with (n := Ld0 + Ls + 1) by (exact OVd || lia). apply NF0, I.
        - rewrite push3_off with (n := Ld0 + Ls + 1) by (exact OVd || lia). exact Z0. }
      subst k.
      repeat x64_step.
      exists Ld0. conj_tac.
      * rewrite RBX. reflexivity.
      * destruct CS as (B1&B2&B3&B4&B5). unfold cs_but_rbx.
        rewrite !update_frame by discriminate.
        rewrite C1, C2, C3, C4, C5. repeat split; assumption.
  - (* call strcpy(dst+Ld, src) *)
    destruct PRE as [Ld [NF0 [Z0 [MEM [RDI [RSI [RBX [RSP [CS [OK [SB [RB' RBXB']]]]]]]]]]]].
    pose proof OK as (Ld1 & Ls & NF1 & Z1 & NFs & Zs & NOV & LB & OVd & OVs).
    assert (LE: Ld1 = Ld) by exact (nilfree_unique m d Ld1 Ld NF1 Z1 NF0 Z0). subst Ld1.
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcat_program _ _ _ _ s2 nil _ s1 t MDL1 strcat_program_welltyped).
    intro MDL2.
    set (M2 := m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := src] [Ⓠs0 R_RSP ⊖ 32 := 0x1659ac]) in *.
    assert (S2M: s2 V_MEM64 = M2) by (unfold s2; apply update_updated).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 32) by (unfold s2; rewrite update_frame by discriminate; apply update_updated).
    assert (SRCB: forall i, i <= Ls -> M2 Ⓑ[src ⊕ i] = m Ⓑ[src ⊕ i])
      by (intros i I; unfold M2; apply push3_off with (n := Ls + 1); [exact OVs | lia]).
    eapply (call_leaf_ni strcat_program strcpy_program _ _
              (strcpy_invs s2 (s2 V_MEM64) (d ⊕ Ld) src Ls) strcpy_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold strcpy_invs.
      unfold strcpy_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strcpy_correct; first
        [ apply strcpy_in_program | apply subset_updateall2 | assumption | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; assumption) | idtac ].
      rewrite S2M, S2R. split; [split; [|split] | split].
      * intros i I. rewrite SRCB by lia. apply NFs, I.
      * rewrite SRCB by lia. exact Zs.
      * exact NOV.
      * apply nov48_16. apply (sub_nov d (Ld + Ls + 1)). exact OVd. lia.
      * apply nov48_16. exact OVs.
    + intros a s t' NC. unfold strcat_invs, strcat_exit.
      unfold strcpy_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold strcpy_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (strcpy_exit _) eqn:EX; [|destruct PRE].
      unfold strcpy_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcat_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [CPY [FR [RSP' CS']]]].
      rewrite S2M in CPY, FR. rewrite S2R in FR, RSP'.
      assert (RQ: forall k, k = 8 \/ k = 32 -> s' V_MEM64 Ⓠ[s0 R_RSP ⊖ k] = M2 Ⓠ[s0 R_RSP ⊖ k]).
      { intros k Kk. apply getmem_frame_mem. intros a A.
        rewrite <- !getmem_1 with (e:=LittleE).
        destruct (stack_q48 d (Ld + Ls + 1) (s0 R_RSP) k a Ld (Ls + 1) OVd Kk A ltac:(lia)) as [F1 F2].
        apply FR; assumption. }
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 32] = 0x1659ac).
      { rewrite RQ by (right; reflexivity). unfold M2. rewrite getmem_setmem by discriminate. reflexivity. }
      assert (R8: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBX).
      { rewrite RQ by (left; reflexivity). unfold M2.
        rewrite getmem_noverlap by exact (qslot _ 8 32 eq_refl).
        rewrite getmem_noverlap by exact (qslot _ 8 16 eq_refl).
        rewrite getmem_setmem by discriminate. apply N.mod_small; assumption. }
      x64_step. rewrite RA. repeat x64_step.
      assert (RBXs: s' R_RBX = d) by
        (rewrite (proj1 CS'); unfold s2; rewrite !update_frame by discriminate; exact RBX).
      assert (CSb: s' R_RBP = s0 R_RBP /\ s' R_R12 = s0 R_R12 /\ s' R_R13 = s0 R_R13 /\
                   s' R_R14 = s0 R_R14 /\ s' R_R15 = s0 R_R15) by
        (destruct CS' as (_ & B1 & B2 & B3 & B4 & B5); rewrite B1, B2, B3, B4, B5;
         unfold s2; rewrite !update_frame by discriminate;
         destruct CS as (C1 & C2 & C3 & C4 & C5); repeat split; assumption).
      rewrite ?R8.
      conj_tac.
      * exists Ld, Ls. split. exact NF0. split. exact Z0. split. exact NFs. split. exact Zs. split.
        -- intros i I. rewrite <- addr_split. rewrite CPY by exact I. apply SRCB, lt1_le, I.
        -- intros b B1 B2. rewrite (FR b B1 (frame48_16 b _ B2)). unfold M2. apply push3_frame. exact B2.
      * apply N.mod_small. exact RB.
      * destruct CSb as (C1 & C2 & C3 & C4 & C5).
        repeat split; rewrite ?update_updated, ?update_frame by discriminate;
          first [ sreflexivity | sassumption ].
Qed.

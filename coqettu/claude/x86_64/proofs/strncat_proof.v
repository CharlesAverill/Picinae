(* strncat -- append at most n bytes of a string (musl x86_64, C), composed
   with strlen

   SEMANTICS
   ---------
   musl's strncat (src/string/strncat.c) is

       char *a = d;
       d += strlen(d);
       while (n && *s) n--, *d++ = *s++;
       *d++ = 0;
       return a;

   The binary saves R12 (= d), RBP (= n) and RBX (= s), CALLs strlen
   (0x1348c0), and then runs the copy loop with an end pointer
   d + strlen(d) + n.  strlen's contract (strlen_proof.v) is used through
   call_leaf_ni.

   SPECIFICATION (man 3 strncat, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     char *strncat(char *restrict dst, const char src[restrict .ssize],
                   size_t ssize);
     strncat appends to the string dst at most ssize bytes of src, stopping
     at src's terminating null byte, and then writes a terminating null
     byte.  It returns dst.  The buffers must not overlap.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strncat at 0x34940, strlen at 0x348c0 (Ghidra image base
            0x100000: 0x134940, 0x1348c0)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/strncat_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, RSI = src, RDX = n; RSP = rsp; m = memory.
            Precondition (strncat_ok): d is a string of length Ld; Ld + n + 1
            < 2^63; the n+1 bytes at d+Ld do not overlap the n bytes at src;
            the Ld+n+1 bytes at d and the n bytes at src do not overlap the
            32 bytes below rsp (strncat's pushes and its CALL).  src need not
            be terminated within n bytes.
   Output:  At the RET (0x134980): RAX = d; there is K <= n such that
            src[0..K) are nonzero and K = n or src[K] = 0; d[Ld+i] = src[i]
            for i < K and d[Ld+K] = 0; every byte outside d[Ld .. Ld+K] and
            the 32 bytes below rsp is unchanged.  RSP = rsp; RBX, RBP,
            R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strncat_amd64 CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.strlen_proof.
Open Scope N.

Definition strncat_program : program := updateall2 strncat_amd64 strlen_amd64.

Theorem strncat_welltyped: welltyped_prog x64typctx strncat_amd64.
Proof. exact strncat_amd64.welltyped. Qed.

Lemma strncat_program_welltyped: welltyped_prog x64typctx strncat_program.
Proof.
  intros s a. unfold strncat_program, updateall2, updateall.
  destruct (strlen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (strlen_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply strncat_welltyped.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition strncat_ok (m d src n rsp:N) :=
  exists Ld, nilfree m d Ld /\ m Ⓑ[d ⊕ Ld] = 0 /\ Ld + n + 1 < 2^63 /\
    ~ overlap 64 (d ⊕ Ld) (n + 1) src n /\
    ~ overlap 64 d (Ld + n + 1) (rsp ⊖ 32) 32 /\ ~ overlap 64 src n (rsp ⊖ 32) 32.

(* the source bytes s[0..k) are nonzero *)
Definition nz (m s k:N) := forall i, i < k -> m Ⓑ[s ⊕ i] <> 0.

(* dd[0..k) holds src[0..k) (as in m); other bytes are as in mb *)
Definition cpb (m mb M dd s k:N) :=
  (forall i, i < k -> M Ⓑ[dd ⊕ i] = m Ⓑ[s ⊕ i]) /\
  (forall b, ~ (msub 64 b dd < k) -> M Ⓑ[b] = mb Ⓑ[b]).

(* the memory after the three pushes and the CALL *)
Definition mb (s0:store) (m:N) :=
  m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX]
    [Ⓠs0 R_RSP ⊖ 32 := 0x134952].

Lemma push4_frame:
  forall m rsp v1 v2 v3 v4 b, 32 <= msub 64 b (rsp ⊖ 32) ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 24 := v3] [Ⓠrsp ⊖ 32 := v4]) Ⓑ[b] = m Ⓑ[b].
Proof.
  intros m rsp v1 v2 v3 v4 b O.
  rewrite (stack_store_frame _ rsp 32 v4 b 32) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 24 v3 b 32) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 16 v2 b 32) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 8 v1 b 32) by (assumption || lia).
  reflexivity.
Qed.

Lemma outside32:
  forall x n rsp i, ~ overlap 64 x n (rsp ⊖ 32) 32 -> i < n -> 32 <= msub 64 (x ⊕ i) (rsp ⊖ 32).
Proof.
  intros x n rsp i NOV I. assert (BB: rsp ⊖ 32 < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ 32) in *. clearbody b.
  destruct (N.le_gt_cases 32 (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D. mlia.
Qed.

Lemma nilfree_unique:
  forall m p a b, nilfree m p a -> m Ⓑ[p ⊕ a] = 0 -> nilfree m p b -> m Ⓑ[p ⊕ b] = 0 -> a = b.
Proof.
  intros m p a b NA ZA NB ZB. destruct (N.lt_trichotomy a b) as [H|[H|H]].
  - exfalso. exact (NB a H ZA).
  - exact H.
  - exfalso. exact (NA b H ZB).
Qed.

Lemma addr_split: forall d L k, (d ⊕ L) ⊕ k = d ⊕ (L + k).
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia. Qed.

Definition cs3 (s0 s:store) :=
  s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Ltac cs3_tac :=
  match goal with
  | CS: cs3 ?s0 _ |- cs3 ?s0 _ =>
      let B1 := fresh in let B2 := fresh in let B3 := fresh in
      destruct CS as (B1 & B2 & B3); unfold cs3; repeat split;
      rewrite ?update_frame by discriminate; assumption
  | CS: callee_saved_eq ?s0 _ |- cs3 ?s0 _ =>
      let B0 := fresh in let B1 := fresh in let B2 := fresh in let B3 := fresh in
      let B4 := fresh in let B5 := fresh in
      destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold cs3; repeat split;
      rewrite ?update_frame by discriminate; assumption
  end.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Lemma cpb_empty: forall m M dd s, cpb m M M dd s 0.
Proof. intros. split. intros i I. lia. reflexivity. Qed.

Lemma cpb_store:
  forall m mb M dd s k a v, cpb m mb M dd s k -> k < 2^64 ->
  a mod 2^64 = (dd + k) mod 2^64 -> v mod 2^8 = m Ⓑ[s ⊕ k] ->
  cpb m mb (setmem 64 LittleE 1 M a v) dd s (k + 1).
Proof.
  intros m mb M dd s k a v [W F] K A V. split.
  - intros i I. destruct (N.lt_ge_cases i k) as [IK|IK].
    + rewrite getmem_noverlap. apply W, IK.
      intros [x [y [X [Y E]]]]. mlia.
    + replace i with k by lia.
      rewrite <- A, getmem_mod_l, getmem_setmem by discriminate. exact V.
  - intros b B. rewrite getmem_noverlap. apply F. lia.
    intros [x [y [X [Y E]]]]. mlia.
Qed.

(* bytes of the stack slots at rsp-j are outside d's Ld+n+1 bytes *)
Lemma slot_outside:
  forall d N rsp j a, ~ overlap 64 d N (rsp ⊖ 32) 32 -> (j = 8 \/ j = 16 \/ j = 24) ->
  msub 64 a (rsp ⊖ j) < 8 -> ~ (msub 64 a d < N).
Proof.
  intros d N rsp j a NOV J A H. apply NOV. exists (msub 64 a d), (32 - j + msub 64 a (rsp ⊖ j)).
  split. exact H. split. destruct J as [J|[J|J]]; subst j; lia.
  destruct J as [J|[J|J]]; subst j; mlia.
Qed.

Lemma src_outside:
  forall d Ld n src k, ~ overlap 64 (d ⊕ Ld) (n + 1) src n -> k < n ->
  ~ (msub 64 (src ⊕ k) (d ⊕ Ld) < k).
Proof.
  intros d Ld n src k NOV K H. apply NOV. exists (msub 64 (src ⊕ k) (d ⊕ Ld)), k.
  split. lia. split. exact K. mlia.
Qed.

Lemma slot_safe:
  forall d Ld n k rsp j a, ~ overlap 64 d (Ld + n + 1) (rsp ⊖ 32) 32 -> (j = 8 \/ j = 16 \/ j = 24) ->
  msub 64 a (rsp ⊖ j) < 8 -> k <= n ->
  ~ overlap 64 a 1 (d + Ld + k) 1 /\ ~ (msub 64 a (d ⊕ Ld) < k).
Proof.
  intros d Ld n k rsp j a NOV J A K. pose proof (slot_outside d _ rsp j a NOV J A) as AO. split.
  - intros [x [y [X [Y E]]]]. apply AO. mlia.
  - intro H. apply AO. mlia.
Qed.

Lemma qslot:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 32) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma prefix_store_noverlap:
  forall d Ld k i, i < k -> Ld + k < 2^64 -> ~ overlap 64 ((d ⊕ Ld) ⊕ i) 1 (d + Ld + k) 1.
Proof. intros d Ld k i I K [x [y [X [Y E]]]]. mlia. Qed.

Lemma frame_store_noverlap:
  forall b d Ld k, ~ (msub 64 b (d ⊕ Ld) < k + 1) -> Ld + k < 2^64 -> ~ overlap 64 b 1 (d + Ld + k) 1.
Proof. intros b d Ld k B K [x [y [X [Y E]]]]. apply B. mlia. Qed.

Lemma not_lt_succ: forall x k, ~ (x < k + 1) -> ~ (x < k).
Proof. intros. lia. Qed.

Lemma store_read:
  forall M d Ld k v, (setmem 64 LittleE 1 M (d + Ld + k) v) Ⓑ[d ⊕ (Ld + k)] = v mod 2^8.
Proof.
  intros. replace (d ⊕ (Ld + k)) with ((d + Ld + k) mod 2^64) by (f_equal; lia).
  rewrite getmem_mod_l, getmem_setmem by discriminate. reflexivity.
Qed.

Lemma mod_eqb_true: forall k n, k <= n -> n < 2^64 -> (k mod 2^64 =? n mod 2^64) = true -> k = n.
Proof.
  intros k n K NB H. apply N.eqb_eq in H. rewrite !N.mod_small in H by lia. exact H.
Qed.

Lemma mod_eqb_false: forall k n, k <= n -> (k mod 2^64 =? n mod 2^64) = false -> k < n.
Proof.
  intros k n K H. apply N.eqb_neq in H. destruct (N.eq_dec k n). subst. contradiction. lia.
Qed.

Lemma nz_succ: forall m s k, nz m s k -> m Ⓑ[s ⊕ k] <> 0 -> nz m s (k + 1).
Proof.
  intros m s k NZ B i I. destruct (N.lt_ge_cases i k). apply NZ. assumption.
  replace i with k by lia. exact B.
Qed.

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Definition strncat_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x134980 => true
  | _ => false end | _ => false end.

Definition strncat_post (s0:store) (m d src n:N) (s:store) :=
  s R_RAX = d /\
  (exists Ld K, nilfree m d Ld /\ m Ⓑ[d ⊕ Ld] = 0 /\ K <= n /\ nz m src K /\
     (K = n \/ m Ⓑ[src ⊕ K] = 0) /\
     (forall i, i < K -> s V_MEM64 Ⓑ[d ⊕ (Ld + i)] = m Ⓑ[src ⊕ i]) /\
     s V_MEM64 Ⓑ[d ⊕ (Ld + K)] = 0 /\
     (forall b, ~ (msub 64 b (d ⊕ Ld) < K + 1) -> 32 <= msub 64 b (s0 R_RSP ⊖ 32) ->
                s V_MEM64 Ⓑ[b] = m Ⓑ[b])) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strncat_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x134940 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13494d => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP]
                                    [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX] /\
                      s R_RDI = d /\ s R_R12 = d /\ s R_RBP = n /\ s R_RBX = src /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x13496a => Some (exists Ld k, nilfree m d Ld /\ m Ⓑ[d ⊕ Ld] = 0 /\ k <= n /\ nz m src k /\
                      cpb m (mb s0 m) (s V_MEM64) (d ⊕ Ld) src k /\
                      s R_RAX = d ⊕ (Ld + k) /\ s R_RDX = d ⊕ (Ld + n) /\ s R_RBX = src ⊕ k /\
                      s R_R12 = d /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x134980 => Some (strncat_post s0 m d src n s)
  | _ => None
  end | _ => None end.

Lemma strlen_in_strncat: strlen_amd64 ⊆2 strncat_program.
Proof. apply subset_updateall2. Qed.

Theorem strncat_correct:
  forall prog s t s' x' m d src n
         (STRNCAT: strncat_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x134940, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (OK: strncat_ok m d src n (s R_RSP)),
  satisfies_all prog (strncat_invs s m d src n) strncat_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n STRNCAT STRLEN ENTRY MDL MEM D S Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RDI 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strncat_program).
    unfold strncat_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strncat_invs.
    unfold strncat_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src n MDL MEM D S Nn OK RB RBXB RBPB R12B DB SB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncat_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B DB SB. rename t1 into t.
  pose proof OK as (Ld0 & NF0 & Z0 & LB & NOVds & NOVd & NOVs).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP CS]]]]].
    repeat x64_step.
    destruct CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B2.
    conj_tac.
    unfold cs3. repeat split; rewrite ?update_frame by discriminate; assumption.
  - (* call strlen(d) *)
    destruct PRE as [MEM [RDI [R12 [RBP [RBX [RSP CS]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strncat_program _ _ _ _ s2 nil _ s1 t MDL1 strncat_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strncat_program strlen_amd64 _ _ (strlen_invs s2 (s2 V_MEM64) d) strlen_exit).
    + apply strlen_in_strncat.
    + intros a s t' EXIT NOCODE. unfold strlen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strlen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; assumption) ].
    + intros a s t' NC. unfold strncat_invs, strncat_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strncat_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [RAX [NF Z]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame, update_updated in RSP' by discriminate.
      rewrite update_updated in MEM', NF, Z.
      destruct CS' as (C0&C1&C2&C3&C4&C5).
      rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      assert (KE: k = Ld0).
      { apply (nilfree_unique _ d k Ld0 NF Z).
        - intros i I. rewrite push4_frame by (apply (outside32 d (Ld0 + n + 1)); [exact NOVd | lia]).
          apply NF0, I.
        - rewrite push4_frame by (apply (outside32 d (Ld0 + n + 1)); [exact NOVd | lia]). exact Z0. }
      subst k.
      repeat x64_step.
      exists Ld0, 0. conj_tac.
      all: first
        [ lia | (intros i I; lia) | (unfold mb; apply cpb_empty)
        | (rewrite R12, N.add_0_r, N.add_comm; reflexivity)
        | (rewrite R12, RBP; f_equal; lia)
        | (rewrite C0, RBX, N.add_0_r, N.mod_small by assumption; reflexivity)
        | (destruct CS as (B3 & B4 & B5); unfold cs3; reg; rewrite C3, C4, C5; repeat split; assumption) ].
  - destruct PRE as [Ld [k [NF [Z [KN [NZ [CP [RAX [RDX [RBX [R12 [RSP CS]]]]]]]]]]]].
    assert (LE: Ld = Ld0) by exact (nilfree_unique m d Ld Ld0 NF Z NF0 Z0). subst Ld.
    assert (NB: n < 2^64) by (clear - LB; change (2^64) with (2 * 2^63); lia).
    assert (LK: Ld0 + k < 2^64) by (clear - LB KN; change (2^64) with (2 * 2^63); lia).
    assert (SR: k < n -> s1 V_MEM64 Ⓑ[src ⊕ k] = m Ⓑ[src ⊕ k]).
    { intro K. rewrite (proj2 CP) by (apply (src_outside d Ld0 n src k NOVds K)).
      unfold mb. apply push4_frame. apply (outside32 src n _ k NOVs K). }
    assert (SL: forall v j, (j = 8 \/ j = 16 \/ j = 24) ->
              (s1 V_MEM64 [Ⓑd + Ld0 + k := v]) Ⓠ[s0 R_RSP ⊖ j] = mb s0 m Ⓠ[s0 R_RSP ⊖ j]).
    { intros v j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
      destruct (slot_safe d Ld0 n k (s0 R_RSP) j a NOVd J A KN) as [S1 S2].
      rewrite getmem_noverlap by exact S1. exact (proj2 CP a S2). }
    assert (R24: mb s0 m Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX).
    { unfold mb. rewrite getmem_noverlap by exact (qslot _ 24 32 eq_refl).
      rewrite getmem_setmem by discriminate. apply N.mod_small. assumption. }
    assert (R16: mb s0 m Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP).
    { unfold mb. rewrite getmem_noverlap by exact (qslot _ 16 32 eq_refl).
      rewrite getmem_noverlap by exact (qslot _ 16 24 eq_refl).
      rewrite getmem_setmem by discriminate. apply N.mod_small. assumption. }
    assert (R8: mb s0 m Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R12).
    { unfold mb. rewrite getmem_noverlap by exact (qslot _ 8 32 eq_refl).
      rewrite getmem_noverlap by exact (qslot _ 8 24 eq_refl).
      rewrite getmem_noverlap by exact (qslot _ 8 16 eq_refl).
      rewrite getmem_setmem by discriminate. apply N.mod_small. assumption. }
    repeat x64_step.
    all: match goal with BC: (_ mod 2^64 =? _) = _ |- _ =>
           rewrite (N.mod_small k) in BC by (clear - KN NB; lia) end.
    + (* k = n: stop *)
      match goal with BC: (_ =? _) = true |- _ => apply N.eqb_eq in BC; rename BC into KE end.
      rewrite (SL 0 24), (SL 0 16), (SL 0 8), R24, R16, R8
        by (first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]).
      split. reflexivity.
      split. exists Ld0, k.
        split. exact NF0. split. exact Z0. split. exact KN. split. exact NZ. split. left. exact KE.
        split. intros i I. rewrite <- addr_split.
          rewrite getmem_noverlap by exact (prefix_store_noverlap d Ld0 k i I LK). exact (proj1 CP i I).
        split. rewrite store_read. reflexivity.
        intros b B1 B2. rewrite getmem_noverlap by exact (frame_store_noverlap b d Ld0 k B1 LK).
          rewrite (proj2 CP b (not_lt_succ _ _ B1)). unfold mb. apply push4_frame. exact B2.
      split. apply N.mod_small. exact RB.
      destruct CS as (C3 & C4 & C5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + (* src[k] = 0: stop *)
      match goal with BC: (_ =? n) = false |- _ => apply N.eqb_neq in BC end.
      assert (K1: k < n) by (clear - KN BC; lia).
      match goal with BC: (getmem _ _ _ _ _ =? 0) = true |- _ =>
        apply N.eqb_eq in BC; rewrite <- getmem_mod_l in BC; rewrite (SR K1) in BC; rename BC into ZK end.
      rewrite (SL 0 24), (SL 0 16), (SL 0 8), R24, R16, R8
        by (first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]).
      split. reflexivity.
      split. exists Ld0, k.
        split. exact NF0. split. exact Z0. split. exact KN. split. exact NZ. split. right. exact ZK.
        split. intros i I. rewrite <- addr_split.
          rewrite getmem_noverlap by exact (prefix_store_noverlap d Ld0 k i I LK). exact (proj1 CP i I).
        split. rewrite store_read. reflexivity.
        intros b B1 B2. rewrite getmem_noverlap by exact (frame_store_noverlap b d Ld0 k B1 LK).
          rewrite (proj2 CP b (not_lt_succ _ _ B1)). unfold mb. apply push4_frame. exact B2.
      split. apply N.mod_small. exact RB.
      destruct CS as (C3 & C4 & C5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + (* copy one byte *)
      match goal with BC: (_ =? n) = false |- _ => apply N.eqb_neq in BC end.
      assert (K1: k < n) by (clear - KN BC; lia).
      match goal with BC: (getmem _ _ _ _ _ =? 0) = false |- _ =>
        apply N.eqb_neq in BC; rewrite <- getmem_mod_l in BC; rewrite (SR K1) in BC; rename BC into NZK end.
      exists Ld0, (k + 1). conj_tac.
      all: first
        [ exact NF0 | exact Z0 | exact (nz_succ m src k NZ NZK) | (clear - K1; lia)
        | (apply cpb_store;
           [ exact CP | (clear - LK; lia) | rewrite N.add_mod_idemp_l by discriminate; reflexivity
           | rewrite N.mod_small by apply (getmem_bound 64 LittleE 1);
             rewrite <- getmem_mod_l; apply SR, K1 ])
        | (rewrite ?N.add_mod_idemp_l, ?N.add_mod_idemp_r by discriminate; f_equal; pure_lia)
        | cs3_tac ].
Qed.

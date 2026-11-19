(* wcscat -- concatenate two wide strings (musl x86_64, C), composed with
   wcslen and wcscpy

   SEMANTICS
   ---------
   musl's wcscat (src/string/wcscat.c) is

       wcscpy(dest + wcslen(dest), src);
       return dest;

   The binary saves RBX (= dest), spills src to its frame, CALLs wcslen
   (0x13c380), then CALLs wcscpy (0x13c350) on dest + 4 wcslen(dest).  Both
   callees' contracts (wcslen_proof.v, wcscpy_proof.v) are used through
   call_leaf_ni.

   SPECIFICATION (man 3 wcscat, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     wchar_t *wcscat(wchar_t *restrict dest, const wchar_t *restrict src);
     wcscat appends a copy of the wide string src, including its
     terminating L'\0', to the end of the wide string dest.  The strings
     must not overlap and dest must have room for the result.  It returns
     dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcscat at 0x65e31, wcslen at 0x3c380, wcscpy at 0x3c350 (Ghidra
            image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcscat_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.  (wcscpy's contract is by a second Claude session.)

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dest, RSI = src; RSP = rsp; m = memory.  Precondition
            (wcscat_ok): dest and src are wide strings of lengths Ld and Ls;
            4(Ld+Ls+1) < 2^63; the 4(Ls+1) bytes at dest+4Ld do not overlap
            the 4(Ls+1) bytes at src; the 4(Ld+Ls+1) bytes at dest and the
            4(Ls+1) bytes at src do not overlap the 32 bytes below rsp.
   Output:  At the RET (0x165e59): RAX = dest; dest[Ld+i] = src[i] for
            i <= Ls (32-bit words); every byte outside the 4(Ls+1) bytes at
            dest+4Ld and the 32 bytes below rsp is unchanged.  RSP = rsp;
            RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcscat_amd64 CoqEtTu.programs.wcslen_amd64
               CoqEtTu.programs.wcscpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_wcopy.
Require Import CoqEtTu.proofs.wcslen_proof CoqEtTu.proofs.wcscpy_proof.
Open Scope N.

Definition wcscat_program : program :=
  updateall2 (updateall2 wcscat_amd64 wcslen_amd64) wcscpy_amd64.

Theorem wcscat_welltyped: welltyped_prog x64typctx wcscat_amd64.
Proof. exact wcscat_amd64.welltyped. Qed.

Lemma wcscat_program_welltyped: welltyped_prog x64typctx wcscat_program.
Proof.
  intros s a. unfold wcscat_program, updateall2, updateall.
  destruct (wcscpy_amd64 s a) as [[sz q]|] eqn:SC.
    pose proof (wcscpy_welltyped s a) as WT. rewrite SC in WT. exact WT.
  destruct (wcslen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (wcslen_welltyped s a) as WT. rewrite SL in WT. exact WT.
  apply wcscat_welltyped.
Qed.

Lemma wcslen_in_wcscat: wcslen_amd64 ⊆2 wcscat_program.
Proof.
  intros s a insn SL. unfold wcscat_program, updateall2, updateall.
  destruct (wcscpy_amd64 s a) eqn:SC.
  - exfalso. revert SC SL. unfold wcscpy_amd64, wcslen_amd64.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  - rewrite SL. reflexivity.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition wcscat_ok (m d src rsp:N) :=
  exists Ld Ls, wnilfree m d Ld /\ m Ⓓ[d ⊕ 4*Ld] = 0 /\ nzw m src Ls /\ m Ⓓ[src ⊕ 4*Ls] = 0 /\
    ~ overlap 64 (d ⊕ 4*Ld) (4*(Ls+1)) src (4*(Ls+1)) /\ 4*(Ld+Ls+1) < 2^63 /\
    ~ overlap 64 d (4*(Ld+Ls+1)) (rsp ⊖ 32) 32 /\ ~ overlap 64 src (4*(Ls+1)) (rsp ⊖ 32) 32.

Definition wcscat_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165e59 => true
  | _ => false end | _ => false end.

Definition wcscat_post (s0:store) (m d src:N) (s:store) :=
  s R_RAX = d /\
  (exists Ld Ls, wnilfree m d Ld /\ m Ⓓ[d ⊕ 4*Ld] = 0 /\ nzw m src Ls /\ m Ⓓ[src ⊕ 4*Ls] = 0 /\
     (forall i, i < Ls + 1 -> s V_MEM64 Ⓓ[(d ⊕ 4*Ld) ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]) /\
     (forall b, ~ (msub 64 b (d ⊕ 4*Ld) < 4*(Ls+1)) -> 32 <= msub 64 b (s0 R_RSP ⊖ 32) ->
                s V_MEM64 Ⓑ[b] = m Ⓑ[b])) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition cs_but_rbx (s0 s:store) :=
  s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
  s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition wcscat_invs (s0:store) (m d src:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165e31 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165e3e => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := src] /\
                      s R_RDI = d /\ s R_RBX = d /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs_but_rbx s0 s)
  | 0x165e4c => Some (exists Ld, wnilfree m d Ld /\ m Ⓓ[d ⊕ 4*Ld] = 0 /\
                      s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := src]
                                    [Ⓠs0 R_RSP ⊖ 32 := 0x165e43] /\
                      s R_RDI = d ⊕ 4*Ld /\ s R_RSI = src /\ s R_RBX = d /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs_but_rbx s0 s)
  | 0x165e59 => Some (wcscat_post s0 m d src s)
  | _ => None
  end | _ => None end.

(* ---- address facts, each proved in an empty context ---- *)

Lemma wnilfree_unique:
  forall m p k L, wnilfree m p k -> m Ⓓ[p ⊕ 4*k] = 0 -> wnilfree m p L -> m Ⓓ[p ⊕ 4*L] = 0 -> k = L.
Proof.
  intros m p k L NK ZK NL ZL. destruct (N.lt_trichotomy k L) as [H|[H|H]].
  - exfalso. apply (NL k H ZK).
  - exact H.
  - exfalso. apply (NK L H ZL).
Qed.

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

(* the dest words up to Ld are inside the dest area *)
Lemma dst_sub:
  forall d Ld Ls rsp, ~ overlap 64 d (4*(Ld+Ls+1)) (rsp ⊖ 32) 32 ->
  ~ overlap 64 d (4*(Ld+1)) (rsp ⊖ 32) 32.
Proof.
  intros d Ld Ls rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. lia. split. exact J. exact E.
Qed.

Lemma app_sub:
  forall d Ld Ls rsp, ~ overlap 64 d (4*(Ld+Ls+1)) (rsp ⊖ 32) 32 ->
  ~ overlap 64 (d ⊕ 4*Ld) (4*(Ls+1)) (rsp ⊖ 32) 32.
Proof.
  intros d Ld Ls rsp NOV [i [j [I [J E]]]]. apply NOV. exists (4*Ld + i), j. split. lia. split. exact J.
  rewrite <- E, N.add_mod_idemp_l by discriminate. f_equal. lia.
Qed.

(* bytes of a stack slot at rsp-j lie outside the appended area *)
Lemma slot_out:
  forall dd N rsp j a, ~ overlap 64 dd N (rsp ⊖ 32) 32 -> (j = 8 \/ j = 16 \/ j = 32) ->
  msub 64 a (rsp ⊖ j) < 8 -> ~ (msub 64 a dd < N).
Proof.
  intros dd N rsp j a NOV J A H. apply NOV. exists (msub 64 a dd), (32 - j + msub 64 a (rsp ⊖ j)).
  split. exact H. split. destruct J as [J|[J|J]]; subst j; lia.
  destruct J as [J|[J|J]]; subst j; mlia.
Qed.

Lemma qslot:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 32) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem wcscat_correct:
  forall prog s t s' x' m d src
         (WCSCAT: wcscat_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog) (WCSCPY: wcscpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165e31, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src)
         (OK: wcscat_ok m d src (s R_RSP)),
  satisfies_all prog (wcscat_invs s m d src) wcscat_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src WCSCAT WCSLEN WCSCPY ENTRY MDL MEM D S OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcscat_program).
    unfold wcscat_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcscat_invs.
    unfold wcscat_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src MDL MEM D S OK RB RBXB SB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscat_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB SB. rename t1 into t.
  pose proof OK as (Ld0 & Ls & NL0 & ZL0 & NZs & Zs & NOVds & LB & OVd & OVs).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [RSP CS]]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0.
    conj_tac. unfold cs_but_rbx; repeat split; rewrite ?update_frame by discriminate; assumption.
  - destruct PRE as [MEM [RDI [RBX [RSP CS]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcscat_program _ _ _ _ s2 nil _ s1 t MDL1 wcscat_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni wcscat_program wcslen_amd64 _ _ (wcslen_invs s2 (s2 V_MEM64) d) wcslen_exit).
    + apply wcslen_in_wcscat.
    + intros a s t' EXIT NOCODE. unfold wcslen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcslen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
    + intros a s t' NC. unfold wcscat_invs, wcscat_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcscat_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [NF [Z RAX]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM', NF, Z.
      destruct CS' as (C0&C1&C2&C3&C4&C5).
      rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      assert (KL: k = Ld0).
      { apply (wnilfree_unique _ d _ Ld0 NF Z).
        - intros i I. rewrite (push3_word m _ _ _ _ d (Ld0 + 1) i (dst_sub d Ld0 Ls _ OVd)) by (clear - I; lia).
          apply NL0, I.
        - rewrite (push3_word m _ _ _ _ d (Ld0 + 1) Ld0 (dst_sub d Ld0 Ls _ OVd)) by (clear; lia). exact ZL0. }
      subst k. rewrite (wcslen_ret Ld0 ltac:(clear - LB; lia)) in RAX.
      repeat x64_step.
      exists Ld0. conj_tac.
      * rewrite RBX, N.mul_comm. reflexivity.
      * destruct CS as (B1 & B2 & B3 & B4 & B5). unfold cs_but_rbx. reg.
        rewrite C1, C2, C3, C4, C5. repeat split; assumption.
  - destruct PRE as [Ld [NL [ZL [MEM [RDI [RSI [RBX [RSP CS]]]]]]]].
    assert (LE: Ld = Ld0) by exact (wnilfree_unique m d Ld Ld0 NL ZL NL0 ZL0). subst Ld.
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcscat_program _ _ _ _ s2 nil _ s1 t MDL1 wcscat_program_welltyped).
    intro MDL2.
    set (M2 := m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := src] [Ⓠs0 R_RSP ⊖ 32 := 1465937]) in *.
    assert (S2M: s2 V_MEM64 = M2) by (unfold s2; apply update_updated).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 32) by (unfold s2; rewrite update_frame by discriminate; apply update_updated).
    assert (SRCW: forall i, i < Ls + 1 -> M2 Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i])
      by (intros i I; unfold M2; exact (push3_word m _ _ _ _ src (Ls + 1) i OVs I)).
    pose proof (app_sub d Ld0 Ls _ OVd) as OVa.
    eapply (call_leaf_ni wcscat_program wcscpy_amd64 _ _
              (wcscpy_invs s2 (s2 V_MEM64) (d ⊕ 4*Ld0) src Ls) wcscpy_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcscpy_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcscpy_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) | idtac ].
      rewrite S2M. split; [|split; [|split]].
      * intros i I. rewrite SRCW by (clear - I; lia). apply NZs, I.
      * rewrite SRCW by (clear; lia). exact Zs.
      * exact NOVds.
      * clear - LB. lia.
    + intros a s t' NC. unfold wcscat_invs, wcscat_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcscat_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [[CPY FR] [RSP' CS']]].
      rewrite S2M in CPY, FR. rewrite S2R in RSP'.
      assert (RQ: forall j, (j = 8 \/ j = 16 \/ j = 32) -> s' V_MEM64 Ⓠ[s0 R_RSP ⊖ j] = M2 Ⓠ[s0 R_RSP ⊖ j]).
      { intros j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
        apply FR. exact (slot_out _ _ _ j a OVa J A). }
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 32] = 1465937).
      { rewrite RQ by (right; right; reflexivity). unfold M2. rewrite getmem_setmem by discriminate. reflexivity. }
      assert (R8: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBX).
      { rewrite RQ by (left; reflexivity). unfold M2.
        rewrite getmem_noverlap by exact (qslot _ 8 32 eq_refl).
        rewrite getmem_noverlap by exact (qslot _ 8 16 eq_refl).
        rewrite getmem_setmem by discriminate. apply N.mod_small; assumption. }
      x64_step. rewrite RA. repeat x64_step.
      assert (RBXs: s' R_RBX = d) by
        (rewrite (proj1 CS'); unfold s2; reg; exact RBX).
      assert (CSb: s' R_RBP = s0 R_RBP /\ s' R_R12 = s0 R_R12 /\ s' R_R13 = s0 R_R13 /\
                   s' R_R14 = s0 R_R14 /\ s' R_R15 = s0 R_R15) by
        (destruct CS' as (_ & B1 & B2 & B3 & B4 & B5); rewrite B1, B2, B3, B4, B5;
         unfold s2; reg; destruct CS as (C1 & C2 & C3 & C4 & C5); repeat split; assumption).
      rewrite ?R8.
      split. exact RBXs.
      split.
      { exists Ld0, Ls. split. exact NL0. split. exact ZL0. split. exact NZs. split. exact Zs. split.
        - intros i I. rewrite CPY by exact I. apply SRCW, I.
        - intros b B1 B2. rewrite (FR b B1). unfold M2. apply push3_32. exact B2. }
      split. apply N.mod_small. exact RB.
      destruct CSb as (C1 & C2 & C3 & C4 & C5).
      unfold callee_saved_eq. repeat split; reg; sassumption.
Qed.

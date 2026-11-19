(* wcsncat -- append at most n wide characters (musl x86_64, C), composed
   with wcslen

   SEMANTICS
   ---------
   musl's wcsncat (src/string/wcsncat.c) is

       wchar_t *a = d;
       d += wcslen(d);
       while (n && *s) n--, *d++ = *s++;
       *d++ = 0;
       return a;

   The binary saves R12 (= d), RBP (= s) and RBX (= n), CALLs wcslen
   (0x13c380) and copies 32-bit words while counting RBX down.  wcslen's
   contract (wcslen_proof.v) is used through call_leaf_ni.

   SPECIFICATION (man 3 wcsncat, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     wchar_t *wcsncat(wchar_t dest[restrict .n], const wchar_t src[restrict .n],
                      size_t n);
     wcsncat appends at most n wide characters of src (stopping at its
     L'\0') to the end of the wide string dest and then adds a terminating
     L'\0'.  The strings must not overlap.  It returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcsncat at 0x34b80, wcslen at 0x3c380 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcsncat_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, RSI = src, RDX = n; RSP = rsp; m = memory.
            Precondition (wcsncat_ok): d is a wide string of length Ld;
            4(Ld+n+1) < 2^63; the 4(n+1) bytes at d+4Ld do not overlap the
            4n bytes at src; the 4(Ld+n+1) bytes at d and the 4n bytes at
            src do not overlap the 32 bytes below rsp.  src need not be
            terminated within n wide characters.
   Output:  At the RET (0x134bc7): RAX = d; there is K <= n such that the
            words src[0..K) are nonzero and K = n or src[K] = 0; d[Ld+i] =
            src[i] for i < K and d[Ld+K] = 0 (32-bit words); every byte
            outside the 4(K+1) bytes at d+4Ld and the 32 bytes below rsp is
            unchanged.  RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcsncat_amd64 CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_wcopy.
Require Import CoqEtTu.proofs.wcslen_proof.
Open Scope N.

Definition wcsncat_program : program := updateall2 wcsncat_amd64 wcslen_amd64.

Theorem wcsncat_welltyped: welltyped_prog x64typctx wcsncat_amd64.
Proof. exact wcsncat_amd64.welltyped. Qed.

Lemma wcsncat_program_welltyped: welltyped_prog x64typctx wcsncat_program.
Proof.
  intros s a. unfold wcsncat_program, updateall2, updateall.
  destruct (wcslen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (wcslen_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply wcsncat_welltyped.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition wcsncat_ok (m d src n rsp:N) :=
  exists Ld, wnilfree m d Ld /\ m Ⓓ[d ⊕ 4*Ld] = 0 /\ 4*(Ld+n+1) < 2^63 /\
    ~ overlap 64 (d ⊕ 4*Ld) (4*(n+1)) src (4*n) /\
    ~ overlap 64 d (4*(Ld+n+1)) (rsp ⊖ 32) 32 /\ ~ overlap 64 src (4*n) (rsp ⊖ 32) 32.

Definition mb (s0:store) (m:N) :=
  m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX]
    [Ⓠs0 R_RSP ⊖ 32 := 0x134b92].

Definition cs3 (s0 s:store) :=
  s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition wcsncat_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x134bc7 => true
  | _ => false end | _ => false end.

Definition wcsncat_post (s0:store) (m d src n:N) (s:store) :=
  s R_RAX = d /\
  (exists Ld K, wnilfree m d Ld /\ m Ⓓ[d ⊕ 4*Ld] = 0 /\ K <= n /\ nzw m src K /\
     (K = n \/ m Ⓓ[src ⊕ 4*K] = 0) /\
     (forall i, i < K -> s V_MEM64 Ⓓ[(d ⊕ 4*Ld) ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]) /\
     s V_MEM64 Ⓓ[(d ⊕ 4*Ld) ⊕ 4*K] = 0 /\
     (forall b, ~ (msub 64 b (d ⊕ 4*Ld) < 4*(K+1)) -> 32 <= msub 64 b (s0 R_RSP ⊖ 32) ->
                s V_MEM64 Ⓑ[b] = m Ⓑ[b])) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wcsncat_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x134b80 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134b8d => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP]
                                    [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX] /\
                      s R_RDI = d /\ s R_R12 = d /\ s R_RBP = src /\ s R_RBX = n /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x134bae => Some (exists Ld k, wnilfree m d Ld /\ m Ⓓ[d ⊕ 4*Ld] = 0 /\ k <= n /\ nzw m src k /\
                      wcpf (mb s0 m) (s V_MEM64) (d ⊕ 4*Ld) src k /\
                      s R_RAX = (d ⊕ 4*Ld) ⊕ 4*k /\ s R_RBP = src ⊕ 4*k /\ s R_RBX = n - k /\
                      s R_R12 = d /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x134bc7 => Some (wcsncat_post s0 m d src n s)
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

Lemma word_byte32:
  forall x N rsp i a, ~ overlap 64 x (4*N) (rsp ⊖ 32) 32 -> i < N -> msub 64 a (x ⊕ 4*i) < 4 ->
  32 <= msub 64 a (rsp ⊖ 32).
Proof.
  intros x N rsp i a NOV I A.
  destruct (N.le_gt_cases 32 (msub 64 a (rsp ⊖ 32))) as [H|H]. exact H. exfalso.
  apply NOV. exists (4*i + msub 64 a (x ⊕ 4*i)), (msub 64 a (rsp ⊖ 32)).
  split. lia. split. exact H. mlia.
Qed.

Lemma push4_word:
  forall m rsp v1 v2 v3 v4 x N i, ~ overlap 64 x (4*N) (rsp ⊖ 32) 32 -> i < N ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 24 := v3] [Ⓠrsp ⊖ 32 := v4]) Ⓓ[x ⊕ 4*i] = m Ⓓ[x ⊕ 4*i].
Proof.
  intros m rsp v1 v2 v3 v4 x N i NOV I. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply push4_frame. exact (word_byte32 x N rsp i a NOV I A).
Qed.

Lemma dst_sub:
  forall d Ld n rsp, ~ overlap 64 d (4*(Ld+n+1)) (rsp ⊖ 32) 32 ->
  ~ overlap 64 d (4*(Ld+1)) (rsp ⊖ 32) 32.
Proof.
  intros d Ld n rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. lia. split. exact J. exact E.
Qed.

Lemma app_sub:
  forall d Ld n rsp, ~ overlap 64 d (4*(Ld+n+1)) (rsp ⊖ 32) 32 ->
  ~ overlap 64 (d ⊕ 4*Ld) (4*(n+1)) (rsp ⊖ 32) 32.
Proof.
  intros d Ld n rsp NOV [i [j [I [J E]]]]. apply NOV. exists (4*Ld + i), j. split. lia. split. exact J.
  rewrite <- E, N.add_mod_idemp_l by discriminate. f_equal. lia.
Qed.

(* a byte of source word k is outside the first k appended words *)
Lemma src_byte_out:
  forall dd n src k a, ~ overlap 64 dd (4*(n+1)) src (4*n) -> k < n -> msub 64 a (src ⊕ 4*k) < 4 ->
  ~ (msub 64 a dd < 4*k).
Proof.
  intros dd n src k a NOV K A H. apply NOV. exists (msub 64 a dd), (4*k + msub 64 a (src ⊕ 4*k)).
  split. lia. split. lia. mlia.
Qed.

Lemma word_store_noverlap:
  forall dd i k, i < k -> 4*(k+1) < 2^63 -> ~ overlap 64 (dd ⊕ 4*i) 4 (dd ⊕ 4*k) 4.
Proof. intros dd i k I K [x [y [X [Y E]]]]. mlia. Qed.

Lemma byte_store_noverlap:
  forall b dd k, ~ (msub 64 b dd < 4*(k+1)) -> 4*(k+1) < 2^63 -> ~ overlap 64 b 1 (dd ⊕ 4*k) 4.
Proof. intros b dd k B K [x [y [X [Y E]]]]. apply B. mlia. Qed.

Lemma not_lt_word: forall x k, ~ (x < 4*(k+1)) -> ~ (x < 4*k).
Proof. intros. lia. Qed.

Lemma slot_base: forall rsp j, (j = 8 \/ j = 16 \/ j = 24) -> (rsp ⊖ 32 + (32 - j)) mod 2^64 = rsp ⊖ j.
Proof. intros rsp j J. destruct J as [J|[J|J]]; subst j; mlia. Qed.

Lemma slot_out:
  forall dd N rsp j a, ~ overlap 64 dd N (rsp ⊖ 32) 32 -> (j = 8 \/ j = 16 \/ j = 24) ->
  msub 64 a (rsp ⊖ j) < 8 -> ~ (msub 64 a dd < N).
Proof.
  intros dd N rsp j a NOV J A H. apply NOV. exists (msub 64 a dd), (32 - j + msub 64 a (rsp ⊖ j)).
  split. exact H. split. destruct J as [J|[J|J]]; subst j; lia.
  rewrite add_msub. rewrite N.add_assoc, <- N.add_mod_idemp_l by discriminate.
  rewrite (slot_base rsp j J), add_msub. reflexivity.
Qed.

Lemma msub_add_r: forall a d x, msub 64 a (d ⊕ x) = msub 64 (msub 64 a d) x.
Proof. intros. unfold msub. change (2^64) with 18446744073709551616. lia. Qed.

Lemma app_byte:
  forall a d Ld n k, ~ (msub 64 a d < 4*(Ld+n+1)) -> k <= n ->
  ~ (msub 64 a (d ⊕ 4*Ld) < 4*(k+1)).
Proof.
  intros a d Ld n k AO K. rewrite msub_add_r.
  assert (U: msub 64 a d < 2^64) by apply msub_lt.
  set (u := msub 64 a d) in *. clearbody u. intro H. apply AO. clear AO.
  unfold msub in H. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma slot_byte:
  forall d Ld n k rsp j a, ~ overlap 64 d (4*(Ld+n+1)) (rsp ⊖ 32) 32 -> (j = 8 \/ j = 16 \/ j = 24) ->
  msub 64 a (rsp ⊖ j) < 8 -> k <= n -> 4*(Ld+n+1) < 2^63 ->
  ~ overlap 64 a 1 ((d ⊕ 4*Ld) ⊕ 4*k) 4 /\ ~ (msub 64 a (d ⊕ 4*Ld) < 4*k).
Proof.
  intros d Ld n k rsp j a NOV J A K NB.
  pose proof (app_byte a d Ld n k (slot_out d _ rsp j a NOV J A) K) as AB.
  split.
  - apply byte_store_noverlap. exact AB. lia.
  - exact (not_lt_word _ _ AB).
Qed.

Lemma qslot:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 32) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma word_store_noverlap':
  forall dd a i k, a mod 2^64 = (dd + 4*k) mod 2^64 -> i < k -> 4*(k+1) < 2^63 ->
  ~ overlap 64 (dd ⊕ 4*i) 4 a 4.
Proof.
  intros dd a i k A I K [x [y [X [Y E]]]]. mlia.
Qed.

Lemma byte_store_noverlap':
  forall b dd a k, a mod 2^64 = (dd + 4*k) mod 2^64 -> ~ (msub 64 b dd < 4*(k+1)) -> 4*(k+1) < 2^63 ->
  ~ overlap 64 b 1 a 4.
Proof.
  intros b dd a k A B K [x [y [X [Y E]]]]. apply B. mlia.
Qed.

Lemma store_addr: forall d L k, (d + L + k) mod 2^64 = ((d ⊕ L) + k) mod 2^64.
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. reflexivity. Qed.

Lemma nz_word: forall (M:memory) a, M Ⓓ[a] < 2^32.
Proof. intros. apply (getmem_bound 64 LittleE 4). Qed.

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem wcsncat_correct:
  forall prog s t s' x' m d src n
         (WCSNCAT: wcsncat_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x134b80, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (OK: wcsncat_ok m d src n (s R_RSP)),
  satisfies_all prog (wcsncat_invs s m d src n) wcsncat_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n WCSNCAT WCSLEN ENTRY MDL MEM D S Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RDI 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcsncat_program).
    unfold wcsncat_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcsncat_invs.
    unfold wcsncat_program, updateall2, updateall in NOCODE.
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
  eapply models_at_invariant; try eassumption. apply wcsncat_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B DB SB. rename t1 into t.
  pose proof OK as (Ld0 & NL0 & ZL0 & LB & NOVds & NOVd & NOVs).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP CS]]]]].
    repeat x64_step.
    destruct CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B2.
    conj_tac.
    unfold cs3. repeat split; rewrite ?update_frame by discriminate; assumption.
  - destruct PRE as [MEM [RDI [R12 [RBP [RBX [RSP CS]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcsncat_program _ _ _ _ s2 nil _ s1 t MDL1 wcsncat_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni wcsncat_program wcslen_amd64 _ _ (wcslen_invs s2 (s2 V_MEM64) d) wcslen_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcslen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcslen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
    + intros a s t' NC. unfold wcsncat_invs, wcsncat_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcsncat_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [NF [Z RAX]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM', NF, Z.
      destruct CS' as (C0&C1&C2&C3&C4&C5).
      rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      assert (KL: k = Ld0).
      { apply (wnilfree_unique _ d _ Ld0 NF Z).
        - intros i I. rewrite (push4_word m _ _ _ _ _ d (Ld0 + 1) i (dst_sub d Ld0 n _ NOVd)) by (clear - I; lia).
          apply NL0, I.
        - rewrite (push4_word m _ _ _ _ _ d (Ld0 + 1) Ld0 (dst_sub d Ld0 n _ NOVd)) by (clear; lia). exact ZL0. }
      subst k. rewrite (wcslen_ret Ld0 ltac:(clear - LB; lia)) in RAX.
      repeat x64_step.
      exists Ld0, 0. conj_tac.
      * apply N.le_0_l.
      * intros i I. exfalso. exact (N.nlt_0_r i I).
      * unfold mb. apply wcpf_empty.
      * rewrite R12, N.mul_0_r, N.add_0_r, N.mod_mod, N.mul_comm by discriminate. reflexivity.
      * rewrite C1, RBP, N.mul_0_r, N.add_0_r. symmetry. apply N.mod_small. exact SB.
      * rewrite C0, RBX, N.sub_0_r. reflexivity.
      * destruct CS as (B3 & B4 & B5). unfold cs3. reg. rewrite C3, C4, C5. repeat split; assumption.
  - destruct PRE as [Ld [k [NL [ZL [KN [NZ [CP [RAX [RBP [RBX [R12 [RSP CS]]]]]]]]]]]].
    assert (LE: Ld = Ld0) by exact (wnilfree_unique m d Ld Ld0 NL ZL NL0 ZL0). subst Ld.
    assert (NB4: 4*(k+1) < 2^63) by (clear - LB KN; lia).
    assert (AD: (d + 4*Ld0 + 4*k) mod 2^64 = ((d ⊕ 4*Ld0) + 4*k) mod 2^64) by apply store_addr.
    assert (SR: k < n -> s1 V_MEM64 Ⓓ[src ⊕ 4*k] = mb s0 m Ⓓ[src ⊕ 4*k]).
    { intro K. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
      exact (proj2 CP a (src_byte_out (d ⊕ 4*Ld0) n src k a NOVds K A)). }
    assert (SM: forall i, i < n -> mb s0 m Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i])
      by (intros i I; unfold mb; exact (push4_word m _ _ _ _ _ src n i NOVs I)).
    assert (SL: forall v j, (j = 8 \/ j = 16 \/ j = 24) ->
              (s1 V_MEM64 [Ⓓd + 4*Ld0 + 4*k := v]) Ⓠ[s0 R_RSP ⊖ j] = mb s0 m Ⓠ[s0 R_RSP ⊖ j]).
    { intros v j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
      destruct (slot_byte d Ld0 n k (s0 R_RSP) j a NOVd J A KN LB) as [S1 S2].
      rewrite getmem_noverlap.
      - exact (proj2 CP a S2).
      - intros [x [y [X [Y E]]]]. apply S1. exists x, y. split. exact X. split. exact Y.
        rewrite E, <- (N.add_mod_idemp_l (d + 4*Ld0 + 4*k)), AD by discriminate.
        reflexivity. }
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
    + (* n words copied *)
      match goal with BC: (_ - _ =? 0) = true |- _ => apply N.eqb_eq in BC end.
      assert (KE: k = n) by (clear - KN BC; lia).
      rewrite (SL 0 24), (SL 0 16), (SL 0 8), R24, R16, R8
        by (first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]).
      split. reflexivity.
      split. exists Ld0, k.
        split. exact NL0. split. exact ZL0. split. exact KN. split. exact NZ. split. left. exact KE.
        split. intros i I.
          rewrite getmem_noverlap by exact (word_store_noverlap' (d ⊕ 4*Ld0) _ i k AD I NB4).
          rewrite (proj1 CP i I). apply SM. clear - I KN; lia.
        split. rewrite <- AD, getmem_mod_l, getmem_setmem by discriminate. reflexivity.
        intros b B1 B2. rewrite getmem_noverlap by exact (byte_store_noverlap' b (d ⊕ 4*Ld0) _ k AD B1 NB4).
          rewrite (proj2 CP b (not_lt_word _ _ B1)). unfold mb. apply push4_frame. exact B2.
      split. apply N.mod_small. exact RB.
      destruct CS as (C3 & C4 & C5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + (* src[k] = 0 *)
      match goal with BC: (_ - _ =? 0) = false |- _ => apply N.eqb_neq in BC end.
      assert (K1: k < n) by (clear - KN BC; lia).
      match goal with BC: (getmem _ _ _ _ _ =? 0) = true |- _ =>
        apply N.eqb_eq in BC; rewrite <- getmem_mod_l in BC; rewrite (SR K1), (SM k K1) in BC; rename BC into ZK end.
      rewrite (SL 0 24), (SL 0 16), (SL 0 8), R24, R16, R8
        by (first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]).
      split. reflexivity.
      split. exists Ld0, k.
        split. exact NL0. split. exact ZL0. split. exact KN. split. exact NZ. split. right. exact ZK.
        split. intros i I.
          rewrite getmem_noverlap by exact (word_store_noverlap' (d ⊕ 4*Ld0) _ i k AD I NB4).
          rewrite (proj1 CP i I). apply SM. clear - I KN; lia.
        split. rewrite <- AD, getmem_mod_l, getmem_setmem by discriminate. reflexivity.
        intros b B1 B2. rewrite getmem_noverlap by exact (byte_store_noverlap' b (d ⊕ 4*Ld0) _ k AD B1 NB4).
          rewrite (proj2 CP b (not_lt_word _ _ B1)). unfold mb. apply push4_frame. exact B2.
      split. apply N.mod_small. exact RB.
      destruct CS as (C3 & C4 & C5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + (* copy word k *)
      match goal with BC: (_ - _ =? 0) = false |- _ => apply N.eqb_neq in BC end.
      assert (K1: k < n) by (clear - KN BC; lia).
      match goal with BC: (getmem _ _ _ _ _ =? 0) = false |- _ =>
        apply N.eqb_neq in BC; rewrite <- getmem_mod_l in BC; rewrite (SR K1), (SM k K1) in BC; rename BC into NZK end.
      exists Ld0, (k + 1). conj_tac.
      all: first
        [ exact NL0 | exact ZL0 | (clear - K1; lia) | exact (nzw_succ m src k NZ NZK)
        | (apply wcpf_store; [ exact CP | exact NB4 | exact AD
                             | rewrite N.mod_small by apply nz_word; rewrite <- getmem_mod_l; apply SR, K1 ])
        | (rewrite ?N.add_mod_idemp_l by discriminate; f_equal; pure_lia)
        | (f_equal; pure_lia)
        | (clear - K1 LB; unfold msub; change (2^64) with 18446744073709551616 in *;
           change (2^63) with 9223372036854775808 in *; lia)
        | (destruct CS as (C3 & C4 & C5); unfold cs3; repeat split; reg; assumption) ].
Qed.

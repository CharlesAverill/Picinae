(* wcsxfrm_l -- transform a wide string for collation (musl x86_64, C),
   composed with wcslen and wmemcpy

   SEMANTICS
   ---------
   musl's __wcsxfrm_l (src/locale/wcsxfrm.c), exported as wcsxfrm_l, is

       size_t l = wcslen(src);
       if (l < n) {
           wmemcpy(dest, src, l+1);
       } else if (n) {
           wmemcpy(dest, src, n-1);
           dest[n-1] = 0;
       }
       return l;

   The binary saves R12 (= dest), RBP (= src) and RBX (= n), CALLs wcslen
   (0x13c380), and on the two copying paths spills l and CALLs wmemcpy
   (0x13c3f0).  wcslen's contract (wcslen_proof.v) and wmemcpy's
   (wmemcpy_proof.v, by a second Claude session) are used through
   call_leaf_ni.

   SPECIFICATION (man 3 wcsxfrm, POSIX; paraphrased)
   ------------------------------------------------
     size_t wcsxfrm_l(wchar_t *restrict ws1, const wchar_t *restrict ws2,
                      size_t n, locale_t locale);
     wcsxfrm transforms ws2 so that wcscmp on transformed strings agrees
     with wcscoll and places at most n wide characters of the result,
     including the terminating L'\0', in ws1; it returns the length of the
     transformed string.  (musl's transformation is the identity; when the
     result does not fit, musl stores the first n-1 characters and a
     terminator.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            __wcsxfrm_l (wcsxfrm_l) at 0x46447, wcslen at 0x3c380, wmemcpy at
            0x3c3f0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcsxfrm_l_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dest, RSI = src, RDX = n (RCX = locale, ignored); RSP = rsp;
            m = memory.  Precondition (wxfrm_ok): src is a wide string of
            length L with 4(L+1) < 2^63 whose 4(L+1) bytes do not overlap the
            48 bytes below rsp; with W = L+1 if L < n and W = n otherwise,
            the 4W bytes at dest do not overlap the 4W bytes at src nor the
            48 bytes below rsp.
   Output:  At the RET (0x146478): RAX = L; the first W words at dest hold
            src[0..W) except that, when L >= n > 0, dest[n-1] = 0 (wxfrm_res);
            every byte outside the 4W bytes at dest and the 48 bytes below
            rsp is unchanged.  RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcsxfrm_l_amd64 CoqEtTu.programs.wcslen_amd64 CoqEtTu.programs.wmemcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_wcopy.
Require Import CoqEtTu.proofs.wcslen_proof CoqEtTu.proofs.wmemcpy_proof.
Open Scope N.

Definition wcsxfrm_l_program : program :=
  updateall2 (updateall2 wcsxfrm_l_amd64 wcslen_amd64) wmemcpy_amd64.

Theorem wcsxfrm_l_welltyped: welltyped_prog x64typctx wcsxfrm_l_amd64.
Proof. exact wcsxfrm_l_amd64.welltyped. Qed.

Lemma wcsxfrm_l_program_welltyped: welltyped_prog x64typctx wcsxfrm_l_program.
Proof.
  intros s a. unfold wcsxfrm_l_program, updateall2, updateall.
  destruct (wmemcpy_amd64 s a) as [[sz q]|] eqn:SC.
    pose proof (wmemcpy_welltyped s a) as WT. rewrite SC in WT. exact WT.
  destruct (wcslen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (wcslen_welltyped s a) as WT. rewrite SL in WT. exact WT.
  apply wcsxfrm_l_welltyped.
Qed.

Lemma wcslen_in_wxfrm: wcslen_amd64 ⊆2 wcsxfrm_l_program.
Proof.
  intros s a insn SL. unfold wcsxfrm_l_program, updateall2, updateall.
  destruct (wmemcpy_amd64 s a) eqn:SC.
  - exfalso. revert SC SL. unfold wmemcpy_amd64, wcslen_amd64.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  - rewrite SL. reflexivity.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition wnum (L n:N) := if L <? n then L + 1 else n.

Definition wxfrm_ok (m d s n rsp:N) :=
  exists L, wnilfree m s L /\ m Ⓓ[s ⊕ 4*L] = 0 /\ 4*(L+1) < 2^63 /\
    ~ overlap 64 s (4*(L+1)) (rsp ⊖ 48) 48 /\
    ~ overlap 64 d (4 * wnum L n) s (4 * wnum L n) /\ ~ overlap 64 d (4 * wnum L n) (rsp ⊖ 48) 48.

(* the words written: a copy, except a final terminator when truncating *)
Definition wxfrm_res (m M:memory) (d s L n:N) :=
  forall i, i < wnum L n ->
    M Ⓓ[d ⊕ 4*i] = if (n <=? L) && (i =? n - 1) then 0 else m Ⓓ[s ⊕ 4*i].

Definition wcsxfrm_l_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x146478 => true
  | _ => false end | _ => false end.

Definition wcsxfrm_l_post (s0:store) (m d src n:N) (s:store) :=
  (exists L, wnilfree m src L /\ m Ⓓ[src ⊕ 4*L] = 0 /\ s R_RAX = L /\
     wxfrm_res m (s V_MEM64) d src L n /\
     (forall b, ~ (msub 64 b d < 4 * wnum L n) -> 48 <= msub 64 b (s0 R_RSP ⊖ 48) ->
                s V_MEM64 Ⓑ[b] = m Ⓑ[b])) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition cs3 (s0 s:store) := s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition mpush (s0:store) (m:N) :=
  m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX].

Definition wcsxfrm_l_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x146447 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x14645b => Some (s V_MEM64 = mpush s0 m /\ s R_RDI = src /\ s R_R12 = d /\ s R_RBP = src /\
                      s R_RBX = n /\ s R_RSP = s0 R_RSP ⊖ 40 /\ cs3 s0 s)
  | 0x146488 => Some (exists L, wnilfree m src L /\ m Ⓓ[src ⊕ 4*L] = 0 /\ L < n /\
                      s V_MEM64 = mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := 0x146460] [Ⓠs0 R_RSP ⊖ 32 := L] /\
                      s R_RDI = d /\ s R_RSI = src /\ s R_RDX = L + 1 /\ s R_RSP = s0 R_RSP ⊖ 40 /\
                      s R_R12 = d /\ s R_RBP = src /\ s R_RBX = n /\ cs3 s0 s)
  | 0x1464a6 => Some (exists L, wnilfree m src L /\ m Ⓓ[src ⊕ 4*L] = 0 /\ n <= L /\ 0 < n /\
                      s V_MEM64 = mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := 0x146460] [Ⓠs0 R_RSP ⊖ 32 := L] /\
                      s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n - 1 /\ s R_RSP = s0 R_RSP ⊖ 40 /\
                      s R_R12 = d /\ s R_RBP = src /\ s R_RBX = n - 1 /\ cs3 s0 s)
  | 0x146478 => Some (wcsxfrm_l_post s0 m d src n s)
  | _ => None
  end | _ => None end.

(* ---- facts, each proved in an empty context ---- *)

Lemma qslot48:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 48) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Ltac sframe := unfold mpush;
  repeat (rewrite (stack_store_frame _ _ _ _ _ 48) by first [assumption | pure_lia]); reflexivity.

Lemma frameA: forall s0 m v b, 48 <= msub 64 b (s0 R_RSP ⊖ 48) ->
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := v]) Ⓑ[b] = m Ⓑ[b].
Proof. intros. sframe. Qed.

Lemma frameB: forall s0 m v w b, 48 <= msub 64 b (s0 R_RSP ⊖ 48) ->
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓑ[b] = m Ⓑ[b].
Proof. intros. sframe. Qed.

Lemma word_byte48:
  forall x N rsp i a, ~ overlap 64 x (4*N) (rsp ⊖ 48) 48 -> i < N -> msub 64 a (x ⊕ 4*i) < 4 ->
  48 <= msub 64 a (rsp ⊖ 48).
Proof.
  intros x N rsp i a NOV I A.
  destruct (N.le_gt_cases 48 (msub 64 a (rsp ⊖ 48))) as [H|H]. exact H. exfalso.
  apply NOV. exists (4*i + msub 64 a (x ⊕ 4*i)), (msub 64 a (rsp ⊖ 48)).
  split. lia. split. exact H. mlia.
Qed.

Lemma slots0: forall s0 m, s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 ->
  mpush s0 m Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX /\
  mpush s0 m Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\
  mpush s0 m Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R12.
Proof.
  intros s0 m B1 B2 B3. unfold mpush. split; [|split].
  - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot48 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot48 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma slotsB: forall s0 m v w, s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 -> v < 2^64 ->
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R12 /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 32] = v /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 48] = w mod 2^64.
Proof.
  intros s0 m v w B1 B2 B3 B4. unfold mpush. split; [|split; [|split; [|split]]].
  - rewrite getmem_noverlap by exact (qslot48 _ 24 48 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 24 32 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot48 _ 16 48 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 16 32 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot48 _ 8 48 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 8 32 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot48 _ 32 48 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_setmem by discriminate. reflexivity.
Qed.

Lemma slot_base: forall rsp j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32 \/ j = 48) ->
  (rsp ⊖ 48 + (48 - j)) mod 2^64 = rsp ⊖ j.
Proof. intros rsp j J. destruct J as [J|[J|[J|[J|J]]]]; subst j; mlia. Qed.

(* a stack slot's bytes are outside dest's area *)
Lemma slot_out:
  forall d N rsp j a, ~ overlap 64 d N (rsp ⊖ 48) 48 ->
  (j = 8 \/ j = 16 \/ j = 24 \/ j = 32 \/ j = 48) -> msub 64 a (rsp ⊖ j) < 8 -> ~ (msub 64 a d < N).
Proof.
  intros d N rsp j a NOV J A H. apply NOV. exists (msub 64 a d), (48 - j + msub 64 a (rsp ⊖ j)).
  split. exact H. split. destruct J as [J|[J|[J|[J|J]]]]; subst j; lia.
  rewrite add_msub. rewrite N.add_assoc, <- N.add_mod_idemp_l by discriminate.
  rewrite (slot_base rsp j J), add_msub. reflexivity.
Qed.

Lemma len_unique:
  forall m p k L, wnilfree m p k -> m Ⓓ[p ⊕ 4*k] = 0 -> wnilfree m p L -> m Ⓓ[p ⊕ 4*L] = 0 -> k = L.
Proof.
  intros m p k L NK ZK NL ZL. destruct (N.lt_trichotomy k L) as [H|[H|H]].
  - exfalso. apply (NL k H ZK).
  - exact H.
  - exfalso. apply (NK L H ZL).
Qed.

Lemma wnum_lt: forall L n, L < n -> wnum L n = L + 1.
Proof. intros. unfold wnum. destruct (N.ltb_spec L n). reflexivity. lia. Qed.

Lemma wnum_ge: forall L n, n <= L -> wnum L n = n.
Proof. intros. unfold wnum. destruct (N.ltb_spec L n). lia. reflexivity. Qed.

Lemma msub1: forall x, 0 < x -> x < 2^64 -> msub 64 x 1 = x - 1.
Proof. intros. mlia. Qed.

Lemma ovl_sub: forall x y n, ~ overlap 64 x (4*n) y (4*n) -> ~ overlap 64 x (4*(n-1)) y (4*(n-1)).
Proof. intros x y n NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. lia. split. lia. exact E. Qed.

Lemma ovl_sub1: forall x n r, ~ overlap 64 x (4*n) r 48 -> ~ overlap 64 x (4*(n-1)) r 48.
Proof. intros x n r NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. lia. split. exact J. exact E. Qed.

Lemma last_word_noverlap:
  forall d n i a, a mod 2^64 = (d + 4*(n-1)) mod 2^64 -> i < n - 1 -> 4*n < 2^63 ->
  ~ overlap 64 (d ⊕ 4*i) 4 a 4.
Proof. intros d n i a A I K [x [y [X [Y E]]]]. mlia. Qed.

Lemma last_byte_noverlap:
  forall b d n a, a mod 2^64 = (d + 4*(n-1)) mod 2^64 -> 0 < n -> ~ (msub 64 b d < 4*n) -> 4*n < 2^63 ->
  ~ overlap 64 b 1 a 4.
Proof. intros b d n a A N0 B K [x [y [X [Y E]]]]. apply B. mlia. Qed.

Lemma last_word_eq: forall d n, 0 < n -> d ⊕ 4*(n-1) = (d + (n - 1) * 4) mod 2^64.
Proof. intros. f_equal. lia. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem wcsxfrm_l_correct:
  forall prog s t s' x' m d src n
         (WXFRM: wcsxfrm_l_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog) (WMEMCPY: wmemcpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x146447, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (OK: wxfrm_ok m d src n (s R_RSP)),
  satisfies_all prog (wcsxfrm_l_invs s m d src n) wcsxfrm_l_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n WXFRM WCSLEN WMEMCPY ENTRY MDL MEM D S Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcsxfrm_l_program).
    unfold wcsxfrm_l_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcsxfrm_l_invs.
    unfold wcsxfrm_l_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src n MDL MEM D S Nn OK RB RBXB RBPB R12B NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsxfrm_l_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B NB. rename t1 into t.
  destruct OK as (L0 & NL0 & ZL0 & LB & OVs & NDS & OVd).
  destruct (slots0 s0 m R12B RBPB RBXB) as [U24 [U16 U8]].
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP CS]]]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B2. unfold mpush.
    conj_tac. unfold cs3. repeat split; reg; assumption.
  - destruct PRE as [MEM [RDI [R12 [RBP [RBX [RSP CS]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcsxfrm_l_program _ _ _ _ s2 nil _ s1 t MDL1 wcsxfrm_l_program_welltyped).
    intro MDL2.
    assert (SB: forall i, i < L0 + 1 -> (mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := 0x146460]) Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]).
    { intros i I. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
      apply frameA. exact (word_byte48 src (L0 + 1) _ i a OVs I A). }
    eapply (call_leaf_ni wcsxfrm_l_program wcslen_amd64 _ _ (wcslen_invs s2 (s2 V_MEM64) src) wcslen_exit).
    + apply wcslen_in_wxfrm.
    + intros a s t' EXIT NOCODE. unfold wcslen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcslen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
    + intros a s t' NC. unfold wcsxfrm_l_invs, wcsxfrm_l_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcsxfrm_l_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [NF [Z RAX]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM', NF, Z, RSP'.
      assert (KE: k = L0).
      { apply (len_unique _ src k L0 NF Z).
        - intros i I. rewrite SB by (clear - I; lia). apply NL0, I.
        - rewrite SB by (clear; lia). exact ZL0. }
      subst k. rewrite (wcslen_ret L0 ltac:(clear - LB; lia)) in RAX.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      repeat x64_step.
      * match goal with BC: (L0 <? _) = true |- _ => apply N.ltb_lt in BC; rename BC into LN end.
        exists L0. split. exact NL0. split. exact ZL0. split. rewrite <- RBX. exact LN.
        split. reflexivity. split. sassumption. split. sassumption.
        split. rewrite N.add_comm. apply N.mod_small. clear - LB; lia.
        repeat split; try sassumption.
        all: reg; rewrite ?C3, ?C4, ?C5; destruct CS as (B3 & B4 & B5); assumption.
      * match goal with BC: (L0 <? _) = false |- _ => apply N.ltb_ge in BC; rename BC into LN end.
        match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into N0 end.
        rewrite RBX in LN, N0.
        rewrite U24, U16, U8.
        split. exists L0. split. exact NL0. split. exact ZL0. split. reflexivity.
          split. intros i I. rewrite ?RBX, N0, (wnum_ge L0 0 (N.le_0_l L0)) in I. exfalso. exact (N.nlt_0_r i I).
          intros b B1 B2. apply frameA. exact B2.
        split. apply N.mod_small. exact RB.
        destruct CS as (B3 & B4 & B5). unfold callee_saved_eq. repeat split; reg;
          first [sassumption | (rewrite ?C3, ?C4, ?C5; sassumption)].
      * match goal with BC: (L0 <? _) = false |- _ => apply N.ltb_ge in BC; rename BC into LN end.
        match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into N0 end.
        rewrite RBX in LN, N0.
        assert (M1: msub 64 (s1 R_RBX) 1 = n - 1) by (rewrite RBX; apply msub1; [clear - N0; lia | exact NB]).
        exists L0. split. exact NL0. split. exact ZL0. split. exact LN. split. clear - N0; lia.
        split. reflexivity. split. sassumption. split. sassumption.
        split. exact M1. split. reflexivity. split. sassumption. split. sassumption. split. exact M1.
        unfold cs3. repeat split; reg; rewrite ?C3, ?C4, ?C5; destruct CS as (B3 & B4 & B5); assumption.
  - destruct PRE as [L [NL [ZL [LN [MEM [RDI [RSI [RDX [RSP [R12 [RBP [RBX CS]]]]]]]]]]]].
    assert (LE: L = L0) by exact (len_unique m src L L0 NL ZL NL0 ZL0). subst L.
    rewrite (wnum_lt L0 n LN) in NDS, OVd.
    assert (LB': L0 < 2^64) by (clear - LB; lia).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcsxfrm_l_program _ _ _ _ s2 nil _ s1 t MDL1 wcsxfrm_l_program_welltyped).
    intro MDL2.
    set (M3 := mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := L0] [Ⓠs0 R_RSP ⊖ 48 := 0x14648d]) in *.
    assert (S2M: s2 V_MEM64 = M3) by (unfold s2; apply update_updated).
    assert (SW: forall i, i < L0 + 1 -> M3 Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]).
    { intros i I. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
      unfold M3. apply frameB. exact (word_byte48 src (L0 + 1) _ i a OVs I A). }
    destruct (slotsB s0 m L0 0x14648d R12B RBPB RBXB LB') as [V24 [V16 [V8 [V32 V48]]]].
    fold M3 in V24, V16, V8, V32, V48.
    eapply (call_leaf_ni wcsxfrm_l_program wmemcpy_amd64 _ _ (wmemcpy_invs s2 (s2 V_MEM64) d src (L0 + 1)) wmemcpy_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wmemcpy_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wmemcpy_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) | idtac ].
      split. exact NDS. exact LB.
    + intros a s t' NC. unfold wcsxfrm_l_invs, wcsxfrm_l_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wmemcpy_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wmemcpy_exit _) eqn:EX; [|destruct PRE].
      unfold wmemcpy_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcsxfrm_l_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [[CPY FR] [RSP' CS']]].
      rewrite S2M in CPY, FR. unfold s2 in RSP'. rewrite update_frame, update_updated in RSP' by discriminate.
      assert (RQ: forall j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32 \/ j = 48) ->
                s' V_MEM64 Ⓠ[s0 R_RSP ⊖ j] = M3 Ⓠ[s0 R_RSP ⊖ j]).
      { intros j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
        exact (FR a (slot_out d _ _ j a OVd J A)). }
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 48] = 0x14648d)
        by (rewrite (RQ 48), V48 by (right; right; right; right; reflexivity); reflexivity).
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). unfold s2 in C0, C1, C2, C3, C4, C5.
      rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      x64_step. rewrite RA. repeat x64_step.
      rewrite (RQ 32), V32 by (right; right; right; left; reflexivity).
      rewrite (RQ 24), V24 by (right; right; left; reflexivity).
      rewrite (RQ 16), V16 by (right; left; reflexivity).
      rewrite (RQ 8), V8 by (left; reflexivity).
      split. exists L0. split. exact NL0. split. exact ZL0. split. reflexivity.
        split. intros i I. rewrite (wnum_lt L0 n LN) in I.
          replace ((n <=? L0) && (i =? n - 1))%bool with false by (destruct (N.leb_spec n L0); [exfalso; clear - LN H; lia | reflexivity]).
          rewrite CPY by exact I. apply SW, I.
        intros b B1 B2. rewrite (wnum_lt L0 n LN) in B1. rewrite (FR b B1). unfold M3. apply frameB. exact B2.
      split. apply N.mod_small. exact RB.
      destruct CS as (B3 & B4 & B5). unfold callee_saved_eq. repeat split; reg;
        first [sassumption | (rewrite ?C3, ?C4, ?C5; sassumption)].
  - destruct PRE as [L [NL [ZL [NL' [N0 [MEM [RDI [RSI [RDX [RSP [R12 [RBP [RBX CS]]]]]]]]]]]]].
    assert (LE: L = L0) by exact (len_unique m src L L0 NL ZL NL0 ZL0). subst L.
    rewrite (wnum_ge L0 n NL') in NDS, OVd.
    assert (LB': L0 < 2^64) by (clear - LB; lia).
    assert (NB4: 4*n < 2^63) by (clear - NL' LB; lia).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcsxfrm_l_program _ _ _ _ s2 nil _ s1 t MDL1 wcsxfrm_l_program_welltyped).
    intro MDL2.
    set (M3 := mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := L0] [Ⓠs0 R_RSP ⊖ 48 := 0x1464ab]) in *.
    assert (S2M: s2 V_MEM64 = M3) by (unfold s2; apply update_updated).
    assert (SW: forall i, i < L0 + 1 -> M3 Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]).
    { intros i I. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
      unfold M3. apply frameB. exact (word_byte48 src (L0 + 1) _ i a OVs I A). }
    destruct (slotsB s0 m L0 0x1464ab R12B RBPB RBXB LB') as [V24 [V16 [V8 [V32 V48]]]].
    fold M3 in V24, V16, V8, V32, V48.
    eapply (call_leaf_ni wcsxfrm_l_program wmemcpy_amd64 _ _ (wmemcpy_invs s2 (s2 V_MEM64) d src (n - 1)) wmemcpy_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wmemcpy_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wmemcpy_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) | idtac ].
      split. apply ovl_sub, NDS. clear - NB4; lia.
    + intros a s t' NC. unfold wcsxfrm_l_invs, wcsxfrm_l_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wmemcpy_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wmemcpy_exit _) eqn:EX; [|destruct PRE].
      unfold wmemcpy_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcsxfrm_l_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [[CPY FR] [RSP' CS']]].
      rewrite S2M in CPY, FR. unfold s2 in RSP'. rewrite update_frame, update_updated in RSP' by discriminate.
      assert (FRn: forall b, ~ (msub 64 b d < 4*n) -> s' V_MEM64 Ⓑ[b] = M3 Ⓑ[b])
        by (intros b B; apply FR; clear - B; lia).
      assert (RQ: forall j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32 \/ j = 48) ->
                s' V_MEM64 Ⓠ[s0 R_RSP ⊖ j] = M3 Ⓠ[s0 R_RSP ⊖ j]).
      { intros j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
        exact (FRn a (slot_out d _ _ j a OVd J A)). }
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 48] = 0x1464ab)
        by (rewrite (RQ 48), V48 by (right; right; right; right; reflexivity); reflexivity).
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). unfold s2 in C0, C1, C2, C3, C4, C5.
      rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      x64_step. rewrite RA. repeat x64_step.
      rewrite R12, RBX.
      assert (AM: (d + (n - 1) * 4) mod 2^64 = (d + 4*(n-1)) mod 2^64) by (f_equal; pure_lia).
      assert (SL: forall j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32 \/ j = 48) ->
                (s' V_MEM64 [Ⓓd + (n - 1) * 4 := 0]) Ⓠ[s0 R_RSP ⊖ j] = M3 Ⓠ[s0 R_RSP ⊖ j]).
      { intros j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
        pose proof (slot_out d _ _ j a OVd J A) as AO.
        rewrite getmem_noverlap by exact (last_byte_noverlap a d n _ AM N0 AO NB4).
        exact (FRn a AO). }
      rewrite (SL 32), V32 by (right; right; right; left; reflexivity).
      rewrite (SL 24), V24 by (right; right; left; reflexivity).
      rewrite (SL 16), V16 by (right; left; reflexivity).
      rewrite (SL 8), V8 by (left; reflexivity).
      split. exists L0. split. exact NL0. split. exact ZL0. split. reflexivity.
        split. { intros i I. rewrite (wnum_ge L0 n NL') in I.
          destruct (N.eqb_spec i (n - 1)) as [E|E].
          * subst i. rewrite ?N.eqb_refl, Bool.andb_true_r.
            destruct (N.leb_spec n L0) as [_|H]; [|exfalso; clear - NL' H; lia].
            rewrite (last_word_eq d n N0), getmem_mod_l, getmem_setmem by discriminate. reflexivity.
          * rewrite ?(proj2 (N.eqb_neq _ _) E), ?Bool.andb_false_r.
            assert (I1: i < n - 1) by (clear - I E; lia).
            rewrite getmem_noverlap by exact (last_word_noverlap d n i _ AM I1 NB4).
            rewrite CPY by exact I1. apply SW. clear - I1 NL'; lia. }
        intros b B1 B2. rewrite (wnum_ge L0 n NL') in B1.
          rewrite getmem_noverlap by exact (last_byte_noverlap b d n _ AM N0 B1 NB4).
          rewrite (FRn b B1). unfold M3. apply frameB. exact B2.
      split. apply N.mod_small. exact RB.
      destruct CS as (B3 & B4 & B5). unfold callee_saved_eq. repeat split; reg;
        first [sassumption | (rewrite ?C3, ?C4, ?C5; sassumption)].
Qed.

(* wcsncpy -- copy a fixed-size wide-character string (musl x86_64, C),
   composed with wmemset

   SEMANTICS
   ---------
   musl's wcsncpy (src/string/wcsncpy.c) is

       wchar_t *a = d;
       while (n && *s) n--, *d++ = *s++;
       wmemset(d, 0, n);
       return a;

   The binary saves RBX (= d), copies one 32-bit word per iteration and then
   CALLs wmemset (0x13c480) with the advanced d, c = 0 and the remaining n.
   wmemset's contract (wmemset_proof.v; it writes no stack) is used through
   call_leaf_ni.

   SPECIFICATION (man 3 wcsncpy, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     wchar_t *wcsncpy(wchar_t dest[restrict .n], const wchar_t src[restrict .n],
                      size_t n);
     wcsncpy copies at most n wide characters from src to dest, stopping at
     src's terminating L'\0', and fills the rest of the n wide characters of
     dest with L'\0'.  If src has no terminator within n wide characters,
     dest is not terminated.  The arrays must not overlap.  It returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcsncpy at 0x34be0, wmemset at 0x3c480 (Ghidra image base
            0x100000: 0x134be0, 0x13c480)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/wcsncpy_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, RSI = src, RDX = n; RSP = rsp; m = memory.
            Precondition (wcsncpy_ok): 4n < 2^63; the 4n bytes at d, the 4n
            bytes at src and the 16 bytes below rsp are pairwise disjoint.
            src need not be terminated within n wide characters.
   Output:  At the RET (0x134c24): RAX = d; there is K <= n such that the
            32-bit words src[0..K) are nonzero and K = n or src[K] = 0
            (K = wcsnlen(src, n)); d[i] = src[i] for i < K and d[i] = 0 for
            K <= i < n (32-bit words); every byte outside the 4n bytes at d
            and the 16 bytes below rsp is unchanged.  RSP = rsp; RBX, RBP,
            R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcsncpy_amd64 CoqEtTu.programs.wmemset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.wmemset_proof.
Open Scope N.

Definition wcsncpy_program : program := updateall2 wcsncpy_amd64 wmemset_amd64.

Theorem wcsncpy_welltyped: welltyped_prog x64typctx wcsncpy_amd64.
Proof. exact wcsncpy_amd64.welltyped. Qed.

Lemma wcsncpy_program_welltyped: welltyped_prog x64typctx wcsncpy_program.
Proof.
  intros s a. unfold wcsncpy_program, updateall2, updateall.
  destruct (wmemset_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (wmemset_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply wcsncpy_welltyped.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

(* the 4n bytes at d, the 4n bytes at s and the 16 bytes below rsp are pairwise disjoint *)
Definition wcsncpy_ok (d s n rsp:N) :=
  ~ overlap 64 d (4*n) s (4*n) /\ ~ overlap 64 d (4*n) (rsp ⊖ 16) 16 /\
  ~ overlap 64 s (4*n) (rsp ⊖ 16) 16 /\ 4*n < 2^63.

(* the source words s[0..k) are nonzero *)
Definition nzw (m s k:N) := forall i, i < k -> m Ⓓ[s ⊕ 4*i] <> 0.

(* d[0..k) holds src[0..k) (as in m); bytes outside d's 4n are as in m1 *)
Definition wcp (m m1 M d s k n:N) :=
  (forall i, i < k -> M Ⓓ[d ⊕ 4*i] = m Ⓓ[s ⊕ 4*i]) /\
  (forall b, ~ (msub 64 b d < 4*n) -> M Ⓑ[b] = m1 Ⓑ[b]).

Definition cs_but_rbx (s0 s:store) :=
  s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
  s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Lemma wcp_empty: forall m m1 d s n, wcp m m1 m1 d s 0 n.
Proof. intros. split. intros i I. lia. reflexivity. Qed.

(* a source byte lies outside d's area and outside the pushed RBX slot *)
Lemma src_byte:
  forall m M d s k n rsp v i a, wcp m (m [Ⓠrsp ⊖ 8 := v]) M d s k n -> wcsncpy_ok d s n rsp ->
  i < n -> msub 64 a (s ⊕ 4*i) < 4 -> M Ⓑ[a] = m Ⓑ[a].
Proof.
  intros m M d s k n rsp v i a [_ F] [ND [NDS [NS NB]]] I A.
  rewrite F.
  - apply getmem_noverlap. intros [x [y [X [Y E]]]]. apply NS.
    exists (4*i + msub 64 a (s ⊕ 4*i)), (8 + y). split. lia. split. lia. mlia.
  - intro H. apply ND. exists (msub 64 a d), (4*i + msub 64 a (s ⊕ 4*i)).
    split. exact H. split. lia. mlia.
Qed.

Lemma src_word:
  forall m M d s k n rsp v i, wcp m (m [Ⓠrsp ⊖ 8 := v]) M d s k n -> wcsncpy_ok d s n rsp ->
  i < n -> M Ⓓ[s ⊕ 4*i] = m Ⓓ[s ⊕ 4*i].
Proof.
  intros m M d s k n rsp v i W OK I. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply (src_byte m M d s k n rsp v i a W OK I A).
Qed.

(* one more word copied *)
Lemma wcp_store:
  forall m m1 M d s k n a v, wcp m m1 M d s k n -> k < n -> 4*n < 2^63 ->
  a mod 2^64 = (d + 4*k) mod 2^64 -> v mod 2^32 = m Ⓓ[s ⊕ 4*k] ->
  wcp m m1 (setmem 64 LittleE 4 M a v) d s (k + 1) n.
Proof.
  intros m m1 M d s k n a v [C F] K NB A V. split.
  - intros i I. destruct (N.lt_ge_cases i k) as [IK|IK].
    + rewrite getmem_noverlap. apply C, IK.
      intros [x [y [X [Y E]]]]. mlia.
    + replace i with k by lia.
      rewrite <- A, getmem_mod_l, getmem_setmem by discriminate. exact V.
  - intros b B. rewrite getmem_noverlap. apply F, B.
    intros [x [y [X [Y E]]]]. apply B. mlia.
Qed.

Lemma nzw_succ: forall m s k, nzw m s k -> m Ⓓ[s ⊕ 4*k] <> 0 -> nzw m s (k + 1).
Proof.
  intros m s k NZ B i I. destruct (N.lt_ge_cases i k). apply NZ. assumption.
  replace i with k by lia. exact B.
Qed.

Ltac cs_tac :=
  match goal with
  | CS: cs_but_rbx ?s0 _ |- cs_but_rbx ?s0 _ =>
      let B1 := fresh in let B2 := fresh in let B3 := fresh in let B4 := fresh in let B5 := fresh in
      destruct CS as (B1 & B2 & B3 & B4 & B5); unfold cs_but_rbx; repeat split;
      rewrite ?update_frame by discriminate; assumption
  | CS: callee_saved_eq ?s0 _ |- cs_but_rbx ?s0 _ =>
      let B0 := fresh in let B1 := fresh in let B2 := fresh in let B3 := fresh in let B4 := fresh in
      let B5 := fresh in
      destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold cs_but_rbx; repeat split;
      rewrite ?update_frame by discriminate; assumption
  end.

(* bytes of a quadword at rsp-j (j in {8,16}) are outside d's 4n bytes *)
Lemma stack_outside:
  forall d n rsp j a, ~ overlap 64 d (4*n) (rsp ⊖ 16) 16 -> (j = 8 \/ j = 16) ->
  msub 64 a (rsp ⊖ j) < 8 -> ~ (msub 64 a d < 4*n).
Proof.
  intros d n rsp j a NOV J A H. apply NOV. exists (msub 64 a d), (16 - j + msub 64 a (rsp ⊖ j)).
  split. exact H. split. destruct J; subst j; lia. destruct J; subst j; mlia.
Qed.

(* wmemset's frame (offsets >= 4(n-K) from d+4K) covers everything outside
   d's 4n bytes and the copied prefix *)
Lemma out_fill:
  forall b d n K, K <= n -> 4*n < 2^63 -> (~ (msub 64 b d < 4*n) \/ msub 64 b d < 4*K) ->
  4*(n-K) <= msub 64 b (d ⊕ 4*K).
Proof. intros b d n K KN NB [H|H]; mlia. Qed.

Lemma word_in_prefix:
  forall a d i K, msub 64 a (d ⊕ 4*i) < 4 -> i < K -> 4*K < 2^63 -> msub 64 a d < 4*K.
Proof. intros. mlia. Qed.

Lemma dest_word_stack:
  forall d n rsp i, ~ overlap 64 d (4*n) (rsp ⊖ 16) 16 -> i < n -> ~ overlap 64 (d ⊕ 4*i) 4 (rsp ⊖ 16) 8.
Proof.
  intros d n rsp i NOV I [x [y [X [Y E]]]]. apply NOV. exists (4*i + x), y.
  split. lia. split. lia. mlia.
Qed.

Lemma above_stack:
  forall b rsp k, 16 <= msub 64 b (rsp ⊖ 16) -> (k = 8 \/ k = 16) -> ~ overlap 64 b 1 (rsp ⊖ k) 8.
Proof. intros b rsp k B K [x [y [X [Y E]]]]. destruct K; subst k; mlia. Qed.

Lemma fill_addr4: forall d K i, K <= i -> (d ⊕ 4*K) ⊕ 4*(i - K) = d ⊕ 4*i.
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia. Qed.

Lemma slot8_16: forall a rsp, msub 64 a (rsp ⊖ 8) < 8 -> ~ overlap 64 a 1 (rsp ⊖ 16) 8.
Proof. intros a rsp A [x [y [X [Y E]]]]. mlia. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Definition wcsncpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x134c24 => true
  | _ => false end | _ => false end.

Definition wcsncpy_post (s0:store) (m d src n:N) (s:store) :=
  s R_RAX = d /\
  (exists K, K <= n /\ nzw m src K /\ (K = n \/ m Ⓓ[src ⊕ 4*K] = 0) /\
     (forall i, i < K -> s V_MEM64 Ⓓ[d ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]) /\
     (forall i, K <= i < n -> s V_MEM64 Ⓓ[d ⊕ 4*i] = 0)) /\
  (forall b, ~ (msub 64 b d < 4*n) -> 16 <= msub 64 b (s0 R_RSP ⊖ 16) -> s V_MEM64 Ⓑ[b] = m Ⓑ[b]) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wcsncpy_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x134be0 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134c0e => Some (exists k, k <= n /\ nzw m src k /\
                      wcp m (m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX]) (s V_MEM64) d src k n /\
                      s R_RDI = d ⊕ 4*k /\ s R_RSI = src ⊕ 4*k /\ s R_RDX = n - k /\
                      s R_RBX = d /\ s R_RSP = s0 R_RSP ⊖ 8 /\ cs_but_rbx s0 s)
  | 0x134c1b => Some (exists K, K <= n /\ nzw m src K /\ (K = n \/ m Ⓓ[src ⊕ 4*K] = 0) /\
                      wcp m (m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX]) (s V_MEM64) d src K n /\
                      s R_RDI = d ⊕ 4*K /\ s R_RSI = 0 /\ s R_RDX = n - K /\
                      s R_RBX = d /\ s R_RSP = s0 R_RSP ⊖ 8 /\ cs_but_rbx s0 s)
  | 0x134c24 => Some (wcsncpy_post s0 m d src n s)
  | _ => None
  end | _ => None end.

Theorem wcsncpy_correct:
  forall prog s t s' x' m d src n
         (WCSNCPY: wcsncpy_amd64 ⊆2 prog) (WMEMSET: wmemset_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x134be0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (OK: wcsncpy_ok d src n (s R_RSP)),
  satisfies_all prog (wcsncpy_invs s m d src n) wcsncpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n WCSNCPY WMEMSET ENTRY MDL MEM D S Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RDI 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcsncpy_program).
    unfold wcsncpy_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcsncpy_invs.
    unfold wcsncpy_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src n MDL MEM D S Nn OK RB RBXB DB SB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsncpy_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB DB SB. rename t1 into t.
  assert (NB: 4*n < 2^63) by (destruct OK as [_ [_ [_ NB]]]; exact NB).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP CS]]]]].
    repeat x64_step.
    pose proof (proj1 CS) as B.
    exists 0. conj_tac.
    all: first
      [ lia | (intros i I; lia)
      | (rewrite B; apply wcp_empty)
      | (rewrite N.mul_0_r, N.add_0_r, N.mod_small by assumption; first [reflexivity | assumption])
      | (rewrite N.sub_0_r; assumption)
      | cs_tac ].
  - destruct PRE as [k [KN [NZ [WC [RDI [RSI [RDX [RBX [RSP CS]]]]]]]]].
    repeat x64_step.
    + (* n = k: stop *)
      match goal with BC: (_ - _ =? 0) = true |- _ => apply N.eqb_eq in BC end.
      exists k. conj_tac.
      all: first [ (left; lia) | lia | cs_tac ].
    + (* src[k] = 0: stop *)
      match goal with BC: (_ - _ =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (getmem _ _ _ _ _ =? 0) = true |- _ =>
        apply N.eqb_eq in BC; rewrite <- getmem_mod_l in BC;
        rewrite (src_word m (s1 V_MEM64) d src k n (s0 R_RSP) (s0 R_RBX) k WC OK) in BC by lia end.
      exists k. conj_tac.
      all: first [ (right; assumption) | lia | cs_tac ].
    + (* copy one word *)
      match goal with BC: (_ - _ =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (getmem _ _ _ _ _ =? 0) = false |- _ =>
        apply N.eqb_neq in BC; rewrite <- getmem_mod_l in BC;
        rewrite (src_word m (s1 V_MEM64) d src k n (s0 R_RSP) (s0 R_RBX) k WC OK) in BC by lia end.
      exists (k + 1). conj_tac.
      all: first
        [ lia | (apply nzw_succ; assumption) | (f_equal; lia) | (unfold msub; mlia) | cs_tac
        | (apply wcp_store; [ exact WC | lia | exact NB | reflexivity |];
           rewrite N.mod_small by apply (getmem_bound 64 LittleE 4);
           rewrite <- getmem_mod_l;
           apply (src_word m (s1 V_MEM64) d src k n (s0 R_RSP) (s0 R_RBX) k WC OK); lia) ].
  - destruct PRE as [K [KN [NZ [KS [WC [RDI [RSI [RDX [RBX [RSP CS]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcsncpy_program _ _ _ _ s2 nil _ s1 t MDL1 wcsncpy_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni wcsncpy_program wmemset_amd64 _ _
              (wmemset_invs s2 (s2 V_MEM64) (d ⊕ 4*K) 0 (n - K)) wmemset_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wmemset_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wmemset_correct; first
        [ apply pf2sub_refl | assumption | reflexivity
        | (unfold s2; reg; assumption) | mlia64 ].
    + intros a s t' NC. unfold wcsncpy_invs, wcsncpy_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wmemset_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wmemset_exit _) eqn:EX; [|destruct PRE].
      unfold wmemset_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcsncpy_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX [[FZ FF] [RSP' CS']]].
      unfold s2 in *.
      rewrite update_updated in FF.
      rewrite update_frame, update_updated in RSP' by discriminate.
      pose proof OK as [ND [NDS [NS _]]].
      set (M1 := s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 16 := 1264672]) in *.
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 1264672).
      { transitivity (M1 Ⓠ[s0 R_RSP ⊖ 16]).
        - apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
          apply FF, out_fill. exact KN. exact NB. left.
          apply (stack_outside d n (s0 R_RSP) 16 a NDS). right; reflexivity. exact A.
        - unfold M1. rewrite getmem_setmem by discriminate. reflexivity. }
      assert (R8: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBX).
      { transitivity ((m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX]) Ⓠ[s0 R_RSP ⊖ 8]).
        - apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
          assert (AO: ~ (msub 64 a d < 4*n))
            by (apply (stack_outside d n (s0 R_RSP) 8 a NDS); [left; reflexivity | exact A]).
          rewrite FF by (apply out_fill; [exact KN | exact NB | left; exact AO]).
          unfold M1. rewrite getmem_noverlap by exact (slot8_16 a _ A).
          apply (proj2 WC a AO).
        - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption. }
      x64_step. rewrite RA. repeat x64_step.
      assert (RBXv: s' R_RBX = d) by (rewrite (proj1 CS'); reg; exact RBX).
      assert (CSb: cs_but_rbx s0 s') by
        (destruct CS' as (_ & B1 & B2 & B3 & B4 & B5); destruct CS as (C1 & C2 & C3 & C4 & C5);
         repeat split; [rewrite B1 | rewrite B2 | rewrite B3 | rewrite B4 | rewrite B5]; reg; assumption).
      split. exact RBXv.
      split.
      { exists K. split. exact KN. split. exact NZ. split. exact KS. split.
        - intros i I.
          transitivity (M1 Ⓓ[d ⊕ 4*i]).
          + apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
            apply FF, out_fill. exact KN. exact NB. right.
            apply (word_in_prefix a d i K A I). lia.
          + unfold M1. rewrite getmem_noverlap by (apply (dest_word_stack d n); [exact NDS | lia]).
            apply (proj1 WC i I).
        - intros i [I1 I2]. rewrite <- (fill_addr4 d K i I1). rewrite FZ by lia. reflexivity. }
      split.
      { intros b B1 B2. rewrite FF by (apply out_fill; [exact KN | exact NB | left; exact B1]).
        unfold M1. rewrite getmem_noverlap by (apply above_stack; [exact B2 | right; reflexivity]).
        rewrite (proj2 WC b B1). apply getmem_noverlap.
        apply above_stack; [exact B2 | left; reflexivity]. }
      split. apply N.mod_small. exact RB.
      destruct CSb as (C1 & C2 & C3 & C4 & C5).
      repeat split; reg; sassumption.
Qed.

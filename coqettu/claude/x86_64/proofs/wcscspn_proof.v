(* wcscspn -- length of the initial segment of a wide string not containing
   characters from a set (musl x86_64, C), composed with wcslen (two tail
   calls) and wcschr (-> wcslen)

   SEMANTICS
   ---------
   musl's wcscspn (src/string/wcscspn.c) is

       const wchar_t *a;
       if (!c[0]) return wcslen(s);
       if (!c[1]) return (s=wcschr(a=s, *c)) ? s-a : wcslen(a);
       for (a=s; *a && !wcschr(c, *a); a++);
       return a-s;

   The empty-set case and the single-character not-found case JMP to wcslen
   (0x13c380), whose RET returns to wcscspn's caller (tail_leaf,
   lib/x64_tail.v); the other cases CALL wcschr (0x13c310) (call_leaf_ni).

   SPECIFICATION (man 3 wcscspn, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     size_t wcscspn(const wchar_t *wcs, const wchar_t *reject);
     wcscspn returns the length of the longest initial segment of wcs that
     consists entirely of wide characters not in reject.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcscspn at 0x65e5a, wcschr at 0x3c310, wcslen at 0x3c380 (Ghidra
            image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcscspn_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = c (the set); RSP = rsp; m = memory.  Precondition
            (wcspn_ok): s and c are wide strings (lengths L and Lc, 4L <
            2^63) that are C objects (nonzero, no wrap) and whose words
            through the terminators do not overlap the 64 bytes below rsp.
   Output:  At a RET (0x165eb3, or wcslen's 0x13c3a1 with RSP = rsp, see
            wcscspn_exit; the tail calls use tail_leaf_g_ni and the wcschr
            calls call_leaf_g_ni, lib/x64_tail.v): RAX = K where for
            i < K the word s[i] is nonzero and does not occur in c (notin),
            and s[K] = 0 or s[K] occurs in c (inset).  Nothing outside the
            64 bytes below rsp changes; RSP = rsp; RBX, RBP, R12-R15 are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcscspn_amd64 CoqEtTu.programs.wcschr_amd64 CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.wcslen_proof CoqEtTu.proofs.wcschr_proof CoqEtTu.proofs.wcsspn_proof.
Open Scope N.

Definition wcscspn_program : program := updateall2 wcscspn_amd64 wcschr_program.

Theorem wcscspn_welltyped: welltyped_prog x64typctx wcscspn_amd64.
Proof. exact wcscspn_amd64.welltyped. Qed.

Lemma wcscspn_program_welltyped: welltyped_prog x64typctx wcscspn_program.
Proof.
  intros s a. unfold wcscspn_program, updateall2 at 1, updateall.
  destruct (wcschr_program s a) as [[sz q]|] eqn:SL.
    pose proof (wcschr_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply wcscspn_welltyped.
Qed.

Lemma wcslen_in_cspn: wcslen_amd64 ⊆2 wcscspn_program.
Proof. intros s a insn H. apply subset_updateall2. unfold wcschr_program. apply subset_updateall2, H. Qed.

Definition wcspn_ok (m s c rsp:N) :=
  (exists L, wnilfree m s L /\ m Ⓓ[s ⊕ 4*L] = 0 /\ 4*L < 2^63 /\ 0 < s /\ s + 4*L + 4 <= 2^64 /\
              ~ overlap 64 s (4*L + 4) (rsp ⊖ 64) 64) /\
  (exists Lc, wnilfree m c Lc /\ m Ⓓ[c ⊕ 4*Lc] = 0 /\ 0 < c /\ c + 4*Lc + 4 <= 2^64 /\
              ~ overlap 64 c (4*Lc + 4) (rsp ⊖ 64) 64).

Definition cspre (m:memory) (s c k:N) :=
  forall i, i < k -> m Ⓓ[s ⊕ 4*i] <> 0 /\ notin m c (m Ⓓ[s ⊕ 4*i]).

(* wcslen's RET (0x13c3a1) is wcscspn's exit only at wcscspn's own stack
   depth: the same RET is also reached inside the call to wcschr, which calls
   wcslen with RSP 64 bytes lower (wcschr_invs 0x13c3a1). *)
Definition wcscspn_exit (s0:store) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165eb3 => true
  | 0x13c3a1 => s R_RSP =? s0 R_RSP
  | _ => false end | _ => false end.

Definition wcscspn_post (s0:store) (m p c:N) (s:store) :=
  (exists K, cspre m p c K /\ (m Ⓓ[p ⊕ 4*K] = 0 \/ inset m c (m Ⓓ[p ⊕ 4*K])) /\ s R_RAX = K) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 64 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition mpush (s0:store) (m:N) :=
  m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX].

Definition wcscspn_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165e5a => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165e8f => Some (m Ⓓ[c] <> 0 /\ m Ⓓ[c ⊕ 4] = 0 /\ s V_MEM64 = mpush s0 m /\
                      s R_RDI = p /\ s R_RSI = m Ⓓ[c] /\ s R_RBP = p /\ s R_R12 = c /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165e74 => Some (exists k, m Ⓓ[c] <> 0 /\ m Ⓓ[c ⊕ 4] <> 0 /\ cspre m p c k /\ frm64 s0 m (s V_MEM64) /\
                      s R_RBX = p ⊕ 4*k /\ s R_RBP = p /\ s R_R12 = c /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165e7d => Some (exists k, m Ⓓ[c] <> 0 /\ m Ⓓ[c ⊕ 4] <> 0 /\ cspre m p c k /\
                      m Ⓓ[p ⊕ 4*k] <> 0 /\ s R_RSI mod 2^32 = m Ⓓ[p ⊕ 4*k] /\
                      s R_RDI = c /\ frm64 s0 m (s V_MEM64) /\
                      s R_RBX = p ⊕ 4*k /\ s R_RBP = p /\ s R_R12 = c /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165eb3 => Some (wcscspn_post s0 m p c s)
  | 0x13c3a1 => if s R_RSP =? s0 R_RSP then Some (wcscspn_post s0 m p c s) else None
  | _ => None
  end | _ => None end.

Definition wcscspn_invs0 (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165e5a => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165e8f => Some (m Ⓓ[c] <> 0 /\ m Ⓓ[c ⊕ 4] = 0 /\ s V_MEM64 = mpush s0 m /\
                      s R_RDI = p /\ s R_RSI = m Ⓓ[c] /\ s R_RBP = p /\ s R_R12 = c /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165e74 => Some (exists k, m Ⓓ[c] <> 0 /\ m Ⓓ[c ⊕ 4] <> 0 /\ cspre m p c k /\ frm64 s0 m (s V_MEM64) /\
                      s R_RBX = p ⊕ 4*k /\ s R_RBP = p /\ s R_R12 = c /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165e7d => Some (exists k, m Ⓓ[c] <> 0 /\ m Ⓓ[c ⊕ 4] <> 0 /\ cspre m p c k /\
                      m Ⓓ[p ⊕ 4*k] <> 0 /\ s R_RSI mod 2^32 = m Ⓓ[p ⊕ 4*k] /\
                      s R_RDI = c /\ frm64 s0 m (s V_MEM64) /\
                      s R_RBX = p ⊕ 4*k /\ s R_RBP = p /\ s R_R12 = c /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165eb3 => Some (wcscspn_post s0 m p c s)
  | _ => None
  end | _ => None end.

Definition wcscspn_exit0 (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165eb3 | 0x13c3a1 => true
  | _ => false end | _ => false end.

(* At 0x13c3a1 the precondition is None either way (exit, or no invariant),
   so the store-dependent exit can be replaced by a static one for the
   case split (destruct_inv cannot decide RSP =? s0 RSP). *)
Lemma wcscspn_pre_static:
  forall (P:program) s0 m p c a s t,
  true_inv (get_precondition P (wcscspn_invs s0 m p c) (wcscspn_exit s0) a s t) ->
  true_inv (get_precondition P (wcscspn_invs0 s0 m p c) wcscspn_exit0 a s t).
Proof.
  intros P s0 m p c a s t. unfold get_precondition.
  destruct (N.eq_dec a 0x13c3a1) as [E|NE].
  - subst a. cbv beta iota delta [wcscspn_exit wcscspn_invs].
    destruct (s R_RSP =? s0 R_RSP); [intro H; exact H|].
    destruct (P s 0x13c3a1); intro H; exact H.
  - assert (EX: wcscspn_exit s0 ((Addr a,s)::t) = wcscspn_exit0 ((Addr a,s)::t)).
    { unfold wcscspn_exit, wcscspn_exit0.
      repeat first [ reflexivity | (exfalso; apply NE; reflexivity)
                   | match goal with |- context [match ?n with _ => _ end] =>
                       lazymatch n with (_ =? _) => fail | _ => destruct n end end ]. }
    assert (IV: wcscspn_invs s0 m p c ((Addr a,s)::t) = wcscspn_invs0 s0 m p c ((Addr a,s)::t)).
    { unfold wcscspn_invs, wcscspn_invs0.
      repeat first [ reflexivity | (exfalso; apply NE; reflexivity)
                   | match goal with |- context [match ?n with _ => _ end] =>
                       lazymatch n with (_ =? _) => fail | _ => destruct n end end ]. }
    rewrite EX, IV. exact (fun H => H).
Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Lemma cspre_len: forall m s c k L, cspre m s c k -> m Ⓓ[s ⊕ 4*L] = 0 -> k <= L.
Proof.
  intros m s c k L SP Z. destruct (N.le_gt_cases k L) as [H|H]. exact H.
  exfalso. exact (proj1 (SP L H) Z).
Qed.

Lemma cspre_succ: forall m s c k, cspre m s c k -> m Ⓓ[s ⊕ 4*k] <> 0 -> notin m c (m Ⓓ[s ⊕ 4*k]) ->
  cspre m s c (k + 1).
Proof.
  intros m s c k SP A B i I. destruct (N.lt_ge_cases i k). apply SP. assumption.
  replace i with k by lia. split; assumption.
Qed.

(* with an empty set nothing is in it *)
Lemma notin_empty: forall m c w, m Ⓓ[c] = 0 -> c < 2^64 -> notin m c w.
Proof.
  intros m c w Z CB. exists 0. split. intros i I. lia.
  rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact CB. exact Z.
Qed.

(* the set [c0]: membership is equality with c0 *)
Lemma notin_one: forall m c w, m Ⓓ[c] <> 0 -> m Ⓓ[c ⊕ 4] = 0 -> m Ⓓ[c] <> w -> c < 2^64 -> notin m c w.
Proof.
  intros m c w C0 C1 NE CB. exists 1. split.
  - intros i I. replace i with 0 by lia. rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact CB. split; assumption.
  - exact C1.
Qed.

Lemma inset_one: forall m c, c < 2^64 -> inset m c (m Ⓓ[c]).
Proof.
  intros m c CB. exists 0. split. intros i I. lia.
  rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact CB. reflexivity.
Qed.

Lemma wnilfree_unique':
  forall m p k L, wnilfree m p k -> m Ⓓ[p ⊕ 4*k] = 0 -> wnilfree m p L -> m Ⓓ[p ⊕ 4*L] = 0 -> k = L.
Proof.
  intros m p k L NK ZK NL ZL. destruct (N.lt_trichotomy k L) as [H|[H|H]].
  - exfalso. apply (NL k H ZK).
  - exact H.
  - exfalso. apply (NK L H ZL).
Qed.

Lemma w1: forall (M:memory) x, M Ⓓ[x ⊕ 4*1] = M Ⓓ[4 + x].
Proof. intros. rewrite getmem_mod_l. f_equal. lia. Qed.

Lemma w1': forall (M:memory) x, M Ⓓ[x ⊕ 4] = M Ⓓ[4 + x].
Proof. intros. rewrite getmem_mod_l. f_equal. lia. Qed.

Lemma rsp_ne64: forall x, x < 2^64 -> (x ⊖ 32 ⊖ 32 =? x) = false.
Proof.
  intros x X. apply N.eqb_neq. unfold msub. change (2^64) with 18446744073709551616 in *.
  rewrite N.add_mod_idemp_l by discriminate. intro E.
  rewrite <- N.add_assoc in E. rewrite <- (N.mod_small x 18446744073709551616) in E at 2 by exact X.
  apply (f_equal (fun y => (y + 64) mod 18446744073709551616)) in E.
  rewrite N.add_mod_idemp_l in E by discriminate.
  rewrite N.add_mod_idemp_l in E by discriminate.
  rewrite <- N.add_assoc in E. rewrite N.add_mod in E by discriminate.
  rewrite (N.mod_small x) in E by exact X.
  replace ((18446744073709551584 + 18446744073709551584 + 64) mod 18446744073709551616) with 0 in E by reflexivity.
  rewrite N.add_0_r, N.mod_small in E by exact X. revert E. clear. lia.
Qed.

Lemma mpush_frm64: forall s0 m, s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 -> frm64 s0 m (mpush s0 m).
Proof. intros. unfold mpush. apply frm64_init; assumption. Qed.

Theorem wcscspn_correct:
  forall prog s t s' x' m p c
         (WCSCSPN: wcscspn_amd64 ⊆2 prog) (WCSCHR: wcschr_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165e5a, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (OK: wcspn_ok m p c (s R_RSP)),
  satisfies_all prog (wcscspn_invs s m p c) (wcscspn_exit s) ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c WCSCSPN WCSCHR WCSLEN ENTRY MDL MEM P C OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  assert (CB: c < 2^64) by (rewrite <- C; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcscspn_program).
    unfold wcscspn_program, wcschr_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcscspn_invs.
    unfold wcscspn_program, wcschr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C OK RB RBXB RBPB R12B PB CB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscspn_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B PB CB. rename t1 into t.
  destruct OK as [(L & NL & ZL & LB & P0 & PW & OVs) (Lc & NLc & ZLc & C0 & CW & OVc)].
  apply wcscspn_pre_static in PRE.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [C [RSP CS]]]].
    x64_step. x64_step. x64_step.
    + (* c[0] = 0: tail call wcslen(s) *)
      match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into CZ end.
      x64_step.
      match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
      apply (models_after_steps wcscspn_program _ _ _ _ s2 tm _ s1 t MDL1 wcscspn_program_welltyped).
      intro MDL2.
      assert (S2M: s2 V_MEM64 = m) by (unfold s2; reg; first [exact MEM | reflexivity]).
      assert (S2R: s2 R_RSP = s0 R_RSP) by (unfold s2; reg; first [exact RSP | reflexivity]).
      assert (C02: callee_saved_eq s0 s2) by
        (destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold s2; repeat split; reg; assumption).
      eapply (tail_leaf_g_ni wcscspn_program wcslen_amd64 _ _ (wcslen_invs s2 (s2 V_MEM64) p) wcslen_exit).
      * apply wcslen_in_cspn.
      * intros a s t' EXIT NOCODE. unfold wcslen_invs.
        repeat first
        [ reflexivity | discriminate EXIT | discriminate NOCODE
        | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
      * intros t' [x' s'] START. apply wcslen_correct; first
          [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
      * intros a s t' NC X2 _. unfold wcscspn_invs, wcscspn_exit, wcslen_exit in *.
        repeat first
        [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
        | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
      * intros a s t' X2. unfold wcslen_exit in X2. addr_cases X2.
        cbv beta iota delta [post_or_true true_inv wcslen_invs wcscspn_invs wcslen_post].
        intros [[k [NF [Z RAX]]] [PM [PR PC]]].
        rewrite PR, S2R, N.eqb_refl. cbv beta iota.
        rewrite S2M in NF, Z, PM.
        assert (KL: k = L) by exact (wnilfree_unique' m p k L NF Z NL ZL). subst k.
        split. exists L. split.
          intros i I. split. apply NL, I. apply notin_empty; assumption.
          split. left. exact ZL. rewrite RAX. apply wcslen_ret. exact LB.
        split. rewrite PM. apply stack_frame_refl.
        split. rewrite PR. exact S2R. exact (callee_saved_eq_trans _ _ _ C02 PC).
      * intros [[a|i] s] t'; reflexivity.
      * intros [[a|i] s] t'; reflexivity.
      * intros a s t' X. unfold wcslen_exit in X. addr_cases X; discriminate.
      * split; reflexivity.
      * intros. split; reflexivity.
    + match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into CNZ end.
      pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5).
      assert (LC1: 1 <= Lc).
      { destruct (N.eq_dec Lc 0) as [E|E]; [|clear - E; lia]. exfalso. apply CNZ. subst Lc.
        rewrite N.mul_0_r, N.add_0_r, N.mod_small in ZLc by exact CB. exact ZLc. }
      pose proof (mpush_frm64 s0 m R12B RBPB RBXB) as FR0.
      assert (C1EQ: mpush s0 m Ⓓ[4 + c] = m Ⓓ[4 + c])
        by (rewrite <- !w1; exact (frm64_word s0 m _ c Lc 1 FR0 OVc LC1)).
      repeat x64_step.
      all: rewrite ?B0, ?B1, ?B2 in *; fold (mpush s0 m) in *; rewrite ?C1EQ in *; rewrite ?w1' in *.
      * match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC end.
        conj_tac. unfold cs3. repeat split; reg; assumption.
      * match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC end.
        exists 0. split. exact CNZ. split. assumption. split. intros i I. exfalso. exact (N.nlt_0_r i I).
        split. exact FR0. split. rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact PB. reflexivity.
        conj_tac. unfold cs3. repeat split; reg; assumption.
  - destruct PRE as [k [CNZ [C1NZ [SP [FR [RBX [RBP [R12 [RSP CS]]]]]]]]].
    rewrite w1' in C1NZ.
    assert (KL: k <= L) by exact (cspre_len m p c k L SP ZL).
    assert (BW: s1 V_MEM64 Ⓓ[p + 4*k] = m Ⓓ[p ⊕ 4*k])
      by (rewrite <- getmem_mod_l; exact (frm64_word s0 m _ p L k FR OVs KL)).
    pose proof FR as [_ [T8 [T16 T24]]].
    repeat x64_step.
    all: rewrite ?BW in *.
    + match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC end.
      rewrite msub_off by exact PB. change (2 .& 63) with 2. rewrite (wcslen_ret k ltac:(clear - KL LB; lia)).
      rewrite T8, T16, T24.
      split. exists k. split. exact SP. split. left. assumption. reflexivity.
      split. exact (frm64_frame _ _ _ FR).
      split. apply N.mod_small. exact RB.
      destruct CS as (B3 & B4 & B5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC end.
      exists k. conj_tac. destruct CS as (B3 & B4 & B5). unfold cs3. repeat split; reg; assumption.
  - destruct PRE as [k [CNZ [C1NZ [SP [NZ [RSI [RDI [FR [RBX [RBP [R12 [RSP CS]]]]]]]]]]]].
    rewrite w1' in C1NZ.
    assert (KL: k <= L) by exact (cspre_len m p c k L SP ZL).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcscspn_program _ _ _ _ s2 nil _ s1 t MDL1 wcscspn_program_welltyped).
    intro MDL2.
    pose proof (frm64_ra _ _ _ 0x165e82 FR) as FR2.
    assert (CBw: forall i, i <= Lc -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x165e82]) Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i])
      by (intros i I; exact (frm64_word s0 m _ c Lc i FR2 OVc I)).
    eapply (call_leaf_g_ni wcscspn_program wcschr_program _ _ (wcschr_invs s2 (s2 V_MEM64) c (s2 R_RSI)) wcschr_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcschr_invs.
      unfold wcschr_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcschr_correct; first
        [ apply wcschr_in_prog | apply subset_updateall2 | assumption | reflexivity
        | (unfold s2; reg; assumption) | idtac ].
      intro H. exfalso. apply NZ. unfold s2 in H. rewrite !update_frame in H by discriminate.
      rewrite <- RSI. exact H.
    + intros a s t' NC X2 H. unfold wcscspn_invs, wcscspn_exit.
      unfold wcschr_program, updateall2, updateall in NC. unfold wcschr_exit in X2.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
      | match goal with |- context [match ?n with _ => _ end] =>
          lazymatch n with (_ =? _) => fail | _ => destruct n end end
      | (cbv beta iota delta [post_or_true wcschr_invs] in H;
         destruct H as (kk & _ & _ & _ & _ & RSPx & _);
         rewrite RSPx; unfold s2; reg; rewrite rsp_ne64 by exact RB; reflexivity) ].
    + intros a s t' X2 _. unfold wcschr_exit in X2. addr_cases X2.
      all: cbv beta iota delta [inv_or_noexit wcscspn_invs wcscspn_exit]; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcschr_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wcschr_exit _) eqn:EX; [|destruct PRE].
      unfold wcschr_exit in EX. addr_cases EX.
      all: simpl in PRE.
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcscspn_program_welltyped).
      all: intro MDL3.
      all: destruct PRE as [[kk [CF RES]] [SF [RSP' CS']]].
      all: unfold s2 in CF, RES, SF, RSP', CS'.
      all: rewrite ?update_updated in CF, RES, SF.
      all: rewrite !update_frame in RSP' by discriminate.
      all: rewrite update_updated in RSP'.
      all: rewrite ?update_frame in CF, RES by discriminate.
      all: rewrite ?RSI in CF, RES.
      all: assert (KK: kk <= Lc) by (apply (wcfree_len _ c (m Ⓓ[p ⊕ 4*k]) kk Lc CF); rewrite CBw by (clear; lia); exact ZLc).
      all: assert (CFm: wcfree m c (m Ⓓ[p ⊕ 4*k]) kk)
             by (intros i I; rewrite <- (CBw i) by (clear - I KK; lia); apply CF, I).
      all: rewrite (CBw kk KK) in RES.
      all: pose proof (frm64_after _ _ _ _ FR2 SF) as FR3.
      all: pose proof (ra_after _ _ _ _ SF ltac:(rewrite getmem_setmem by discriminate; reflexivity)) as RA.
      all: destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
      all: rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
      all: assert (CK: c ⊕ 4*kk = c + 4*kk) by (apply N.mod_small; clear - KK CW; lia).
      all: destruct RES as [[HK RAXv]|[HK [_ RAXv]]]; [rewrite CK in RAXv|].
      all: x64_step; rewrite RA; repeat x64_step.
      all: try (match goal with BC: (_ + _ =? 0) = true |- _ =>
                  apply N.eqb_eq in BC; exfalso; clear - BC C0; lia end).
      all: pose proof FR3 as [_ [T8 [T16 T24]]].
      all: try (rewrite T8, T16, T24).
      all: try (rewrite ?D0, ?D1, RBX, RBP, msub_off by exact PB; change (2 .& 63) with 2;
                rewrite (wcslen_ret k ltac:(clear - KL LB; lia))).
      all: first
        [ (split; [exists k; split; [exact SP | split; [right; exists kk; split; [exact CFm | exact HK] | reflexivity]] |];
           split; [exact (frm64_frame _ _ _ FR3) |]; split; [apply N.mod_small; exact RB |];
           destruct CS as (B3 & B4 & B5); unfold callee_saved_eq; repeat split; reg;
           first [sassumption | (rewrite ?D3, ?D4, ?D5; sassumption)])
        | (exists (k + 1); split; [exact CNZ |]; split; [exact C1NZ |];
           split; [apply cspre_succ; [exact SP | exact NZ | exists kk; split; [exact CFm | exact HK]] |];
           split; [exact FR3 |];
           split; [rewrite RBX, N.add_mod_idemp_r by discriminate; f_equal; pure_lia |];
           split; [rewrite D1; reg; exact RBP |]; split; [rewrite D2; reg; exact R12 |];
           split; [reflexivity |];
           destruct CS as (B3 & B4 & B5); unfold cs3; repeat split; reg; rewrite ?D3, ?D4, ?D5; assumption)
        | idtac ].
  - (* the single-character set: wcschr(s, c0) *)
    destruct PRE as [C0NZ [C1Z [MEM [RDI [RSI [RBP [R12 [RSP CS]]]]]]]].
    pose proof (mpush_frm64 s0 m R12B RBPB RBXB) as FR.
    rewrite <- MEM in FR. clear MEM.
    assert (C0B: m Ⓓ[c] < 2^32) by apply (getmem_bound 64 LittleE 4 m c).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcscspn_program _ _ _ _ s2 nil _ s1 t MDL1 wcscspn_program_welltyped).
    intro MDL2.
    pose proof (frm64_ra _ _ _ 0x165e94 FR) as FR2.
    assert (SBw: forall i, i <= L -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x165e94]) Ⓓ[p ⊕ 4*i] = m Ⓓ[p ⊕ 4*i])
      by (intros i I; exact (frm64_word s0 m _ p L i FR2 OVs I)).
    eapply (call_leaf_g_ni wcscspn_program wcschr_program _ _ (wcschr_invs s2 (s2 V_MEM64) p (s2 R_RSI)) wcschr_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcschr_invs.
      unfold wcschr_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcschr_correct; first
        [ apply wcschr_in_prog | apply subset_updateall2 | assumption | reflexivity
        | (unfold s2; reg; assumption) | idtac ].
      intro H. exfalso. apply C0NZ. unfold s2 in H. rewrite !update_frame in H by discriminate.
      rewrite RSI, N.mod_small in H by exact C0B. exact H.
    + intros a s t' NC X2 H. unfold wcscspn_invs, wcscspn_exit.
      unfold wcschr_program, updateall2, updateall in NC. unfold wcschr_exit in X2.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
      | match goal with |- context [match ?n with _ => _ end] =>
          lazymatch n with (_ =? _) => fail | _ => destruct n end end
      | (cbv beta iota delta [post_or_true wcschr_invs] in H;
         destruct H as (kk & _ & _ & _ & _ & RSPx & _);
         rewrite RSPx; unfold s2; reg; rewrite rsp_ne64 by exact RB; reflexivity) ].
    + intros a s t' X2 _. unfold wcschr_exit in X2. addr_cases X2.
      all: cbv beta iota delta [inv_or_noexit wcscspn_invs wcscspn_exit]; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcschr_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wcschr_exit _) eqn:EX; [|destruct PRE].
      unfold wcschr_exit in EX. addr_cases EX.
      all: simpl in PRE.
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcscspn_program_welltyped).
      all: intro MDL3.
      all: destruct PRE as [[kk [CF RES]] [SF [RSP' CS']]].
      all: unfold s2 in CF, RES, SF, RSP', CS'.
      all: rewrite ?update_updated in CF, RES, SF.
      all: rewrite !update_frame in RSP' by discriminate.
      all: rewrite update_updated in RSP'.
      all: rewrite ?update_frame in CF, RES by discriminate.
      all: rewrite ?RSI in CF, RES.
      all: rewrite ?(N.mod_small (m Ⓓ[c])) in CF, RES by exact C0B.
      all: assert (KK: kk <= L) by (apply (wcfree_len _ p (m Ⓓ[c]) kk L CF); rewrite SBw by (clear; lia); exact ZL).
      all: assert (CFm: wcfree m p (m Ⓓ[c]) kk)
             by (intros i I; rewrite <- (SBw i) by (clear - I KK; lia); apply CF, I).
      all: rewrite (SBw kk KK) in RES.
      all: pose proof (frm64_after _ _ _ _ FR2 SF) as FR3.
      all: pose proof (ra_after _ _ _ _ SF ltac:(rewrite getmem_setmem by discriminate; reflexivity)) as RA.
      all: destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
      all: rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
      all: assert (PK: p ⊕ 4*kk = p + 4*kk) by (apply N.mod_small; clear - KK PW; lia).
      all: pose proof FR3 as [_ [T8 [T16 T24]]].
      all: destruct RES as [[HK RAXv]|[HK [_ RAXv]]]; [rewrite PK in RAXv|].
      all: x64_step; rewrite RA; x64_step; x64_step.
      all: try (match goal with BC: (_ + _ =? 0) = true |- _ =>
                  apply N.eqb_eq in BC; exfalso; clear - BC P0; lia end).
      all: lazymatch goal with
           | |- nextinv _ _ _ _ ((Addr 0x165ea8, _)::_) =>
               repeat x64_step; rewrite ?T8, ?T16, ?T24;
               rewrite RBP, <- PK, msub_off by exact PB; change (2 .& 63) with 2;
               rewrite (wcslen_ret kk ltac:(clear - KK LB; lia));
               split; [exists kk; split;
                 [ intros i I; destruct (CFm i I) as [A B]; split;
                   [ exact A | apply notin_one; [exact C0NZ | exact C1Z | intro E; exact (B (eq_sym E)) | exact CB]]
                 | split; [right; rewrite HK; apply inset_one, CB | reflexivity]] |];
               split; [exact (frm64_frame _ _ _ FR3) |];
               split; [apply N.mod_small; exact RB |];
               destruct CS as (B3 & B4 & B5); unfold callee_saved_eq; repeat split; reg;
               first [reflexivity | (rewrite ?D3, ?D4, ?D5; sassumption)]
           | |- nextinv _ _ _ _ ((Addr 0x165e99, _)::_) =>
               do 5 x64_step;
               idtac
           end.
      all: match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T0 ++ (Addr _, ?S')::?T2) => set (s3 := S);
             apply (models_after_steps _ _ _ _ _ s3 T0 _ S' T2 MDL3 wcscspn_program_welltyped) end.
      all: intro MDL4.
      all: assert (KKL: kk = L) by (destruct (N.lt_ge_cases kk L) as [H|H];
                                    [exfalso; exact (NL kk H HK) | clear - H KK; lia]).
      all: subst kk.
      all: assert (S3R: s3 R_RSP = s0 R_RSP) by (unfold s3; reg; apply N.mod_small, RB).
      all: assert (S3M: s3 V_MEM64 = s' V_MEM64) by (unfold s3; reg; reflexivity).
      all: assert (C03: callee_saved_eq s0 s3) by
             (destruct CS as (B3 & B4 & B5); unfold s3, callee_saved_eq; repeat split; reg;
              first [ sassumption | (rewrite ?D3, ?D4, ?D5; sassumption) ]).
      all: eapply (tail_leaf_g_ni wcscspn_program wcslen_amd64 _ _ (wcslen_invs s3 (s3 V_MEM64) p) wcslen_exit);
           [ apply wcslen_in_cspn
           | intros a s t' EXIT NOCODE; unfold wcslen_invs;
             repeat first
             [ reflexivity | discriminate EXIT | discriminate NOCODE
             | match goal with |- context [match ?n with _ => _ end] => destruct n end ]
           | intros t' [x' s''] START; apply wcslen_correct; first
               [ apply pf2sub_refl | assumption | reflexivity | (unfold s3; reg; exact RBP) ]
           | intros a s t' NC X2 _; unfold wcscspn_invs, wcscspn_exit, wcslen_exit in *;
             repeat first
             [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
             | match goal with |- context [match ?n with _ => _ end] => destruct n end ]
           | intros a s t' X2; unfold wcslen_exit in X2; addr_cases X2;
             cbv beta iota delta [post_or_true true_inv wcslen_invs wcscspn_invs wcslen_post];
             intros [[k [NFk [Zk RAXk]]] [PM [PR PC]]];
             rewrite PR, S3R, N.eqb_refl; cbv beta iota;
             rewrite S3M in NFk, Zk, PM;
             assert (KL: k <= L) by (destruct (N.le_gt_cases k L) as [H|H]; [exact H|];
               exfalso; apply (NFk L H); rewrite (frm64_word s0 m _ p L L FR3 OVs (N.le_refl L)); exact ZL);
             assert (Zm: m Ⓓ[p ⊕ 4*k] = 0) by (rewrite <- (frm64_word s0 m _ p L k FR3 OVs KL); exact Zk);
             assert (KE: k = L) by (destruct (N.lt_ge_cases k L) as [H|H];
                                    [exfalso; exact (NL k H Zm) | clear - H KL; lia]);
             subst k;
             split; [exists L; split;
               [ intros i I; split;
                 [ apply NL, I
                 | apply notin_one; [exact C0NZ | exact C1Z | intro E; exact (proj2 (CFm i I) (eq_sym E)) | exact CB]]
               | split; [left; exact ZL | rewrite RAXk; apply wcslen_ret; exact LB]] |];
             split; [rewrite PM; exact (frm64_frame _ _ _ FR3) |];
             split; [rewrite PR; exact S3R |];
             exact (callee_saved_eq_trans _ _ _ C03 PC)
           | intros [[a|i] s] t'; reflexivity
           | intros [[a|i] s] t'; reflexivity
           | intros a s t' X; unfold wcslen_exit in X; addr_cases X; discriminate
           | split; reflexivity
           | intros; split; reflexivity ].
Qed.

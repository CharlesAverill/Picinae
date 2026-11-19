(* wcschr -- locate a wide character in a wide string (musl x86_64, C),
   composed with wcslen

   SEMANTICS
   ---------
   musl's wcschr (src/string/wcschr.c) is

       if (!c) return (wchar_t * )s + wcslen(s);
       for (; *s && *s != c; s++);
       return *s ? (wchar_t * )s : 0;

   For c = 0 the binary spills s to its stack frame and CALLs wcslen
   (0x13c380); wcslen's contract (wcslen_proof.v) is used through
   call_leaf_ni.  wcslen returns (4k mod 2^64) >>> 2, which is the element
   count k only when 4k < 2^63, so the c = 0 precondition includes that
   bound (any wide string in a C object satisfies it).

   SPECIFICATION (man 3 wcschr, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <wchar.h>
            wchar_t *wcschr(const wchar_t *wcs, wchar_t wc);

     DESCRIPTION
            The wcschr() function is the wide-character equivalent of the
            strchr(3) function.  It searches the first occurrence of wc in
            the wide-character string pointed to by wcs.

     RETURN VALUE
            The wcschr() function returns a pointer to the first occurrence
            of wc in the wide-character string pointed to by wcs, or NULL if
            wc does not occur in the string.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcschr at 0x3c310, wcslen at 0x3c380 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcschr_amd64.v, wcslen_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, ESI = wc (c32 = RSI mod 2^32); RSP = rsp; m = memory.
            Precondition (wstack_ok), only when c32 = 0: s has length L with
            4L < 2^63, and its 4L+4 bytes do not overlap the 32 bytes below
            rsp (wcschr's frame and the CALL's return address).
   Output:  At any RET: for some k, the words s[0..k) are neither 0 nor c32
            and either s[k] = c32 and RAX = s + 4k (mod 2^64), or s[k] = 0,
            c32 <> 0 and RAX = 0 (NULL).  No byte outside the 32 bytes below
            rsp has changed; RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcschr_amd64 CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.wcslen_proof.
Open Scope N.

Definition wcschr_program : program := updateall2 wcschr_amd64 wcslen_amd64.

Theorem wcschr_welltyped: welltyped_prog x64typctx wcschr_amd64.
Proof. exact wcschr_amd64.welltyped. Qed.

Lemma wcschr_program_welltyped: welltyped_prog x64typctx wcschr_program.
Proof.
  intros s a. unfold wcschr_program, updateall2, updateall.
  destruct (wcslen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (wcslen_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply wcschr_welltyped.
Qed.

(* the words s[0..k) are neither 0 nor c *)
Definition wcfree (m:memory) (p c k:N) := forall i, i < k -> m Ⓓ[p ⊕ 4*i] <> 0 /\ m Ⓓ[p ⊕ 4*i] <> c.

Definition wstack_ok (m p c rsp:N) :=
  c mod 2^32 = 0 -> exists L, wnilfree m p L /\ m Ⓓ[p ⊕ 4*L] = 0 /\ 4*L < 2^63 /\
                             ~ overlap 64 p (4*L + 4) (rsp ⊖ 32) 32.

Definition wcschr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13c32f | 0x13c341 | 0x13c344 => true
  | _ => false end | _ => false end.

Definition wcschr_post (s0:store) (m p c:N) (s:store) :=
  (exists k, wcfree m p (c mod 2^32) k /\
     ((m Ⓓ[p ⊕ 4*k] = c mod 2^32 /\ s R_RAX = p ⊕ 4*k) \/
      (m Ⓓ[p ⊕ 4*k] = 0 /\ c mod 2^32 <> 0 /\ s R_RAX = 0))) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 32 /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

(* memory at the call to wcslen: s saved at rsp-16, return address pushed *)
Definition wcschr_cmem (s0:store) (m p:N) := m [Ⓠs0 R_RSP ⊖ 16 := p] [Ⓠs0 R_RSP ⊖ 32 := 0x13c322].

(* 0x13c3a1 is wcslen's RET: the invariant there (wcslen's postcondition in
   wcschr's frame) lets a caller of wcschr that also tail-calls wcslen (e.g.
   wcscspn) tell this return apart from its own exit by RSP. *)
Definition wcschr_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13c310 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ wstack_ok m p c (s0 R_RSP))
  | 0x13c31d => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 16 := p] /\ s R_RDI = p /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ c mod 2^32 = 0 /\ callee_saved_eq s0 s /\
                      wstack_ok m p c (s0 R_RSP) /\ s0 R_RSP < 2^64)
  | 0x13c334 => Some (exists k, s R_RDI = p ⊕ 4*k /\ wcfree m p (c mod 2^32) k /\ s R_RSI = c /\
                      c mod 2^32 <> 0 /\ s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c3a1 => Some (exists k, wnilfree (wcschr_cmem s0 m p) p k /\ wcschr_cmem s0 m p Ⓓ[p ⊕ 4*k] = 0 /\
                      s R_RAX = (4 ⊗ k) >>> 2 /\ s V_MEM64 = wcschr_cmem s0 m p /\
                      s R_RSP = s0 R_RSP ⊖ 32 /\ callee_saved_eq s0 s /\ c mod 2^32 = 0 /\
                      wstack_ok m p c (s0 R_RSP) /\ s0 R_RSP < 2^64)
  | 0x13c32f | 0x13c341 | 0x13c344 => Some (wcschr_post s0 m p c s)
  | _ => None
  end | _ => None end.

Lemma wnilfree_unique:
  forall m p k L, wnilfree m p k -> m Ⓓ[p ⊕ 4*k] = 0 -> wnilfree m p L -> m Ⓓ[p ⊕ 4*L] = 0 -> k = L.
Proof.
  intros m p k L NK ZK NL ZL. destruct (N.lt_trichotomy k L) as [H|[H|H]].
  - exfalso. apply (NL k H ZK).
  - exact H.
  - exfalso. apply (NK L H ZL).
Qed.

(* The two stack writes before the call leave the string's words alone. *)
Lemma frame_words:
  forall m p L rsp v1 v2 i, ~ overlap 64 p (4*L + 4) (rsp ⊖ 32) 32 -> i <= L ->
  (m [Ⓠrsp ⊖ 16 := v1] [Ⓠrsp ⊖ 32 := v2]) Ⓓ[p ⊕ 4*i] = m Ⓓ[p ⊕ 4*i].
Proof.
  intros m p L rsp v1 v2 i NOV I.
  rewrite getmem_noverlap. rewrite getmem_noverlap. reflexivity.
  - intros [x [y [X [Y E]]]]. apply NOV. exists (4*i + x), (16 + y). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
  - intros [x [y [X [Y E]]]]. apply NOV. exists (4*i + x), y. split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma dword_load_off: forall (m:memory) p k, m Ⓓ[p ⊕ k] = m Ⓓ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Ltac frame_tac :=
  lazymatch goal with |- stack_frame _ _ _ _ =>
    repeat (apply stack_frame_store; [lia | reflexivity |]);
    first [ apply stack_frame_refl
          | match goal with H: _ V_MEM64 = _ |- _ => rewrite H; apply stack_frame_refl end ]
  end.
Ltac fin := conj_tac; try frame_tac.

Theorem wcschr_correct:
  forall prog s t s' x' m p c
         (WCSCHR: wcschr_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13c310, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (STK: wstack_ok m p c (s R_RSP)),
  satisfies_all prog (wcschr_invs s m p c) wcschr_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c WCSCHR WCSLEN ENTRY MDL MEM P C STK.
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcschr_program).
    unfold wcschr_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcschr_invs.
    unfold wcschr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C PB STK START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcschr_program_welltyped. intro MDL1.
  clear - PRE MDL1 PB. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [P [C [RSP [CS STK]]]]].
    assert (RB: s0 R_RSP < 2^64) by (rewrite <- RSP; apply (MDL1 R_RSP 64); reflexivity).
    repeat x64_step. all: bc_norm.
    + conj_tac.
    + exists 0. split. rewrite N.mul_0_r, N.add_0_r, N.mod_small by assumption. assumption.
      split. intros i I. lia. conj_tac.
  - (* the call to wcslen *)
    destruct PRE as [MEM [RDI [RSP [C0 [CS [STK RB]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcschr_program _ _ _ _ s2 nil _ s1 t MDL1 wcschr_program_welltyped).
    intro MDL2.
    eapply (tail_leaf_g_ni wcschr_program wcslen_amd64 _ _ (wcslen_invs s2 (s2 V_MEM64) p) wcslen_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcslen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcslen_correct; first
        [ assumption | apply pf2sub_refl | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; exact RDI) ].
    + intros a s t' NC X2 _. unfold wcschr_invs, wcschr_exit, wcslen_exit in *.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros a s t' X2 H. unfold wcslen_exit in X2. addr_cases X2.
      cbv beta iota delta [post_or_true true_inv wcslen_invs wcschr_invs] in H |- *.
      destruct H as [[k [NF [Z RAX]]] [MEM' [RSP' CS']]].
      assert (S2M: s2 V_MEM64 = wcschr_cmem s0 m p).
      { unfold s2, wcschr_cmem. rewrite update_updated. sreflexivity. }
      rewrite S2M in NF, Z, MEM'.
      exists k. split. exact NF. split. exact Z. split. exact RAX. split. exact MEM'.
      split. rewrite RSP'. unfold s2. rewrite !update_frame by discriminate. rewrite update_updated. reflexivity.
      split. eapply callee_saved_eq_trans. exact CS. eapply callee_saved_eq_trans; [|exact CS'].
        unfold s2. repeat split; rewrite !update_frame by discriminate; reflexivity.
      split. exact C0. split. exact STK. exact RB.
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcslen_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
  - (* loop *)
    destruct PRE as [k [RDI [WF [RSI [CNZ [MEM [RSP CS]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?dword_load_off in *.
    all: lazymatch goal with
    | |- exists _, _ =>
        exists (k + 1); split; [mlia64|];
        split; [intros i I; destruct (N.lt_ge_cases i k); [apply WF; assumption|];
                replace i with k by lia; split; assumption|];
        conj_tac
    | _ =>
        split; [ exists k; split; [assumption|];
                 first [ left; split; [assumption | reflexivity]
                       | right; split; [assumption|]; split; [assumption | reflexivity] ] |];
        fin
    end.
  - (* wcslen's RET *)
    destruct PRE as [k [NF [Z [RAX [MEM [RSP [CS [C0 [STK RB]]]]]]]]].
    unfold wcschr_cmem in MEM, NF, Z.
    repeat x64_step.
    destruct (STK C0) as [L [NL [ZL [LB NOV]]]].
    assert (KL: k = L).
    { apply (wnilfree_unique _ p _ L NF Z).
      intros i I. rewrite frame_words with (L:=L) by (assumption || lia). apply NL, I.
      rewrite frame_words with (L:=L) by (assumption || lia). exact ZL. }
    rewrite KL in *. rewrite (wcslen_ret L LB).
    split. exists L. split. intros i I. rewrite C0. split; apply NL, I.
      left. split. rewrite C0. exact ZL. f_equal. lia.
    split. frame_tac.
    split. apply N.mod_small, RB.
    callee_saved_tac.
Qed.


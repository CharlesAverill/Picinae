(* wcsnlen -- length of a fixed-size wide-character string (musl x86_64, C),
   composed with wmemchr

   SEMANTICS
   ---------
   musl's wcsnlen (src/string/wcsnlen.c) is

       const wchar_t *z = wmemchr(s, 0, n);
       if (z) n = z-s;
       return n;

   The binary saves RBP and RBX (keeping s and n there), reserves 8 more
   stack bytes and CALLs wmemchr (0x134ec0); it returns (z-s) >>> 2, or n
   when wmemchr returns NULL.  wmemchr's contract (wmemchr_proof.v; it
   writes no memory) is used through call_leaf_ni.

   SPECIFICATION (man 3 wcsnlen, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <wchar.h>
            size_t wcsnlen(const wchar_t s[.maxlen], size_t maxlen);

     DESCRIPTION
            The wcsnlen() function is the wide-character equivalent of the
            strnlen(3) function.  It returns the number of wide-characters in
            the string pointed to by s, not including the terminating null
            wide character (L'\0'), but at most maxlen wide characters (note:
            this parameter is not a byte count).  In doing this, wcsnlen()
            looks at only the first maxlen wide characters at s and never
            beyond s[maxlen-1].

     RETURN VALUE
            The wcsnlen() function returns wcslen(s), if that is less than
            maxlen, or maxlen if there is no null wide character among the
            first maxlen wide characters pointed to by s.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcsnlen at 0x65fa5, wmemchr at 0x34ec0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcsnlen_amd64.v, wmemchr_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = maxlen n; RSP = rsp; m = memory.  Preconditions
            (wcsnlen_ok): s <> 0, s + 4n <= 2^64 and 4n < 2^63 (a C object;
            the last makes the SAR exact), and the 4n bytes at s do not
            overlap the 32 bytes below rsp.  s need not be terminated.
   Output:  At the RET (0x165fd2): RAX = K where K <= n, the words s[0..K)
            are nonzero and s[K] = 0 if K < n.  No byte outside the 32 bytes
            below rsp has changed; RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcsnlen_amd64 CoqEtTu.programs.wmemchr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.wmemchr_proof CoqEtTu.proofs.wcslen_proof.
Open Scope N.

Definition wcsnlen_program : program := updateall2 wcsnlen_amd64 wmemchr_amd64.

Theorem wcsnlen_welltyped: welltyped_prog x64typctx wcsnlen_amd64.
Proof. exact wcsnlen_amd64.welltyped. Qed.

Lemma wcsnlen_program_welltyped: welltyped_prog x64typctx wcsnlen_program.
Proof.
  intros s a. unfold wcsnlen_program, updateall2, updateall.
  destruct (wmemchr_amd64 s a) as [[sz q]|] eqn:SC.
    pose proof (wmemchr_welltyped s a) as WT. rewrite SC in WT. exact WT.
    apply wcsnlen_welltyped.
Qed.

Definition wcsnlen_ok (p n rsp:N) :=
  0 < p /\ p + 4*n <= 2^64 /\ 4*n < 2^63 /\ ~ overlap 64 p (4*n) (rsp ⊖ 32) 32.

Definition wcsnlen_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165fd2 => true
  | _ => false end | _ => false end.

Definition wcsnlen_post (s0:store) (m p n:N) (s:store) :=
  (exists K, K <= n /\ wabsent m p 0 K /\ (K < n -> m Ⓓ[p ⊕ 4*K] = 0) /\ s R_RAX = K) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 32 /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wcsnlen_invs (s0:store) (m p n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165fa5 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ wcsnlen_ok p n (s0 R_RSP) /\
                      s0 R_RSP < 2^64)
  | 0x165fb6 => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBX] /\
                      s R_RDI = p /\ s R_RSI = 0 /\ s R_RDX = n /\
                      s R_RBX = n /\ s R_RBP = p /\ s R_RSP = s0 R_RSP ⊖ 24 /\
                      s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
                      s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15 /\
                      wcsnlen_ok p n (s0 R_RSP) /\ s0 R_RSP < 2^64 /\ s0 R_RBX < 2^64 /\
                      s0 R_RBP < 2^64)
  | 0x165fd2 => Some (wcsnlen_post s0 m p n s)
  | _ => None
  end | _ => None end.

(* The three stack writes leave the array's words alone. *)
Lemma push3_words:
  forall m p n rsp v1 v2 v3 i, ~ overlap 64 p (4*n) (rsp ⊖ 32) 32 -> i < n ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 32 := v3]) Ⓓ[p ⊕ 4*i] = m Ⓓ[p ⊕ 4*i].
Proof.
  intros m p n rsp v1 v2 v3 i NOV I.
  rewrite getmem_noverlap. rewrite getmem_noverlap. rewrite getmem_noverlap. reflexivity.
  - intros [a [y [A [Y E]]]]. apply NOV. exists (4*i + a), (24 + y). split. lia. split. lia. mlia64.
  - intros [a [y [A [Y E]]]]. apply NOV. exists (4*i + a), (16 + y). split. lia. split. lia. mlia64.
  - intros [a [y [A [Y E]]]]. apply NOV. exists (4*i + a), y. split. lia. split. lia. mlia64.
Qed.

Lemma found_nonnull4: forall p n K, 0 < p -> p + 4*n <= 2^64 -> K < n -> p ⊕ 4*K <> 0.
Proof. intros p n K P PN KN. rewrite N.mod_small by lia. lia. Qed.

Lemma found_idx4: forall p n K, p + 4*n <= 2^64 -> 4*n < 2^63 -> K < n -> (p ⊕ 4*K) ⊖ p >>> 2 = K.
Proof.
  intros p n K PN NB KN.
  replace ((p ⊕ 4*K) ⊖ p) with (4 ⊗ K).
  apply wcslen_ret. lia.
  rewrite (N.mod_small (p + 4*K)) by lia. rewrite N.mod_small by lia. unfold msub.
  change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma wcsnlen_frame:
  forall b rsp, 32 <= msub 64 b (rsp ⊖ 32) ->
  ~ overlap 64 b 1 (rsp ⊖ 32) 8 /\ ~ overlap 64 b 1 (rsp ⊖ 16) 8 /\ ~ overlap 64 b 1 (rsp ⊖ 8) 8.
Proof.
  intros b rsp B. split; [|split]; intros [x [y [X [Y E]]]]; mlia64.
Qed.

Theorem wcsnlen_correct:
  forall prog s t s' x' m p n
         (WCSNLEN: wcsnlen_amd64 ⊆2 prog) (WMEMCHR: wmemchr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165fa5, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (Nn: s R_RSI = n)
         (OK: wcsnlen_ok p n (s R_RSP)),
  satisfies_all prog (wcsnlen_invs s m p n) wcsnlen_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p n WCSNLEN WMEMCHR ENTRY MDL MEM P Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcsnlen_program).
    unfold wcsnlen_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcsnlen_invs.
    unfold wcsnlen_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p n MDL MEM P Nn OK RB RBXB RBPB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsnlen_program_welltyped. intro MDL1.
  clear - PRE MDL1 RB RBXB RBPB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [Nn [RSP [CS [OK RB']]]]]].
    repeat x64_step.
    destruct CS as (B & BP & B12 & B13 & B14 & B15). rewrite B, BP. conj_tac.
  - destruct PRE as [MEM [RDI [RSI [RDX [RBX [RBP [RSP [R12 [R13 [R14 [R15 [OK [RB' [RBXB' RBPB']]]]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcsnlen_program _ _ _ _ s2 nil _ s1 t MDL1 wcsnlen_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni wcsnlen_program wmemchr_amd64 _ _
              (wmemchr_invs s2 (s2 V_MEM64) p 0 n) wmemchr_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wmemchr_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wmemchr_correct; first
        [ apply pf2sub_refl | assumption | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; assumption) ].
    + intros a s t' NC. unfold wcsnlen_invs, wcsnlen_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wmemchr_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wmemchr_exit _) eqn:EX; [|destruct PRE].
      unfold wmemchr_exit in EX. addr_cases EX.
      all: simpl in PRE.
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcsnlen_program_welltyped).
      all: intro MDL3.
      all: destruct PRE as [RES [MEM' [RSP' CS']]].
      all: unfold s2 in *.
      all: rewrite !update_frame, update_updated in RSP' by discriminate.
      all: rewrite update_updated in RES, MEM'.
      all: change (0 mod 2^32) with 0 in RES.
      all: destruct OK as [P0 [PN [NB NOV]]].
      all: repeat x64_step.
      all: bc_norm.
      all: assert (RBXv: s' R_RBX = n) by (rewrite (proj1 CS'), !update_frame by discriminate; exact RBX).
      all: assert (RBPv: s' R_RBP = p) by (rewrite (proj1 (proj2 CS')), !update_frame by discriminate; exact RBP).
      all: assert (CSb: s' R_R12 = s0 R_R12 /\ s' R_R13 = s0 R_R13 /\ s' R_R14 = s0 R_R14 /\
                        s' R_R15 = s0 R_R15) by
             (destruct CS' as (_ & _ & C & D' & E & F); rewrite C, D', E, F;
              rewrite !update_frame by discriminate; repeat split; assumption).
      all: rewrite ?RBXv, ?RBPv in *.
      all: change (2 .& 63) with 2.
      all: split; [ destruct RES as [[K [KN [WA [WK RV]]]] | [WA RV]];
        [ rewrite RV in *; exists K; split; [lia|];
          split; [intros i I; rewrite <- (push3_words m p n (s0 R_RSP) (s0 R_RBP) (s0 R_RBX) 1466299 i NOV) by lia;
                  apply WA, I|];
          split; [intros _; rewrite <- (push3_words m p n (s0 R_RSP) (s0 R_RBP) (s0 R_RBX) 1466299 K NOV KN); exact WK|];
          first [ apply (found_idx4 p n K); assumption
                | exfalso; apply (found_nonnull4 p n K); assumption ]
        | rewrite RV in *; exists n; split; [lia|];
          split; [intros i I; rewrite <- (push3_words m p n (s0 R_RSP) (s0 R_RBP) (s0 R_RBX) 1466299 i NOV) by lia;
                  apply WA, I|];
          split; [intros; lia|];
          first [ reflexivity | exfalso; congruence ] ] |].
      all: split; [ repeat (apply stack_frame_store; [lia | reflexivity |]); apply stack_frame_refl |].
      all: split; [apply N.mod_small; assumption|].
      all: destruct CSb as (C12 & C13 & C14 & C15).
      all: repeat split; rewrite ?update_frame by discriminate;
           first [ assumption | rewrite update_updated; apply N.mod_small; assumption ].
Qed.

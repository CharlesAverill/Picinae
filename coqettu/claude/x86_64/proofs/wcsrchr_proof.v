(* wcsrchr -- locate the last occurrence of a wide character (musl x86_64,
   C), composed with wcslen

   SEMANTICS
   ---------
   musl's wcsrchr (src/string/wcsrchr.c) is

       const wchar_t *p;
       for (p=s+wcslen(s); p>=s && *p!=c; p--);
       return p>=s ? (wchar_t * )p : 0;

   The binary keeps s in RBX and c in EBP, CALLs wcslen (0x13c380), and
   scans backwards from s + 4 wcslen(s) with an unsigned pointer compare.
   wcslen's contract (wcslen_proof.v) is used through call_leaf_ni.

   SPECIFICATION (man 3 wcsrchr, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     wchar_t *wcsrchr(const wchar_t *wcs, wchar_t wc);
     wcsrchr is the wide-character equivalent of strrchr: it returns a
     pointer to the last occurrence of wc in the wide string wcs (the
     terminating L'\0' counts as part of the string), or NULL if wc does not
     occur.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcsrchr at 0x3c3b0, wcslen at 0x3c380 (Ghidra image base
            0x100000: 0x13c3b0, 0x13c380)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcsrchr_amd64.v, wcslen_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, ESI = wc (c32 = RSI mod 2^32); RSP = rsp; m = memory.
            Precondition (wcsrchr_ok): s is a wide string of length L with
            4L < 2^63; 4 <= s and s + 4L + 4 <= 2^64 (the array neither
            starts in the first 4 bytes nor wraps, so the backward pointer
            walk s-4 < s terminates as in C); its 4L+4 bytes do not overlap
            the 32 bytes below rsp.
   Output:  At the RET (0x13c3e7): either RAX = s + 4j for the largest
            j <= L with s[j] = c32, or no s[i] (i <= L) equals c32 and
            RAX = 0.  No byte outside the 32 bytes below rsp has changed;
            RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcsrchr_amd64 CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.wcslen_proof.
Open Scope N.

Definition wcsrchr_program : program := updateall2 wcsrchr_amd64 wcslen_amd64.

Theorem wcsrchr_welltyped: welltyped_prog x64typctx wcsrchr_amd64.
Proof. exact wcsrchr_amd64.welltyped. Qed.

Lemma wcsrchr_program_welltyped: welltyped_prog x64typctx wcsrchr_program.
Proof.
  intros s a. unfold wcsrchr_program, updateall2, updateall.
  destruct (wcslen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (wcslen_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply wcsrchr_welltyped.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition wcsrchr_ok (m p rsp:N) :=
  exists L, wnilfree m p L /\ m Ⓓ[p ⊕ 4*L] = 0 /\ 4*L < 2^63 /\ 4 <= p /\ p + 4*L + 4 <= 2^64 /\
    ~ overlap 64 p (4*L + 4) (rsp ⊖ 32) 32.

Definition wcsrchr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13c3e7 => true
  | _ => false end | _ => false end.

Definition wcsrchr_post (s0:store) (m p c:N) (s:store) :=
  (exists L, wnilfree m p L /\ m Ⓓ[p ⊕ 4*L] = 0 /\
     ((exists j, j <= L /\ m Ⓓ[p + 4*j] = c mod 2^32 /\
                 (forall i, j < i <= L -> m Ⓓ[p + 4*i] <> c mod 2^32) /\ s R_RAX = p + 4*j) \/
      ((forall i, i <= L -> m Ⓓ[p + 4*i] <> c mod 2^32) /\ s R_RAX = 0))) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 32 /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition cs4 (s0 s:store) :=
  s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

(* memory during the scan: the two pushes and wcslen's return address *)
Definition mscan (s0:store) (m:N) :=
  m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 32 := 0x13c3c0].

Definition wcsrchr_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13c3b0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c3bb => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBX] /\
                      s R_RDI = p /\ s R_RBX = p /\ s R_RBP = c mod 2^32 /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs4 s0 s)
  | 0x13c3d4 => Some (exists L e, wnilfree m p L /\ m Ⓓ[p ⊕ 4*L] = 0 /\ e <= L + 1 /\
                      (forall i, e <= i <= L -> m Ⓓ[p + 4*i] <> c mod 2^32) /\
                      s R_RAX = p + 4*e - 4 /\ s V_MEM64 = mscan s0 m /\
                      s R_RBX = p /\ s R_RBP = c mod 2^32 /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs4 s0 s)
  | 0x13c3e7 => Some (wcsrchr_post s0 m p c s)
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

(* the three stack stores leave the string's words alone *)
Lemma frame_words3:
  forall m p L rsp v1 v2 v3 i, ~ overlap 64 p (4*L + 4) (rsp ⊖ 32) 32 -> i <= L ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 32 := v3]) Ⓓ[p ⊕ 4*i] = m Ⓓ[p ⊕ 4*i].
Proof.
  intros m p L rsp v1 v2 v3 i NOV I.
  rewrite getmem_noverlap. rewrite getmem_noverlap. rewrite getmem_noverlap. reflexivity.
  - intros [x [y [X [Y E]]]]. apply NOV. exists (4*i + x), (24 + y). split. lia. split. lia. mlia.
  - intros [x [y [X [Y E]]]]. apply NOV. exists (4*i + x), (16 + y). split. lia. split. lia. mlia.
  - intros [x [y [X [Y E]]]]. apply NOV. exists (4*i + x), y. split. lia. split. lia. mlia.
Qed.

Lemma nowrap_word: forall p L i, p + 4*L + 4 <= 2^64 -> i <= L -> p ⊕ 4*i = p + 4*i.
Proof. intros. apply N.mod_small. lia. Qed.

Lemma cs4_tac_lemma: forall s0 s, callee_saved_eq s0 s -> cs4 s0 s.
Proof. intros s0 s (_&_&A&B&C&D). repeat split; assumption. Qed.

Ltac cs4_tac :=
  match goal with
  | CS: cs4 ?s0 _ |- cs4 ?s0 _ =>
      let B1 := fresh in let B2 := fresh in let B3 := fresh in let B4 := fresh in
      destruct CS as (B1 & B2 & B3 & B4); unfold cs4; repeat split;
      rewrite ?update_frame by discriminate; assumption
  | CS: callee_saved_eq ?s0 _ |- cs4 ?s0 _ =>
      let B0 := fresh in let B1 := fresh in let B2 := fresh in let B3 := fresh in
      let B4 := fresh in let B5 := fresh in
      destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold cs4; repeat split;
      rewrite ?update_frame by discriminate; assumption
  end.

Lemma qslot:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 32) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma mscan_rbx: forall s0 m, s0 R_RBX < 2^64 -> mscan s0 m Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBX.
Proof.
  intros. unfold mscan. rewrite getmem_noverlap by exact (qslot _ 16 32 eq_refl).
  rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma mscan_rbp: forall s0 m, s0 R_RBP < 2^64 -> mscan s0 m Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBP.
Proof.
  intros. unfold mscan. rewrite getmem_noverlap by exact (qslot _ 8 32 eq_refl).
  rewrite getmem_noverlap by exact (qslot _ 8 16 eq_refl).
  rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma mscan_frame: forall s0 m, stack_frame m (mscan s0 m) (s0 R_RSP) 32.
Proof.
  intros. unfold mscan.
  repeat (apply stack_frame_store; [lia | reflexivity |]). apply stack_frame_refl.
Qed.

Lemma mscan_word:
  forall s0 m p L i, ~ overlap 64 p (4*L + 4) (s0 R_RSP ⊖ 32) 32 -> p + 4*L + 4 <= 2^64 -> i <= L ->
  mscan s0 m Ⓓ[p + 4*i] = m Ⓓ[p + 4*i].
Proof.
  intros s0 m p L i NOV PW I. rewrite <- (nowrap_word p L i PW I). unfold mscan.
  apply (frame_words3 m p L); assumption.
Qed.

Lemma lt_p_e0: forall p e, 4 <= p -> (p + 4*e - 4 <? p) = true -> e = 0.
Proof. intros p e P H. apply N.ltb_lt in H. lia. Qed.

Lemma ge_p_e1: forall p e, 4 <= p -> (p + 4*e - 4 <? p) = false -> 1 <= e.
Proof. intros p e P H. apply N.ltb_ge in H. lia. Qed.

Lemma rax_j: forall p e, 4 <= p -> 1 <= e -> p + 4*e - 4 = p + 4*(e-1).
Proof. intros. lia. Qed.

Lemma rax_dec: forall p e L, 4 <= p -> 1 <= e -> e <= L + 1 -> p + 4*L + 4 <= 2^64 ->
  msub 64 (p + 4*e - 4) 4 = p + 4*(e-1) - 4.
Proof. intros. mlia. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem wcsrchr_correct:
  forall prog s t s' x' m p c
         (WCSRCHR: wcsrchr_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13c3b0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (OK: wcsrchr_ok m p (s R_RSP)),
  satisfies_all prog (wcsrchr_invs s m p c) wcsrchr_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c WCSRCHR WCSLEN ENTRY MDL MEM P C OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcsrchr_program).
    unfold wcsrchr_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcsrchr_invs.
    unfold wcsrchr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C OK RB RBXB RBPB PB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsrchr_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB PB. rename t1 into t.
  pose proof OK as (L0 & NL0 & ZL0 & LB & P4 & PW & NOV).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [C [RSP CS]]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & _). rewrite B0, B1.
    conj_tac. cs4_tac.
  - (* call wcslen(s) *)
    destruct PRE as [MEM [RDI [RBX [RBP [RSP CS]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcsrchr_program _ _ _ _ s2 nil _ s1 t MDL1 wcsrchr_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni wcsrchr_program wcslen_amd64 _ _ (wcslen_invs s2 (s2 V_MEM64) p) wcslen_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcslen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcslen_correct; first
        [ assumption | apply pf2sub_refl | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; exact RDI) ].
    + intros a s t' NC. unfold wcsrchr_invs, wcsrchr_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcsrchr_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [NF [Z RAX]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM', NF, Z.
      destruct CS' as (C0&C1&C2&C3&C4&C5).
      rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      assert (KL: k = L0).
      { apply (wnilfree_unique _ p _ L0 NF Z).
        intros i I. rewrite frame_words3 with (L:=L0) by (exact NOV || (clear - I; lia)). apply NL0, I.
        rewrite frame_words3 with (L:=L0) by (exact NOV || (clear; lia)). exact ZL0. }
      subst k. rewrite (wcslen_ret L0 LB) in RAX.
      repeat x64_step.
      exists L0, (L0 + 1). conj_tac.
      * apply N.le_refl.
      * intros i I. exfalso. clear - I. lia.
      * rewrite RBX, N.mod_small by (clear - PW; lia). clear. lia.
      * unfold mscan. sreflexivity.
      * rewrite C1. exact RBP.
      * destruct CS as (B2 & B3 & B4 & B5). unfold cs4. reg.
        rewrite C2, C3, C4, C5. repeat split; assumption.
  - destruct PRE as [L [e [NL [ZL [EL [NC [RAX [MEM [RBX [RBP [RSP CS]]]]]]]]]]].
    assert (LE: L = L0) by exact (wnilfree_unique m p L L0 NL ZL NL0 ZL0). subst L.
    repeat x64_step.
    + (* p-4 < p: not found *)
      match goal with BC: (_ <? _) = true |- _ => apply (lt_p_e0 p e P4) in BC; subst e end.
      rewrite mscan_rbx, mscan_rbp by assumption.
      split. exists L0. split. exact NL0. split. exact ZL0. right.
        split. intros i I. apply NC. split. apply N.le_0_l. exact I. reflexivity.
      split. apply mscan_frame.
      split. apply N.mod_small. exact RB.
      destruct CS as (C2 & C3 & C4 & C5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + (* found at e-1 *)
      match goal with BC: (_ <? _) = false |- _ => apply (ge_p_e1 p e P4) in BC; rename BC into E1 end.
      match goal with BC: (_ =? _) = true |- _ => apply N.eqb_eq in BC; rename BC into FOUND end.
      rewrite (rax_j p e P4 E1) in *.
      rewrite (mscan_word s0 m p L0 (e-1) NOV PW) in FOUND by (clear - EL E1; lia).
      rewrite mscan_rbx, mscan_rbp by assumption.
      split. exists L0. split. exact NL0. split. exact ZL0. left.
        exists (e - 1). split. clear - EL E1; lia. split. exact FOUND.
        split. intros i I. apply NC. clear - I; lia. reflexivity.
      split. apply mscan_frame.
      split. apply N.mod_small. exact RB.
      destruct CS as (C2 & C3 & C4 & C5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + (* step back *)
      match goal with BC: (_ <? _) = false |- _ => apply (ge_p_e1 p e P4) in BC; rename BC into E1 end.
      match goal with BC: (_ =? _) = false |- _ => apply N.eqb_neq in BC; rename BC into NF end.
      rewrite (rax_j p e P4 E1) in NF.
      rewrite (mscan_word s0 m p L0 (e-1) NOV PW) in NF by (clear - EL E1; lia).
      exists L0, (e - 1). rewrite (rax_dec p e L0 P4 E1 EL PW).
      conj_tac.
      all: first
        [ (clear - EL; lia)
        | (intros i I; destruct (N.eq_dec i (e - 1)) as [->|NE]; [exact NF | apply NC; clear - I NE; lia])
        | cs4_tac ].
Qed.

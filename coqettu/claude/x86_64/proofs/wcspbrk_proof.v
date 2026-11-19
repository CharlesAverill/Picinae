(* wcspbrk -- locate the first wide character of a string that is in a set
   (musl x86_64, C), composed with wcscspn (-> wcschr -> wcslen, wcslen)

   SEMANTICS
   ---------
   musl's wcspbrk (src/string/wcspbrk.c) is

       s += wcscspn(s, b);
       return *s ? (wchar_t * )s : 0;

   compiled to PUSH RBX; CALL wcscspn (0x165e5a); LEA RAX,[RBX+RAX*4];
   POP RBX; CMOVZ on the word there; RET.  The call is composed with
   call_leaf_ni (lib/x64_compose.v) over wcscspn's contract, whose exits
   include wcslen's RET at wcscspn's stack depth (wcscspn_exit).

   SPECIFICATION (man 3 wcspbrk, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     wchar_t *wcspbrk(const wchar_t *wcs, const wchar_t *accept);
     wcspbrk returns a pointer to the first occurrence in wcs of any of the
     characters in accept, or NULL if there is none.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcspbrk at 0x65fd3, wcscspn at 0x65e5a, wcschr at 0x3c310,
            wcslen at 0x3c380 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcspbrk_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = b (the set); RSP = rsp; m = memory.  Precondition
            (wcspbrk_ok): s and b are wide strings (4L < 2^63 for s) that are
            C objects (nonzero, no wrap) and whose words through the
            terminators do not overlap the 80 bytes below rsp.
   Output:  At the RET (0x165feb): for some K, every word s[i] (i < K) is
            nonzero and not in b, and either s[K] = 0 and RAX = 0 (NULL), or
            s[K] is nonzero, occurs in b, and RAX = s + 4K.  Nothing outside
            the 80 bytes below rsp changes; RSP = rsp; RBX, RBP, R12-R15 are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcspbrk_amd64 CoqEtTu.programs.wcscspn_amd64
               CoqEtTu.programs.wcschr_amd64 CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.wcslen_proof CoqEtTu.proofs.wcschr_proof CoqEtTu.proofs.wcsspn_proof
               CoqEtTu.proofs.wcscspn_proof.
Open Scope N.

Definition wcspbrk_program : program := updateall2 wcspbrk_amd64 wcscspn_program.

Theorem wcspbrk_welltyped: welltyped_prog x64typctx wcspbrk_amd64.
Proof. exact wcspbrk_amd64.welltyped. Qed.

Lemma wcspbrk_program_welltyped: welltyped_prog x64typctx wcspbrk_program.
Proof.
  intros s a. unfold wcspbrk_program, updateall2 at 1, updateall.
  destruct (wcscspn_program s a) as [[sz q]|] eqn:SL.
    pose proof (wcscspn_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply wcspbrk_welltyped.
Qed.

Lemma wcscspn_in_prog: wcscspn_amd64 ⊆2 wcscspn_program.
Proof.
  intros s a insn SC. unfold wcscspn_program, wcschr_program, updateall2, updateall.
  destruct (wcslen_amd64 s a) eqn:SL.
  - exfalso. revert SC SL. unfold wcscspn_amd64, wcslen_amd64.
    repeat first
    [ discriminate
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - destruct (wcschr_amd64 s a) eqn:SC2; [|exact SC].
    exfalso. revert SC SC2. unfold wcscspn_amd64, wcschr_amd64.
    repeat first
    [ discriminate
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma wcschr_in_cspn: wcschr_amd64 ⊆2 wcscspn_program.
Proof. intros s a insn H. apply subset_updateall2. apply wcschr_in_prog, H. Qed.

Definition wcspbrk_ok (m s c rsp:N) :=
  (exists L, wnilfree m s L /\ m Ⓓ[s ⊕ 4*L] = 0 /\ 4*L < 2^63 /\ 0 < s /\ s + 4*L + 4 <= 2^64 /\
              ~ overlap 64 s (4*L + 4) (rsp ⊖ 80) 80) /\
  (exists Lc, wnilfree m c Lc /\ m Ⓓ[c ⊕ 4*Lc] = 0 /\ 0 < c /\ c + 4*Lc + 4 <= 2^64 /\
              ~ overlap 64 c (4*Lc + 4) (rsp ⊖ 80) 80).

Definition wcspbrk_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165feb => true
  | _ => false end | _ => false end.

Definition wcspbrk_post (s0:store) (m p c:N) (s:store) :=
  (exists K, cspre m p c K /\
     ((m Ⓓ[p ⊕ 4*K] = 0 /\ s R_RAX = 0) \/
      (m Ⓓ[p ⊕ 4*K] <> 0 /\ inset m c (m Ⓓ[p ⊕ 4*K]) /\ s R_RAX = p ⊕ 4*K))) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 80 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wcspbrk_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165fd3 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165feb => Some (wcspbrk_post s0 m p c s)
  | _ => None
  end | _ => None end.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

(* ---- facts, each proved in an empty context ---- *)

Lemma word_byte80:
  forall x N rsp i a, ~ overlap 64 x (4*N + 4) (rsp ⊖ 80) 80 -> i <= N -> msub 64 a (x ⊕ 4*i) < 4 ->
  80 <= msub 64 a (rsp ⊖ 80).
Proof.
  intros x N rsp i a NOV I A.
  destruct (N.le_gt_cases 80 (msub 64 a (rsp ⊖ 80))) as [H|H]. exact H. exfalso.
  apply NOV. exists (4*i + msub 64 a (x ⊕ 4*i)), (msub 64 a (rsp ⊖ 80)).
  split. lia. split. exact H. mlia.
Qed.

Lemma f80_64: forall b rsp, 80 <= msub 64 b (rsp ⊖ 80) -> 64 <= msub 64 b (rsp ⊖ 16 ⊖ 64).
Proof. intros. mlia. Qed.

Lemma push2_word:
  forall (m:memory) x N rsp v1 v2 i, rsp < 2^64 -> ~ overlap 64 x (4*N + 4) (rsp ⊖ 80) 80 -> i <= N ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2]) Ⓓ[x ⊕ 4*i] = m Ⓓ[x ⊕ 4*i].
Proof.
  intros m x N rsp v1 v2 i RB NOV I. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE).
  pose proof (word_byte80 x N rsp i a NOV I A) as B.
  rewrite (stack_store_frame _ rsp 16 _ a 80) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 8 _ a 80) by (assumption || lia).
  reflexivity.
Qed.

Lemma after_word:
  forall (M M':memory) x N rsp i, stack_frame M M' (rsp ⊖ 16) 64 ->
  ~ overlap 64 x (4*N + 4) (rsp ⊖ 80) 80 -> i <= N -> M' Ⓓ[x ⊕ 4*i] = M Ⓓ[x ⊕ 4*i].
Proof.
  intros M M' x N rsp i SF NOV I. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply SF. apply f80_64. exact (word_byte80 x N rsp i a NOV I A).
Qed.

Lemma slot_after:
  forall (M M':memory) rsp j, stack_frame M M' (rsp ⊖ 16) 64 -> (j = 8 \/ j = 16) ->
  M' Ⓠ[rsp ⊖ j] = M Ⓠ[rsp ⊖ j].
Proof.
  intros M M' rsp j SF J. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply SF. destruct J; subst j; mlia.
Qed.

Lemma frame_final:
  forall (m M':memory) rsp v1 v2, rsp < 2^64 ->
  stack_frame (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2]) M' (rsp ⊖ 16) 64 -> stack_frame m M' rsp 80.
Proof.
  intros m M' rsp v1 v2 RB SF b B. rewrite (SF b (f80_64 b rsp B)).
  rewrite (stack_store_frame _ rsp 16 _ b 80) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 8 _ b 80) by (assumption || lia).
  reflexivity.
Qed.

Lemma sub80_64: forall x L rsp, ~ overlap 64 x L (rsp ⊖ 80) 80 -> ~ overlap 64 x L (rsp ⊖ 16 ⊖ 64) 64.
Proof.
  intros x L rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. exact I. split. lia.
  rewrite E. f_equal. f_equal. mlia.
Qed.

Lemma wcfree_agree:
  forall (M m:memory) c w k N, (forall i, i <= N -> M Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i]) ->
  m Ⓓ[c ⊕ 4*N] = 0 -> wcfree M c w k -> k <= N /\ wcfree m c w k.
Proof.
  intros M m c w k N AG Z CF.
  assert (KN: k <= N).
  { destruct (N.le_gt_cases k N) as [H|H]. exact H. exfalso. apply (proj1 (CF N H)).
    rewrite (AG N (N.le_refl N)). exact Z. }
  split. exact KN. intros i I. rewrite <- (AG i) by (clear - I KN; lia). apply CF, I.
Qed.

Lemma notin_agree:
  forall (M m:memory) c w N, (forall i, i <= N -> M Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i]) ->
  m Ⓓ[c ⊕ 4*N] = 0 -> notin M c w -> notin m c w.
Proof.
  intros M m c w N AG Z [k [CF Zk]]. destruct (wcfree_agree M m c w k N AG Z CF) as [KN CFm].
  exists k. split. exact CFm. rewrite <- (AG k KN). exact Zk.
Qed.

Lemma inset_agree:
  forall (M m:memory) c w N, (forall i, i <= N -> M Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i]) ->
  m Ⓓ[c ⊕ 4*N] = 0 -> inset M c w -> inset m c w.
Proof.
  intros M m c w N AG Z [k [CF Zk]]. destruct (wcfree_agree M m c w k N AG Z CF) as [KN CFm].
  exists k. split. exact CFm. rewrite <- (AG k KN). exact Zk.
Qed.

Lemma cspre_agree:
  forall (M m:memory) p c K L Lc,
  (forall i, i <= L -> M Ⓓ[p ⊕ 4*i] = m Ⓓ[p ⊕ 4*i]) -> m Ⓓ[p ⊕ 4*L] = 0 ->
  (forall i, i <= Lc -> M Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i]) -> m Ⓓ[c ⊕ 4*Lc] = 0 ->
  cspre M p c K -> K <= L /\ cspre m p c K.
Proof.
  intros M m p c K L Lc AP ZP AC ZC SP.
  assert (KL: K <= L).
  { destruct (N.le_gt_cases K L) as [H|H]. exact H. exfalso. apply (proj1 (SP L H)).
    rewrite (AP L (N.le_refl L)). exact ZP. }
  split. exact KL. intros i I. destruct (SP i I) as [A B].
  rewrite <- (AP i) by (clear - I KL; lia). split. exact A.
  exact (notin_agree M m c _ Lc AC ZC B).
Qed.

Lemma wnilfree_agree:
  forall (M m:memory) p L, (forall i, i <= L -> M Ⓓ[p ⊕ 4*i] = m Ⓓ[p ⊕ 4*i]) ->
  wnilfree m p L -> wnilfree M p L.
Proof. intros M m p L AG NL i I. rewrite (AG i) by (clear - I; lia). apply NL, I. Qed.

Lemma lea4: forall p k, p + 4*k < 2^64 -> (p + k * 4) mod 2^64 = p ⊕ 4*k.
Proof. intros. rewrite N.mul_comm. reflexivity. Qed.

Theorem wcspbrk_correct:
  forall prog s t s' x' m p c
         (WCSPBRK: wcspbrk_amd64 ⊆2 prog) (WCSCSPN: wcscspn_amd64 ⊆2 prog)
         (WCSCHR: wcschr_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165fd3, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (OK: wcspbrk_ok m p c (s R_RSP)),
  satisfies_all prog (wcspbrk_invs s m p c) wcspbrk_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c WCSPBRK WCSCSPN WCSCHR WCSLEN ENTRY MDL MEM P C OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  assert (CB: c < 2^64) by (rewrite <- C; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcspbrk_program).
    unfold wcspbrk_program, wcscspn_program, wcschr_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcspbrk_invs.
    unfold wcspbrk_program, wcscspn_program, wcschr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C OK RB RBXB PB CB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcspbrk_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB PB CB. rename t1 into t.
  destruct OK as [(L & NL & ZL & LB & P0 & PW & OVs) (Lc & NLc & ZLc & C0 & CW & OVc)].
  destruct_inv 64 PRE.
  destruct PRE as [MEM [P [C [RSP CS]]]].
  x64_step. x64_step. x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
  apply (models_after_steps wcspbrk_program _ _ _ _ s2 t0 _ s1 t MDL1 wcspbrk_program_welltyped).
  intro MDL2.
  destruct CS as (B0 & B1 & B2 & B3 & B4 & B5).
  assert (S2M: s2 V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s1 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := 0x165fdc])
    by (unfold s2; reg; sreflexivity).
  assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 16) by (unfold s2; reg; reflexivity).
  assert (AGp: forall i, i <= L -> (m [Ⓠs0 R_RSP ⊖ 8 := s1 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := 0x165fdc]) Ⓓ[p ⊕ 4*i] = m Ⓓ[p ⊕ 4*i])
    by (intros i I; exact (push2_word m p L _ _ _ i RB OVs I)).
  assert (AGc: forall i, i <= Lc -> (m [Ⓠs0 R_RSP ⊖ 8 := s1 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := 0x165fdc]) Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i])
    by (intros i I; exact (push2_word m c Lc _ _ _ i RB OVc I)).
  eapply (call_leaf_ni wcspbrk_program wcscspn_program _ _ (wcscspn_invs s2 (s2 V_MEM64) p c) (wcscspn_exit s2)).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold wcscspn_invs.
    unfold wcscspn_program, wcschr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x' s''] START. apply wcscspn_correct; first
      [ apply wcscspn_in_prog | apply wcschr_in_cspn | apply wcslen_in_cspn | reflexivity | assumption
      | (unfold s2; reg; first [reflexivity | exact C]) | idtac ].
    rewrite S2M, S2R. split.
    + exists L. split. exact (wnilfree_agree _ m p L AGp NL).
      split. rewrite (AGp L (N.le_refl L)). exact ZL.
      split. exact LB. split. exact P0. split. exact PW. apply sub80_64, OVs.
    + exists Lc. split. exact (wnilfree_agree _ m c Lc AGc NLc).
      split. rewrite (AGc Lc (N.le_refl Lc)). exact ZLc.
      split. exact C0. split. exact CW. apply sub80_64, OVc.
  - intros a s t' NC. unfold wcspbrk_invs, wcspbrk_exit.
    unfold wcscspn_program, wcschr_program, updateall2, updateall in NC.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity)
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold wcscspn_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
  - intros a' s' t2 ENTRY' UT PRE.
    unfold get_postcondition in PRE.
    destruct (wcscspn_exit _ _) eqn:EX; [|destruct PRE].
    unfold wcscspn_exit in EX. addr_cases EX.
    all: simpl in PRE.
    all: match goal with H: context [wcscspn_post] |- _ => rename H into PR0 end.
    all: try (rewrite EX in PR0; cbv beta iota in PR0).
    all: rewrite app_assoc.
    all: apply (models_after_steps _ _ _ _ _ s' (t2 ++ t0) _ s1 t MDL1 wcspbrk_program_welltyped).
    all: intro MDL3.
    all: destruct PR0 as [[K [SP [RES RAXK]]] [SF [RSP' CS']]].
    all: rewrite S2M in SP, RES, SF. all: rewrite S2R in SF, RSP'.
    all: destruct (cspre_agree _ m p c K L Lc AGp ZL AGc ZLc SP) as [KL SPm].
    all: rewrite (AGp K KL) in RES.
    all: assert (WK: s' V_MEM64 Ⓓ[p ⊕ 4*K] = m Ⓓ[p ⊕ 4*K])
           by (rewrite (after_word _ _ p L _ K SF OVs KL); exact (AGp K KL)).
    all: assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 0x165fdc)
           by (rewrite (slot_after _ _ _ 16 SF (or_intror eq_refl)); rewrite getmem_setmem by discriminate; reflexivity).
    all: assert (RBXs: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBX)
           by (rewrite (slot_after _ _ _ 8 SF (or_introl eq_refl));
               rewrite getmem_noverlap by exact (qslot64 _ 8 16 eq_refl);
               rewrite getmem_setmem by discriminate; rewrite B0; apply N.mod_small, RBXB).
    all: destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
    all: unfold s2 in D0, D1, D2, D3, D4, D5.
    all: rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
    all: rewrite ?update_updated in D0.
    all: x64_step; rewrite RA; repeat x64_step.
    all: assert (WK': s' V_MEM64 Ⓓ[p + K*4] = m Ⓓ[p ⊕ 4*K])
           by (rewrite (N.mul_comm K 4), <- (dword_load_off (s' V_MEM64) p (4*K)); exact WK).
    all: match goal with BC: (_ =? 0) = _ |- _ => rewrite WK' in BC end.
    all: split; [exists K; split; [exact SPm |];
           match goal with
           | BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC; left; split; [exact BC | reflexivity]
           | BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC; right;
               destruct RES as [Z|IN]; [exfalso; exact (BC Z) |];
               split; [exact BC |]; split; [exact (inset_agree _ m c _ Lc AGc ZLc IN) |];
               rewrite (N.mul_comm K 4); reflexivity
           end |].
    all: split; [exact (frame_final m _ _ _ _ RB SF) |].
    all: split; [apply N.mod_small, RB |].
    all: unfold callee_saved_eq; repeat split; reg.
    all: first [exact RBXs | (rewrite ?D1, ?D2, ?D3, ?D4, ?D5; reg; sassumption)].
Qed.
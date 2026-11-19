(* wcsspn -- length of the initial segment of a wide string consisting of
   characters from a set (musl x86_64, C), composed with wcschr (-> wcslen)

   SEMANTICS
   ---------
   musl's wcsspn (src/string/wcsspn.c) is

       const wchar_t *a;
       for (a=s; *a && wcschr(c, *a); a++);
       return a-s;

   The binary keeps s in R12, c in RBP and a in RBX, and CALLs wcschr
   (0x13c310) once per character.  wcschr's contract (wcschr_proof.v, itself
   composed with wcslen) is used through call_leaf_ni; since the character
   is never 0 there, wcschr's c = 0 precondition is vacuous.

   SPECIFICATION (man 3 wcsspn, Linux man-pages 6.9.1, paraphrased)
   ---------------------------------------------------------------
     size_t wcsspn(const wchar_t *wcs, const wchar_t *accept);
     wcsspn returns the length of the longest initial segment of wcs that
     consists entirely of wide characters in accept.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcsspn at 0x65fec, wcschr at 0x3c310 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcsspn_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = c (the set); RSP = rsp; m = memory.  Precondition
            (wspn_ok): s and c are wide strings (lengths L and Lc, 4L < 2^63)
            whose words through the terminators do not overlap the 64 bytes
            below rsp (wcsspn's frame and wcschr's); c is a C object
            (0 < c, c + 4Lc + 4 <= 2^64), so that a match never makes
            wcschr return NULL.
   Output:  At the RET (0x166020): RAX = K where for i < K the word s[i] is
            nonzero and occurs in c before c's terminator (inset), and
            s[K] = 0 or s[K] does not occur in c (notin).  Nothing outside
            the 64 bytes below rsp changes; RSP = rsp; RBX, RBP, R12-R15 are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcsspn_amd64 CoqEtTu.programs.wcschr_amd64 CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.wcslen_proof CoqEtTu.proofs.wcschr_proof.
Open Scope N.

Definition wcsspn_program : program := updateall2 wcsspn_amd64 wcschr_program.

Theorem wcsspn_welltyped: welltyped_prog x64typctx wcsspn_amd64.
Proof. exact wcsspn_amd64.welltyped. Qed.

Lemma wcsspn_program_welltyped: welltyped_prog x64typctx wcsspn_program.
Proof.
  intros s a. unfold wcsspn_program, updateall2 at 1, updateall.
  destruct (wcschr_program s a) as [[sz q]|] eqn:SL.
    pose proof (wcschr_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply wcsspn_welltyped.
Qed.

Lemma wcschr_in_prog: wcschr_amd64 ⊆2 wcschr_program.
Proof.
  intros s a insn SC. unfold wcschr_program, updateall2, updateall.
  destruct (wcslen_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold wcschr_amd64, wcslen_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

(* w occurs in the set c before its terminator *)
Definition inset (m:memory) (c w:N) := exists k, wcfree m c w k /\ m Ⓓ[c ⊕ 4*k] = w.
Definition notin (m:memory) (c w:N) := exists k, wcfree m c w k /\ m Ⓓ[c ⊕ 4*k] = 0.

Definition wspn_ok (m s c rsp:N) :=
  (exists L, wnilfree m s L /\ m Ⓓ[s ⊕ 4*L] = 0 /\ 4*L < 2^63 /\ ~ overlap 64 s (4*L + 4) (rsp ⊖ 64) 64) /\
  (exists Lc, wnilfree m c Lc /\ m Ⓓ[c ⊕ 4*Lc] = 0 /\ 0 < c /\ c + 4*Lc + 4 <= 2^64 /\
              ~ overlap 64 c (4*Lc + 4) (rsp ⊖ 64) 64).

Definition spanpre (m:memory) (s c k:N) :=
  forall i, i < k -> m Ⓓ[s ⊕ 4*i] <> 0 /\ inset m c (m Ⓓ[s ⊕ 4*i]).

Definition frm64 (s0:store) (m M:memory) :=
  (forall b, 64 <= msub 64 b (s0 R_RSP ⊖ 64) -> M Ⓑ[b] = m Ⓑ[b]) /\
  M Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R12 /\ M Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\ M Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX.

Definition cs3 (s0 s:store) := s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition wcsspn_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x166020 => true
  | _ => false end | _ => false end.

Definition wcsspn_post (s0:store) (m p c:N) (s:store) :=
  (exists K, spanpre m p c K /\ (m Ⓓ[p ⊕ 4*K] = 0 \/ notin m c (m Ⓓ[p ⊕ 4*K])) /\ s R_RAX = K) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 64 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wcsspn_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165fec => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165fff => Some (exists k, spanpre m p c k /\ frm64 s0 m (s V_MEM64) /\
                      s R_RBX = p ⊕ 4*k /\ s R_R12 = p /\ s R_RBP = c /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x166008 => Some (exists k, spanpre m p c k /\ m Ⓓ[p ⊕ 4*k] <> 0 /\ s R_RSI mod 2^32 = m Ⓓ[p ⊕ 4*k] /\
                      s R_RDI = c /\ frm64 s0 m (s V_MEM64) /\
                      s R_RBX = p ⊕ 4*k /\ s R_R12 = p /\ s R_RBP = c /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x166020 => Some (wcsspn_post s0 m p c s)
  | _ => None
  end | _ => None end.

(* ---- facts, each proved in an empty context ---- *)

Lemma qslot64:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 64) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma frm64_init:
  forall s0 m, s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 ->
  frm64 s0 m (m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX]).
Proof.
  intros s0 m B1 B2 B3. split; [|split; [|split]].
  - intros b B.
    rewrite (stack_store_frame _ (s0 R_RSP) 24 _ b 64) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 64) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 64) by (assumption || lia).
    reflexivity.
  - rewrite getmem_noverlap by exact (qslot64 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma frm64_ra: forall s0 m M v, frm64 s0 m M -> frm64 s0 m (M [Ⓠs0 R_RSP ⊖ 32 := v]).
Proof.
  intros s0 m M v [F [S8 [S16 S24]]]. split; [|split; [|split]].
  - intros b B. rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 64) by (assumption || lia). apply F, B.
  - rewrite getmem_noverlap by exact (qslot64 _ 8 32 eq_refl). exact S8.
  - rewrite getmem_noverlap by exact (qslot64 _ 16 32 eq_refl). exact S16.
  - rewrite getmem_noverlap by exact (qslot64 _ 24 32 eq_refl). exact S24.
Qed.

Lemma word_byte64:
  forall x N rsp i a, ~ overlap 64 x (4*N + 4) (rsp ⊖ 64) 64 -> i <= N -> msub 64 a (x ⊕ 4*i) < 4 ->
  64 <= msub 64 a (rsp ⊖ 64).
Proof.
  intros x N rsp i a NOV I A.
  destruct (N.le_gt_cases 64 (msub 64 a (rsp ⊖ 64))) as [H|H]. exact H. exfalso.
  apply NOV. exists (4*i + msub 64 a (x ⊕ 4*i)), (msub 64 a (rsp ⊖ 64)).
  split. lia. split. exact H. mlia.
Qed.

Lemma frm64_word:
  forall s0 m M x N i, frm64 s0 m M -> ~ overlap 64 x (4*N + 4) (s0 R_RSP ⊖ 64) 64 -> i <= N ->
  M Ⓓ[x ⊕ 4*i] = m Ⓓ[x ⊕ 4*i].
Proof.
  intros s0 m M x N i [F _] NOV I. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply F. exact (word_byte64 x N _ i a NOV I A).
Qed.

Lemma slot_32: forall a rsp j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32) ->
  msub 64 a (rsp ⊖ j) < 8 -> 32 <= msub 64 a (rsp ⊖ 32 ⊖ 32).
Proof. intros a rsp j J A. destruct J as [J|[J|[J|J]]]; subst j; mlia. Qed.

Lemma f64_32: forall b rsp, 64 <= msub 64 b (rsp ⊖ 64) -> 32 <= msub 64 b (rsp ⊖ 32 ⊖ 32).
Proof. intros. mlia. Qed.

Lemma frm64_after:
  forall s0 m M M', frm64 s0 m M -> stack_frame M M' (s0 R_RSP ⊖ 32) 32 -> frm64 s0 m M'.
Proof.
  intros s0 m M M' [F [S8 [S16 S24]]] SF. split; [|split; [|split]].
  - intros b B. rewrite (SF b (f64_32 b _ B)). apply F, B.
  - rewrite <- S8. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot_32 a _ 8). left; reflexivity. exact A.
  - rewrite <- S16. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot_32 a _ 16). right; left; reflexivity. exact A.
  - rewrite <- S24. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot_32 a _ 24). right; right; left; reflexivity. exact A.
Qed.

Lemma ra_after:
  forall M M' rsp v, stack_frame M M' (rsp ⊖ 32) 32 -> M Ⓠ[rsp ⊖ 32] = v -> M' Ⓠ[rsp ⊖ 32] = v.
Proof.
  intros M M' rsp v SF V. rewrite <- V. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply SF. apply (slot_32 a _ 32). right; right; right; reflexivity. exact A.
Qed.

Lemma frm64_frame: forall s0 m M, frm64 s0 m M -> stack_frame m M (s0 R_RSP) 64.
Proof. intros s0 m M [F _] b B. apply F, B. Qed.

Lemma sub64_32: forall x L rsp, ~ overlap 64 x L (rsp ⊖ 64) 64 -> ~ overlap 64 x L (rsp ⊖ 32 ⊖ 32) 32.
Proof.
  intros x L rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. exact I. split. lia.
  rewrite E. f_equal. f_equal. mlia.
Qed.

Lemma wcfree_len: forall m p c k L, wcfree m p c k -> m Ⓓ[p ⊕ 4*L] = 0 -> k <= L.
Proof.
  intros m p c k L CF Z. destruct (N.le_gt_cases k L) as [H|H]. exact H.
  exfalso. exact (proj1 (CF L H) Z).
Qed.

Lemma spanpre_len: forall m s c k L, spanpre m s c k -> m Ⓓ[s ⊕ 4*L] = 0 -> k <= L.
Proof.
  intros m s c k L SP Z. destruct (N.le_gt_cases k L) as [H|H]. exact H.
  exfalso. exact (proj1 (SP L H) Z).
Qed.

Lemma spanpre_succ: forall m s c k, spanpre m s c k -> m Ⓓ[s ⊕ 4*k] <> 0 -> inset m c (m Ⓓ[s ⊕ 4*k]) ->
  spanpre m s c (k + 1).
Proof.
  intros m s c k SP A B i I. destruct (N.lt_ge_cases i k). apply SP. assumption.
  replace i with k by lia. split; assumption.
Qed.

Lemma msub_off: forall p k, p < 2^64 -> msub 64 (p ⊕ 4*k) p = 4 ⊗ k.
Proof. intros. mlia. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Ltac cs3_close :=
  match goal with CS: cs3 ?s0 _ |- cs3 ?s0 _ =>
    let a := fresh in let b := fresh in let c := fresh in
    destruct CS as (a & b & c); unfold cs3; repeat split; reg; assumption end.

Theorem wcsspn_correct:
  forall prog s t s' x' m p c
         (WCSSPN: wcsspn_amd64 ⊆2 prog) (WCSCHR: wcschr_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165fec, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (OK: wspn_ok m p c (s R_RSP)),
  satisfies_all prog (wcsspn_invs s m p c) wcsspn_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c WCSSPN WCSCHR WCSLEN ENTRY MDL MEM P C OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcsspn_program).
    unfold wcsspn_program, wcschr_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcsspn_invs.
    unfold wcsspn_program, wcschr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C OK RB RBXB RBPB R12B PB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcsspn_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B PB. rename t1 into t.
  destruct OK as [(L & NL & ZL & LB & OVs) (Lc & NLc & ZLc & C0 & CW & OVc)].
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [C [RSP CS]]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B2.
    exists 0. split. intros i I. exfalso. exact (N.nlt_0_r i I).
    split. apply frm64_init; assumption.
    split. rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact PB. reflexivity.
    conj_tac. unfold cs3. repeat split; reg; assumption.
  - destruct PRE as [k [SP [FR [RBX [R12 [RBP [RSP CS]]]]]]].
    assert (KL: k <= L) by exact (spanpre_len m p c k L SP ZL).
    assert (BW: s1 V_MEM64 Ⓓ[p + 4*k] = m Ⓓ[p ⊕ 4*k])
      by (rewrite <- getmem_mod_l; exact (frm64_word s0 m _ p L k FR OVs KL)).
    pose proof FR as [_ [T8 [T16 T24]]].
    repeat x64_step.
    all: rewrite ?BW in *.
    + match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC end.
      change (2 .& 63) with 2. rewrite (wcslen_ret k ltac:(clear - KL LB; lia)).
      rewrite T8, T16, T24.
      split. exists k. split. exact SP. split. left. assumption. reflexivity.
      split. exact (frm64_frame _ _ _ FR).
      split. apply N.mod_small. exact RB.
      destruct CS as (B3 & B4 & B5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC end.
      exists k. conj_tac. cs3_close.
  - destruct PRE as [k [SP [NZ [RSI [RDI [FR [RBX [R12 [RBP [RSP CS]]]]]]]]]].
    assert (KL: k <= L) by exact (spanpre_len m p c k L SP ZL).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcsspn_program _ _ _ _ s2 nil _ s1 t MDL1 wcsspn_program_welltyped).
    intro MDL2.
    pose proof (frm64_ra _ _ _ 0x16600d FR) as FR2.
    assert (CB: forall i, i <= Lc -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x16600d]) Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i])
      by (intros i I; exact (frm64_word s0 m _ c Lc i FR2 OVc I)).
    eapply (call_leaf_ni wcsspn_program wcschr_program _ _ (wcschr_invs s2 (s2 V_MEM64) c (s2 R_RSI)) wcschr_exit).
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
    + intros a s t' NC. unfold wcsspn_invs, wcsspn_exit.
      unfold wcschr_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
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
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcsspn_program_welltyped).
      all: intro MDL3.
      all: destruct PRE as [[kk [CF RES]] [SF [RSP' CS']]].
      all: unfold s2 in CF, RES, SF, RSP', CS'.
      all: rewrite ?update_updated in CF, RES, SF.
      all: rewrite !update_frame in RSP' by discriminate.
      all: rewrite update_updated in RSP'.
      all: rewrite ?update_frame in CF, RES by discriminate.
      all: rewrite ?RSI in CF, RES.
      all: assert (KK: kk <= Lc) by (apply (wcfree_len _ c (m Ⓓ[p ⊕ 4*k]) kk Lc CF); rewrite CB by (clear; lia); exact ZLc).
      all: assert (CFm: wcfree m c (m Ⓓ[p ⊕ 4*k]) kk)
             by (intros i I; rewrite <- (CB i) by (clear - I KK; lia); apply CF, I).
      all: rewrite (CB kk KK) in RES.
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
      all: try (rewrite RBX, R12, msub_off by exact PB; change (2 .& 63) with 2;
                rewrite (wcslen_ret k ltac:(clear - KL LB; lia))).
      all: first
        [ (split; [exists k; split; [exact SP | split; [right; exists kk; split; [exact CFm | exact HK] | reflexivity]] |];
           split; [exact (frm64_frame _ _ _ FR3) |]; split; [apply N.mod_small; exact RB |];
           destruct CS as (B3 & B4 & B5); unfold callee_saved_eq; repeat split; reg;
           first [sassumption | (rewrite ?D3, ?D4, ?D5; sassumption)])
        | (exists (k + 1); split; [apply spanpre_succ; [exact SP | exact NZ | exists kk; split; [exact CFm | exact HK]] |];
           split; [exact FR3 |];
           split; [rewrite RBX, N.add_mod_idemp_r by discriminate; f_equal; pure_lia |];
           split; [rewrite D2; reg; exact R12 |]; split; [rewrite D1; reg; exact RBP |];
           split; [reflexivity |];
           destruct CS as (B3 & B4 & B5); unfold cs3; repeat split; reg; rewrite ?D3, ?D4, ?D5; assumption)
        ].
Qed.

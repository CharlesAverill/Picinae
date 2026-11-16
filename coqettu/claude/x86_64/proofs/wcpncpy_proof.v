(* wcpncpy -- copy a fixed-size wide string, returning a pointer to its end
   (musl x86_64, C), composed with wcsncpy (-> wmemset) and wcsnlen
   (-> wmemchr)

   SEMANTICS
   ---------
   musl's wcpncpy (src/string/wcpncpy.c) is

       return wcsncpy(d, s, n) + wcsnlen(s, n);

   The binary saves R12, RBP (= n) and RBX (= s), CALLs wcsncpy (0x134be0),
   keeps its result in R12 and CALLs wcsnlen (0x165fa5), returning
   R12 + 4 RAX.  Both callees are themselves compositions; their contracts
   (wcsncpy_proof.v, wcsnlen_proof.v) are used through call_leaf_ni.

   SPECIFICATION (man 3 wcpncpy, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     wchar_t *wcpncpy(wchar_t dest[restrict .n], const wchar_t src[restrict .n],
                      size_t n);
     wcpncpy is the wide-character equivalent of stpncpy: it copies at most
     n wide characters from src to dest, padding with L'\0' up to n wide
     characters, and returns a pointer to the last wide character written
     (the first L'\0' written, or dest + n).

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcpncpy at 0x65dfa, wcsncpy at 0x34be0, wcsnlen at 0x65fa5
            (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcpncpy_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, RSI = src, RDX = n; RSP = rsp; m = memory.
            Precondition (wcpncpy_ok): 4n < 2^63; 0 < src and
            src + 4n <= 2^64; the 4n bytes at d, the 4n bytes at src and the
            64 bytes below rsp (this function's and both callees' frames)
            are pairwise disjoint.
   Output:  At the RET (0x165e1f): there is K <= n such that the 32-bit words
            src[0..K) are nonzero and src[K] = 0 if K < n; RAX = d + 4K
            (mod 2^64); d[i] = src[i] for i < K and d[i] = 0 for K <= i < n;
            every byte outside the 4n bytes at d and the 64 bytes below rsp
            is unchanged.  RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcpncpy_amd64 CoqEtTu.programs.wcsncpy_amd64
               CoqEtTu.programs.wmemset_amd64 CoqEtTu.programs.wcsnlen_amd64
               CoqEtTu.programs.wmemchr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.wmemchr_proof CoqEtTu.proofs.wcsnlen_proof.
Require Import CoqEtTu.proofs.wmemset_proof CoqEtTu.proofs.wcsncpy_proof.
Open Scope N.

Definition wcpncpy_program : program :=
  updateall2 (updateall2 wcpncpy_amd64 wcsncpy_program) wcsnlen_program.

Theorem wcpncpy_welltyped: welltyped_prog x64typctx wcpncpy_amd64.
Proof. exact wcpncpy_amd64.welltyped. Qed.

Lemma wcpncpy_program_welltyped: welltyped_prog x64typctx wcpncpy_program.
Proof.
  intros s a. unfold wcpncpy_program, updateall2 at 1, updateall.
  destruct (wcsnlen_program s a) as [[sz q]|] eqn:SL.
    pose proof (wcsnlen_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
  unfold updateall2, updateall.
  destruct (wcsncpy_program s a) as [[sz q]|] eqn:SC.
    pose proof (wcsncpy_program_welltyped s a) as WT. rewrite SC in WT. exact WT.
  apply wcpncpy_welltyped.
Qed.

Lemma wcsncpy_in_prog: wcsncpy_amd64 ⊆2 wcsncpy_program.
Proof.
  intros s a insn SC. unfold wcsncpy_program, updateall2, updateall.
  destruct (wmemset_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold wcsncpy_amd64, wmemset_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma wcsnlen_in_prog: wcsnlen_amd64 ⊆2 wcsnlen_program.
Proof.
  intros s a insn SC. unfold wcsnlen_program, updateall2, updateall.
  destruct (wmemchr_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold wcsnlen_amd64, wmemchr_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma wcsncpy_in_wcpncpy: wcsncpy_program ⊆2 wcpncpy_program.
Proof.
  intros s a insn SL. unfold wcpncpy_program, updateall2, updateall.
  destruct (wcsnlen_program s a) eqn:SC.
  - exfalso. revert SC SL.
    unfold wcsnlen_program, wcsncpy_program, updateall2, updateall,
           wcsnlen_amd64, wmemchr_amd64, wcsncpy_amd64, wmemset_amd64.
    cbv beta.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  - rewrite SL. reflexivity.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition wcpncpy_ok (d s n rsp:N) :=
  ~ overlap 64 d (4*n) s (4*n) /\ ~ overlap 64 d (4*n) (rsp ⊖ 64) 64 /\
  ~ overlap 64 s (4*n) (rsp ⊖ 64) 64 /\ 4*n < 2^63 /\ 0 < s /\ s + 4*n <= 2^64.

Definition wcpncpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165e1f => true
  | _ => false end | _ => false end.

Definition wcpncpy_post (s0:store) (m d src n:N) (s:store) :=
  (exists K, K <= n /\ nzw m src K /\ (K < n -> m Ⓓ[src ⊕ 4*K] = 0) /\ s R_RAX = d ⊕ 4*K /\
     (forall i, i < K -> s V_MEM64 Ⓓ[d ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]) /\
     (forall i, K <= i < n -> s V_MEM64 Ⓓ[d ⊕ 4*i] = 0)) /\
  (forall b, ~ (msub 64 b d < 4*n) -> 64 <= msub 64 b (s0 R_RSP ⊖ 64) -> s V_MEM64 Ⓑ[b] = m Ⓑ[b]) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition cs3 (s0 s:store) :=
  s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

(* the memory after the three pushes *)
Definition mpush (s0:store) (m:N) :=
  m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX].

(* ---- address facts, each proved in an empty context ---- *)

Lemma sub64_16: forall x L rsp, ~ overlap 64 x L (rsp ⊖ 64) 64 -> ~ overlap 64 x L (rsp ⊖ 32 ⊖ 16) 16.
Proof.
  intros x L rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, (16 + j). split. exact I. split. lia.
  rewrite E. replace (rsp ⊖ 32 ⊖ 16) with ((rsp ⊖ 64 + 16) mod 2^64) by mlia.
  rewrite N.add_mod_idemp_l by discriminate. rewrite N.add_assoc. reflexivity.
Qed.

Lemma sub64_32: forall x L rsp, ~ overlap 64 x L (rsp ⊖ 64) 64 -> ~ overlap 64 x L (rsp ⊖ 32 ⊖ 32) 32.
Proof.
  intros x L rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. exact I. split. lia.
  rewrite E. f_equal. f_equal. mlia.
Qed.

Lemma word_byte64:
  forall x n rsp i a, ~ overlap 64 x (4*n) (rsp ⊖ 64) 64 -> i < n -> msub 64 a (x ⊕ 4*i) < 4 ->
  64 <= msub 64 a (rsp ⊖ 64) /\ msub 64 a x < 4*n.
Proof.
  intros x n rsp i a NOV I A. split.
  - destruct (N.le_gt_cases 64 (msub 64 a (rsp ⊖ 64))) as [H|H]. exact H. exfalso.
    apply NOV. exists (4*i + msub 64 a (x ⊕ 4*i)), (msub 64 a (rsp ⊖ 64)).
    split. lia. split. exact H. mlia.
  - mlia.
Qed.

Lemma push4_64:
  forall m rsp v1 v2 v3 v4 b, 64 <= msub 64 b (rsp ⊖ 64) ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 24 := v3] [Ⓠrsp ⊖ 32 := v4]) Ⓑ[b] = m Ⓑ[b].
Proof.
  intros m rsp v1 v2 v3 v4 b O.
  rewrite (stack_store_frame _ rsp 32 v4 b 64) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 24 v3 b 64) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 16 v2 b 64) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 8 v1 b 64) by (assumption || lia).
  reflexivity.
Qed.

Lemma push3_48:
  forall m rsp v1 v2 v3 b, 48 <= msub 64 b (rsp ⊖ 48) ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 24 := v3]) Ⓑ[b] = m Ⓑ[b].
Proof.
  intros m rsp v1 v2 v3 b O.
  rewrite (stack_store_frame _ rsp 24 v3 b 48) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 16 v2 b 48) by (assumption || lia).
  rewrite (stack_store_frame _ rsp 8 v1 b 48) by (assumption || lia).
  reflexivity.
Qed.

(* source words survive the pushes and the first CALL *)
Lemma src_word4:
  forall m rsp v1 v2 v3 v4 x n i, ~ overlap 64 x (4*n) (rsp ⊖ 64) 64 -> i < n ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 24 := v3] [Ⓠrsp ⊖ 32 := v4]) Ⓓ[x ⊕ 4*i] = m Ⓓ[x ⊕ 4*i].
Proof.
  intros m rsp v1 v2 v3 v4 x n i NOV I. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply push4_64.
  exact (proj1 (word_byte64 x n rsp i a NOV I A)).
Qed.

Lemma f48_16: forall b rsp, 48 <= msub 64 b (rsp ⊖ 48) -> 16 <= msub 64 b (rsp ⊖ 32 ⊖ 16).
Proof. intros. mlia. Qed.

Lemma f48_ra: forall b rsp, 48 <= msub 64 b (rsp ⊖ 48) -> ~ overlap 64 b 1 (rsp ⊖ 32) 8.
Proof. intros b rsp B [x [y [X [Y E]]]]. mlia. Qed.

Lemma f24_16: forall b rsp, msub 64 b (rsp ⊖ 24) < 24 -> 16 <= msub 64 b (rsp ⊖ 32 ⊖ 16).
Proof. intros. mlia. Qed.

Lemma f24_ra: forall b rsp, msub 64 b (rsp ⊖ 24) < 24 -> ~ overlap 64 b 1 (rsp ⊖ 32) 8.
Proof. intros b rsp B [x [y [X [Y E]]]]. mlia. Qed.

Lemma f64_48: forall b rsp, 64 <= msub 64 b (rsp ⊖ 64) -> 48 <= msub 64 b (rsp ⊖ 48).
Proof. intros. mlia. Qed.

Lemma f64_32: forall b rsp, 64 <= msub 64 b (rsp ⊖ 64) -> 32 <= msub 64 b (rsp ⊖ 32 ⊖ 32).
Proof. intros. mlia. Qed.

Lemma f64_ra: forall b rsp, 64 <= msub 64 b (rsp ⊖ 64) -> ~ overlap 64 b 1 (rsp ⊖ 32) 8.
Proof. intros b rsp B [x [y [X [Y E]]]]. mlia. Qed.

Lemma ra_word: forall b rsp, msub 64 b (rsp ⊖ 32) < 8 -> 32 <= msub 64 b (rsp ⊖ 32 ⊖ 32).
Proof. intros. mlia. Qed.

(* bytes of a saved-register slot: outside d and in the 24 pushed bytes *)
Lemma slot_byte:
  forall d n rsp j a, ~ overlap 64 d (4*n) (rsp ⊖ 64) 64 -> (j = 8 \/ j = 16 \/ j = 24) ->
  msub 64 a (rsp ⊖ j) < 8 ->
  ~ (msub 64 a d < 4*n) /\ msub 64 a (rsp ⊖ 24) < 24 /\ 32 <= msub 64 a (rsp ⊖ 32 ⊖ 32).
Proof.
  intros d n rsp j a NOV J A. split; [|split].
  - intro H. apply NOV. exists (msub 64 a d), (64 - j + msub 64 a (rsp ⊖ j)).
    split. exact H. split. destruct J as [J|[J|J]]; subst j; lia.
    destruct J as [J|[J|J]]; subst j; mlia.
  - destruct J as [J|[J|J]]; subst j; mlia.
  - destruct J as [J|[J|J]]; subst j; mlia.
Qed.

Lemma ra_slot:
  forall d n rsp a, ~ overlap 64 d (4*n) (rsp ⊖ 64) 64 -> msub 64 a (rsp ⊖ 32) < 8 ->
  ~ (msub 64 a d < 4*n) /\ 16 <= msub 64 a (rsp ⊖ 32 ⊖ 16).
Proof.
  intros d n rsp a NOV A. split.
  - intro H. apply NOV. exists (msub 64 a d), (32 + msub 64 a (rsp ⊖ 32)).
    split. exact H. split. lia. mlia.
  - mlia.
Qed.

Lemma src_not_dst:
  forall d s n i a, ~ overlap 64 d (4*n) s (4*n) -> i < n -> msub 64 a (s ⊕ 4*i) < 4 -> ~ (msub 64 a d < 4*n).
Proof.
  intros d s n i a NOV I A H. apply NOV. exists (msub 64 a d), (4*i + msub 64 a (s ⊕ 4*i)).
  split. exact H. split. lia. mlia.
Qed.

Lemma len_unique:
  forall m s n K K', K <= n -> nzw m s K -> (K = n \/ m Ⓓ[s ⊕ 4*K] = 0) ->
  K' <= n -> wabsent m s 0 K' -> (K' < n -> m Ⓓ[s ⊕ 4*K'] = 0) -> K = K'.
Proof.
  intros m s n K K' KN NZ KS KN' AB KZ. destruct (N.lt_trichotomy K K') as [H|[H|H]].
  - exfalso. destruct KS as [KS|KS]. lia. exact (AB K H KS).
  - exact H.
  - exfalso. exact (NZ K' H (KZ ltac:(lia))).
Qed.

Lemma qslot:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 32) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma mpush_rbx: forall s0 m, s0 R_RBX < 2^64 -> mpush s0 m Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX.
Proof. intros. unfold mpush. rewrite getmem_setmem by discriminate. apply N.mod_small. assumption. Qed.

Lemma mpush_rbp: forall s0 m, s0 R_RBP < 2^64 -> mpush s0 m Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP.
Proof.
  intros. unfold mpush. rewrite getmem_noverlap by exact (qslot _ 16 24 eq_refl).
  rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma mpush_r12: forall s0 m, s0 R_R12 < 2^64 -> mpush s0 m Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R12.
Proof.
  intros. unfold mpush. rewrite getmem_noverlap by exact (qslot _ 8 24 eq_refl).
  rewrite getmem_noverlap by exact (qslot _ 8 16 eq_refl).
  rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma dst_byte:
  forall d n rsp i a, ~ overlap 64 d (4*n) (rsp ⊖ 64) 64 -> i < n -> msub 64 a (d ⊕ 4*i) < 4 ->
  32 <= msub 64 a (rsp ⊖ 32 ⊖ 32) /\ ~ overlap 64 a 1 (rsp ⊖ 32) 8.
Proof.
  intros d n rsp i a NOV I A. destruct (word_byte64 d n rsp i a NOV I A) as [H _]. split.
  - exact (f64_32 a rsp H).
  - exact (f64_ra a rsp H).
Qed.

Lemma cs3_tac_lemma: forall s0 s, callee_saved_eq s0 s -> cs3 s0 s.
Proof. intros s0 s (_&_&_&A&B&C). repeat split; assumption. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Definition wcpncpy_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165dfa => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165e04 => Some (s V_MEM64 = mpush s0 m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RBP = n /\ s R_RBX = src /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165e12 => Some (exists K, K <= n /\ nzw m src K /\ (K = n \/ m Ⓓ[src ⊕ 4*K] = 0) /\
                      (forall i, i < K -> s V_MEM64 Ⓓ[d ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]) /\
                      (forall i, K <= i < n -> s V_MEM64 Ⓓ[d ⊕ 4*i] = 0) /\
                      (forall b, ~ (msub 64 b d < 4*n) -> 48 <= msub 64 b (s0 R_RSP ⊖ 48) ->
                                 s V_MEM64 Ⓑ[b] = m Ⓑ[b]) /\
                      (forall b, ~ (msub 64 b d < 4*n) -> msub 64 b (s0 R_RSP ⊖ 24) < 24 ->
                                 s V_MEM64 Ⓑ[b] = mpush s0 m Ⓑ[b]) /\
                      s R_RDI = src /\ s R_RSI = n /\ s R_R12 = d /\ s R_RBX = src /\ s R_RBP = n /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165e1f => Some (wcpncpy_post s0 m d src n s)
  | _ => None
  end | _ => None end.

Theorem wcpncpy_correct:
  forall prog s t s' x' m d src n
         (WCPNCPY: wcpncpy_amd64 ⊆2 prog) (WCSNCPY: wcsncpy_amd64 ⊆2 prog)
         (WMEMSET: wmemset_amd64 ⊆2 prog) (WCSNLEN: wcsnlen_amd64 ⊆2 prog)
         (WMEMCHR: wmemchr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165dfa, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (OK: wcpncpy_ok d src n (s R_RSP)),
  satisfies_all prog (wcpncpy_invs s m d src n) wcpncpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n WCPNCPY WCSNCPY WMEMSET WCSNLEN WMEMCHR ENTRY MDL MEM D S Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RDI 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcpncpy_program).
    unfold wcpncpy_program, wcsncpy_program, wcsnlen_program.
    repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcpncpy_invs.
    unfold wcpncpy_program, wcsncpy_program, wcsnlen_program, updateall2, updateall in NOCODE.
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
  eapply models_at_invariant; try eassumption. apply wcpncpy_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B DB SB. rename t1 into t.
  pose proof OK as (NDS & NDK & NSK & NB & S0 & SW).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP CS]]]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B2.
    split. reflexivity. split. exact D.
    conj_tac. unfold cs3. repeat split; rewrite ?update_frame by discriminate; assumption.
  - destruct PRE as [MEM [RDI [RSI [RDX [RBP [RBX [RSP CS]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcpncpy_program _ _ _ _ s2 nil _ s1 t MDL1 wcpncpy_program_welltyped).
    intro MDL2.
    set (M2 := mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := 1465865]) in *.
    assert (S2M: s2 V_MEM64 = M2) by (unfold s2; apply update_updated).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 32) by (unfold s2; rewrite update_frame by discriminate; apply update_updated).
    assert (SRCW: forall i, i < n -> M2 Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i])
      by (intros i I; unfold M2, mpush; exact (src_word4 m _ _ _ _ _ src n i NSK I)).
    eapply (call_leaf_ni wcpncpy_program wcsncpy_program _ _
              (wcsncpy_invs s2 (s2 V_MEM64) d src n) wcsncpy_exit).
    + apply wcsncpy_in_wcpncpy.
    + intros a s t' EXIT NOCODE. unfold wcsncpy_invs.
      unfold wcsncpy_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcsncpy_correct; first
        [ apply wcsncpy_in_prog | apply subset_updateall2 | assumption | reflexivity
        | (unfold s2; reg; assumption) | idtac ].
      rewrite S2R. split. exact NDS. split. apply sub64_16, NDK. split. apply sub64_16, NSK. exact NB.
    + intros a s t' NC. unfold wcpncpy_invs, wcpncpy_exit.
      unfold wcsncpy_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcsncpy_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wcsncpy_exit _) eqn:EX; [|destruct PRE].
      unfold wcsncpy_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcpncpy_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX [[K [KN [NZ [KS [CPY ZER]]]]] [FR [RSP' CS']]]].
      rewrite S2M in NZ, KS, CPY, FR. rewrite S2R in FR, RSP'.
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 32] = 1465865).
      { transitivity (M2 Ⓠ[s0 R_RSP ⊖ 32]).
        - apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
          destruct (ra_slot d n (s0 R_RSP) a NDK A) as [A1 A2]. exact (FR a A1 A2).
        - unfold M2. rewrite getmem_setmem by discriminate. reflexivity. }
      x64_step. rewrite RA. repeat x64_step.
      assert (RBXs: s' R_RBX = src) by (rewrite (proj1 CS'); unfold s2; reg; exact RBX).
      assert (RBPs: s' R_RBP = n) by (rewrite (proj1 (proj2 CS')); unfold s2; reg; exact RBP).
      exists K. split. exact KN.
      split. intros i I. rewrite <- SRCW by (clear - I KN; lia). apply NZ, I.
      split. destruct (N.eq_dec K n) as [E|NE]. left. exact E. right.
        destruct KS as [KS|KS]. contradiction. rewrite <- SRCW by (clear - KN NE; lia). exact KS.
      split. intros i I. rewrite CPY by exact I. apply SRCW. clear - I KN; lia.
      split. exact ZER.
      split. intros b B1 B2. rewrite (FR b B1 (f48_16 b _ B2)). unfold M2.
        rewrite getmem_noverlap by exact (f48_ra b _ B2). unfold mpush. apply push3_48. exact B2.
      split. intros b B1 B2. rewrite (FR b B1 (f24_16 b _ B2)). unfold M2.
        apply getmem_noverlap. exact (f24_ra b _ B2).
      split. exact RBXs. split. exact RBPs. split. reflexivity. split. exact RBXs. split. exact RBPs.
      split. reflexivity.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). destruct CS as (B3 & B4 & B5).
      unfold cs3. reg. rewrite C3, C4, C5. unfold s2. reg. repeat split; assumption.
  - destruct PRE as [K [KN [NZ [KS [CP [ZR [FR [FP [RDI [RSI [R12 [RBX [RBP [RSP CS]]]]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s3 := S) end.
    apply (models_after_steps wcpncpy_program _ _ _ _ s3 nil _ s1 t MDL1 wcpncpy_program_welltyped).
    intro MDL2.
    set (M3 := s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 1465879]) in *.
    assert (S3M: s3 V_MEM64 = M3) by (unfold s3; apply update_updated).
    assert (S3R: s3 R_RSP = s0 R_RSP ⊖ 32) by (unfold s3; rewrite update_frame by discriminate; apply update_updated).
    assert (SRC3: forall i, i < n -> M3 Ⓓ[src ⊕ 4*i] = m Ⓓ[src ⊕ 4*i]).
    { intros i I. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
      destruct (word_byte64 src n (s0 R_RSP) i a NSK I A) as [H64 _].
      unfold M3. rewrite getmem_noverlap by exact (f64_ra a _ H64).
      exact (FR a (src_not_dst d src n i a NDS I A) (f64_48 a _ H64)). }
    eapply (call_leaf_ni wcpncpy_program wcsnlen_program _ _
              (wcsnlen_invs s3 (s3 V_MEM64) src n) wcsnlen_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcsnlen_invs.
      unfold wcsnlen_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply wcsnlen_correct; first
        [ apply wcsnlen_in_prog | apply subset_updateall2 | assumption | reflexivity
        | (unfold s3; reg; assumption) | idtac ].
      rewrite S3R. split. exact S0. split. exact SW. split. exact NB. apply sub64_32, NSK.
    + intros a s t' NC. unfold wcpncpy_invs, wcpncpy_exit.
      unfold wcsnlen_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcsnlen_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wcsnlen_exit _) eqn:EX; [|destruct PRE].
      unfold wcsnlen_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcpncpy_program_welltyped).
      intro MDL3.
      destruct PRE as [[K' [KN' [ABS [KZ RAX]]]] [SF [RSP' CS']]].
      rewrite S3M in ABS, KZ, SF. rewrite S3R in SF, RSP'.
      assert (KE: K = K').
      { apply (len_unique m src n K K' KN NZ KS KN').
        - intros i I. rewrite <- SRC3 by (clear - I KN'; lia). apply ABS, I.
        - intro I. rewrite <- SRC3 by exact I. apply KZ, I. }
      subst K'.
      assert (SL: forall j, (j = 8 \/ j = 16 \/ j = 24) ->
                s' V_MEM64 Ⓠ[s0 R_RSP ⊖ j] = mpush s0 m Ⓠ[s0 R_RSP ⊖ j]).
      { intros j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
        destruct (slot_byte d n (s0 R_RSP) j a NDK J A) as [A1 [A2 A3]].
        rewrite (SF a A3). unfold M3. rewrite getmem_noverlap by exact (f24_ra a _ A2).
        exact (FP a A1 A2). }
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 32] = 1465879).
      { transitivity (M3 Ⓠ[s0 R_RSP ⊖ 32]).
        - apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
          exact (SF a (ra_word a _ A)).
        - unfold M3. rewrite getmem_setmem by discriminate. reflexivity. }
      x64_step. rewrite RA. repeat x64_step.
      rewrite ?(SL 24), ?(SL 16), ?(SL 8)
        by (first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]).
      rewrite ?mpush_rbx, ?mpush_rbp, ?mpush_r12 by assumption.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5).
      unfold s3 in C2, C3, C4, C5. rewrite !update_frame in C2, C3, C4, C5 by discriminate.
      split.
      { exists K. split. exact KN. split. exact NZ.
        split. intro I. destruct KS as [KS|KS]. subst K. exfalso. exact (N.lt_irrefl _ I). exact KS.
        split. rewrite C2, R12. match goal with H: _ = s' R_RAX |- _ => rewrite <- H end.
          rewrite N.mul_comm. reflexivity.
        split.
        - intros i I. transitivity (s1 V_MEM64 Ⓓ[d ⊕ 4*i]).
          + apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
            destruct (dst_byte d n _ i a NDK (N.lt_le_trans _ _ _ I KN) A) as [A1 A2].
            rewrite (SF a A1). unfold M3. apply getmem_noverlap, A2.
          + apply CP, I.
        - intros i [I1 I2]. transitivity (s1 V_MEM64 Ⓓ[d ⊕ 4*i]).
          + apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
            destruct (dst_byte d n _ i a NDK I2 A) as [A1 A2].
            rewrite (SF a A1). unfold M3. apply getmem_noverlap, A2.
          + apply ZR. split; assumption. }
      split.
      { intros b B1 B2. rewrite (SF b (f64_32 b _ B2)). unfold M3.
        rewrite getmem_noverlap by exact (f64_ra b _ B2). exact (FR b B1 (f64_48 b _ B2)). }
      split. apply N.mod_small. exact RB.
      destruct CS as (B3 & B4 & B5).
      unfold callee_saved_eq. reg. rewrite C3, C4, C5. repeat split; sassumption.
Qed.

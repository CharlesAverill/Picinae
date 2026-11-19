(* wcstok -- split a wide string into tokens (musl x86_64, C), composed with
   wcsspn (-> wcschr -> wcslen) and wcscspn (-> wcschr -> wcslen, wcslen)

   SEMANTICS
   ---------
   musl's wcstok (src/string/wcstok.c) is

       wchar_t *wcstok(wchar_t *restrict s, const wchar_t *restrict sep,
                       wchar_t **restrict p)
       {
           if (!s && !(s = *p)) return NULL;
           s += wcsspn(s, sep);
           if (!*s) return *p = 0;
           *p = s + wcscspn(s, sep);
           if ( **p) *( *p)++ = 0;
           else *p = 0;
           return s;
       }

   compiled with the two CALLs (wcsspn 0x165fec, wcscspn 0x165e5a) composed
   by call_leaf_ni (lib/x64_compose.v); both are cuts (0x166036, 0x16604b).

   SPECIFICATION (man 3 wcstok, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     wchar_t *wcstok(wchar_t *wcs, const wchar_t *delim, wchar_t **ptr);
     wcstok returns the next token of wcs (or, if wcs is NULL, of the string
     saved in *ptr): it skips leading characters in delim, the token extends
     to the next character in delim, which is overwritten with L'\0', and
     *ptr is updated to continue after it.  At the end of the string it
     returns NULL.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcstok at 0x66021, wcsspn at 0x65fec, wcscspn at 0x65e5a, wcschr
            at 0x3c310, wcslen at 0x3c380 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcstok_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = c (delimiters), RDX = p; RSP = rsp; m = memory.
            Let s1 = (s if s <> 0, else the pointer at p) (ts).
            Precondition (wcstok_ok): p's 8 bytes are outside the 96 bytes
            below rsp; if s1 <> 0, s1 and c are wide strings (4L < 2^63 for
            s1) that are C objects (nonzero, no wrap), whose words through
            the terminators are outside the 96 bytes below rsp, and s1's
            words are disjoint from p's 8 bytes (restrict).
   Output:  At the RET (0x16606f), wcstok_post:
            s1 = 0: RAX = 0, memory unchanged outside the 96 bytes below rsp.
            Else K1 is the length of the initial run of delimiters
            (spanpre; s1[K1] is 0 or not a delimiter) and
            - s1[K1] = 0: RAX = 0 and *p = 0;
            - else RAX = t = s1 + 4K1, K2 is the token length (cspre) and
              either t[K2] = 0 and *p = 0, or t[K2] is a delimiter, it is
              overwritten with 0 and *p = t + 4K2 + 4.
            All other bytes outside the 96 bytes below rsp are unchanged;
            RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcstok_amd64 CoqEtTu.programs.wcsspn_amd64 CoqEtTu.programs.wcscspn_amd64
               CoqEtTu.programs.wcschr_amd64 CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.wcslen_proof CoqEtTu.proofs.wcschr_proof CoqEtTu.proofs.wcsspn_proof
               CoqEtTu.proofs.wcscspn_proof CoqEtTu.proofs.wcspbrk_proof.
Open Scope N.

Definition wcstok_program : program :=
  updateall2 wcstok_amd64 (updateall2 wcsspn_amd64 wcscspn_program).

Theorem wcstok_welltyped: welltyped_prog x64typctx wcstok_amd64.
Proof. exact wcstok_amd64.welltyped. Qed.

Lemma wcstok_program_welltyped: welltyped_prog x64typctx wcstok_program.
Proof.
  intros s a. unfold wcstok_program, updateall2 at 1, updateall.
  destruct (updateall2 wcsspn_amd64 wcscspn_program s a) as [[sz q]|] eqn:SL.
  - unfold updateall2, updateall in SL. destruct (wcscspn_program s a) as [[sz' q']|] eqn:SL2.
    + inversion SL; subst. pose proof (wcscspn_program_welltyped s a) as WT. rewrite SL2 in WT. exact WT.
    + pose proof (wcsspn_welltyped s a) as WT. rewrite SL in WT. exact WT.
  - apply wcstok_welltyped.
Qed.

Lemma wcsspn_in_tok0: wcsspn_amd64 ⊆2 updateall2 wcsspn_amd64 wcscspn_program.
Proof.
  intros s a insn SC. unfold wcscspn_program, wcschr_program, updateall2, updateall.
  destruct (wcslen_amd64 s a) eqn:SL.
  - exfalso. revert SC SL. unfold wcsspn_amd64, wcslen_amd64.
    repeat first
    [ discriminate
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - destruct (wcschr_amd64 s a) eqn:SC2.
    + exfalso. revert SC SC2. unfold wcsspn_amd64, wcschr_amd64.
      repeat first
      [ discriminate
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + destruct (wcscspn_amd64 s a) eqn:SC3; [|exact SC].
      exfalso. revert SC SC3. unfold wcsspn_amd64, wcscspn_amd64.
      repeat first
      [ discriminate
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma wcscspn_in_tok: wcscspn_program ⊆2 wcstok_program.
Proof. intros s a insn H. unfold wcstok_program. apply subset_updateall2, subset_updateall2, H. Qed.

Lemma wcsspn_in_tok: wcsspn_program ⊆2 wcstok_program.
Proof.
  unfold wcsspn_program. apply updateall2_lub.
  - intros s a insn H. unfold wcstok_program. apply subset_updateall2, wcsspn_in_tok0, H.
  - intros s a insn H. apply wcscspn_in_tok. apply subset_updateall2, H.
Qed.

(* the string wcstok works on *)
Definition ts (m:memory) (s p:N) := if s =? 0 then m Ⓠ[p] else s.

Lemma ts_nz: forall m s p, s <> 0 -> ts m s p = s.
Proof. intros. unfold ts. apply N.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma ts_z: forall m p, ts m 0 p = m Ⓠ[p].
Proof. reflexivity. Qed.

Definition wcstok_ok (m s c p rsp:N) :=
  ~ overlap 64 p 8 (rsp ⊖ 96) 96 /\
  (ts m s p = 0 \/
   ((exists L, wnilfree m (ts m s p) L /\ m Ⓓ[ts m s p ⊕ 4*L] = 0 /\ 4*L < 2^63 /\
               ts m s p + 4*L + 4 <= 2^64 /\
               ~ overlap 64 (ts m s p) (4*L + 4) (rsp ⊖ 96) 96 /\ ~ overlap 64 p 8 (ts m s p) (4*L + 4)) /\
    (exists Lc, wnilfree m c Lc /\ m Ⓓ[c ⊕ 4*Lc] = 0 /\ 0 < c /\ c + 4*Lc + 4 <= 2^64 /\
                ~ overlap 64 c (4*Lc + 4) (rsp ⊖ 96) 96))).

(* every byte outside the frame and the written ranges is as in m *)
Definition oth1 (M m:memory) (rsp p:N) :=
  forall b, 96 <= msub 64 b (rsp ⊖ 96) -> 8 <= msub 64 b p -> M Ⓑ[b] = m Ⓑ[b].
Definition oth2 (M m:memory) (rsp p e:N) :=
  forall b, 96 <= msub 64 b (rsp ⊖ 96) -> 8 <= msub 64 b p -> 4 <= msub 64 b e -> M Ⓑ[b] = m Ⓑ[b].

Definition wcstok_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x16606f => true
  | _ => false end | _ => false end.

Definition wcstok_post (s0:store) (m s c p:N) (st:store) :=
  ((ts m s p = 0 /\ st R_RAX = 0 /\
    (forall b, 96 <= msub 64 b (s0 R_RSP ⊖ 96) -> st V_MEM64 Ⓑ[b] = m Ⓑ[b])) \/
   (exists K1, ts m s p <> 0 /\ spanpre m (ts m s p) c K1 /\
    ((m Ⓓ[ts m s p ⊕ 4*K1] = 0 /\ st R_RAX = 0 /\ st V_MEM64 Ⓠ[p] = 0 /\
      oth1 (st V_MEM64) m (s0 R_RSP) p) \/
     (m Ⓓ[ts m s p ⊕ 4*K1] <> 0 /\ notin m c (m Ⓓ[ts m s p ⊕ 4*K1]) /\
      st R_RAX = ts m s p ⊕ 4*K1 /\
      exists K2, cspre m (ts m s p ⊕ 4*K1) c K2 /\
       ((m Ⓓ[(ts m s p ⊕ 4*K1) ⊕ 4*K2] = 0 /\ st V_MEM64 Ⓠ[p] = 0 /\
         oth1 (st V_MEM64) m (s0 R_RSP) p) \/
        (m Ⓓ[(ts m s p ⊕ 4*K1) ⊕ 4*K2] <> 0 /\ inset m c (m Ⓓ[(ts m s p ⊕ 4*K1) ⊕ 4*K2]) /\
         st V_MEM64 Ⓓ[(ts m s p ⊕ 4*K1) ⊕ 4*K2] = 0 /\
         st V_MEM64 Ⓠ[p] = ((ts m s p ⊕ 4*K1) ⊕ 4*K2) ⊕ 4 /\
         oth2 (st V_MEM64) m (s0 R_RSP) p ((ts m s p ⊕ 4*K1) ⊕ 4*K2))))))) /\
  st R_RSP = s0 R_RSP /\ callee_saved_eq s0 st.

(* memory below the pushes: unchanged outside 96 bytes, saved registers *)
Definition frm96 (s0:store) (m M:memory) :=
  (forall b, 96 <= msub 64 b (s0 R_RSP ⊖ 96) -> M Ⓑ[b] = m Ⓑ[b]) /\
  M Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R12 /\ M Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\ M Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX.

Definition wcstok_invs (s0:store) (m s c p:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0x166021 => Some (st V_MEM64 = m /\ st R_RDI = s /\ st R_RSI = c /\ st R_RDX = p /\
                      st R_RSP = s0 R_RSP /\ callee_saved_eq s0 st)
  | 0x166036 => Some (ts m s p <> 0 /\ st V_MEM64 = mpush s0 m /\ st R_RDI = ts m s p /\ st R_RSI = c /\
                      st R_RBX = ts m s p /\ st R_RBP = c /\ st R_R12 = p /\
                      st R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 st)
  | 0x16604b => Some (exists K1, ts m s p <> 0 /\ spanpre m (ts m s p) c K1 /\
                      m Ⓓ[ts m s p ⊕ 4*K1] <> 0 /\ notin m c (m Ⓓ[ts m s p ⊕ 4*K1]) /\
                      frm96 s0 m (st V_MEM64) /\
                      st R_RDI = ts m s p ⊕ 4*K1 /\ st R_RSI = c /\ st R_RBX = ts m s p ⊕ 4*K1 /\
                      st R_RBP = c /\ st R_R12 = p /\ st R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 st)
  | 0x16606f => Some (wcstok_post s0 m s c p st)
  | _ => None
  end | _ => None end.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.
Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

(* ---- facts, each proved in an empty context ---- *)

Lemma frm96_init:
  forall s0 m, s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 -> frm96 s0 m (mpush s0 m).
Proof.
  intros s0 m B1 B2 B3. unfold mpush. split; [|split; [|split]].
  - intros b B.
    rewrite (stack_store_frame _ (s0 R_RSP) 24 _ b 96) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 96) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 96) by (assumption || lia).
    reflexivity.
  - rewrite getmem_noverlap by exact (qslot64 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma frm96_ra: forall s0 m M v, frm96 s0 m M -> frm96 s0 m (M [Ⓠs0 R_RSP ⊖ 32 := v]).
Proof.
  intros s0 m M v [F [S8 [S16 S24]]]. split; [|split; [|split]].
  - intros b B. rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 96) by (assumption || lia). apply F, B.
  - rewrite getmem_noverlap by exact (qslot64 _ 8 32 eq_refl). exact S8.
  - rewrite getmem_noverlap by exact (qslot64 _ 16 32 eq_refl). exact S16.
  - rewrite getmem_noverlap by exact (qslot64 _ 24 32 eq_refl). exact S24.
Qed.

Lemma f96_64: forall b rsp, 96 <= msub 64 b (rsp ⊖ 96) -> 64 <= msub 64 b (rsp ⊖ 32 ⊖ 64).
Proof. intros. mlia. Qed.

Lemma slot96: forall a rsp j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32) ->
  msub 64 a (rsp ⊖ j) < 8 -> 64 <= msub 64 a (rsp ⊖ 32 ⊖ 64).
Proof. intros a rsp j J A. destruct J as [J|[J|[J|J]]]; subst j; mlia. Qed.

Lemma frm96_after:
  forall s0 m M M', frm96 s0 m M -> stack_frame M M' (s0 R_RSP ⊖ 32) 64 -> frm96 s0 m M'.
Proof.
  intros s0 m M M' [F [S8 [S16 S24]]] SF. split; [|split; [|split]].
  - intros b B. rewrite (SF b (f96_64 b _ B)). apply F, B.
  - rewrite <- S8. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot96 a _ 8). left; reflexivity. exact A.
  - rewrite <- S16. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot96 a _ 16). right; left; reflexivity. exact A.
  - rewrite <- S24. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot96 a _ 24). right; right; left; reflexivity. exact A.
Qed.

Lemma ra_after96:
  forall M M' rsp v, stack_frame M M' (rsp ⊖ 32) 64 -> M Ⓠ[rsp ⊖ 32] = v -> M' Ⓠ[rsp ⊖ 32] = v.
Proof.
  intros M M' rsp v SF V. rewrite <- V. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply SF. apply (slot96 a _ 32). right; right; right; reflexivity. exact A.
Qed.

Lemma word_byte96:
  forall x n rsp i a, ~ overlap 64 x n (rsp ⊖ 96) 96 -> i + 4 <= n -> msub 64 a (x ⊕ i) < 4 ->
  96 <= msub 64 a (rsp ⊖ 96).
Proof.
  intros x n rsp i a NOV I A.
  destruct (N.le_gt_cases 96 (msub 64 a (rsp ⊖ 96))) as [H|H]. exact H. exfalso.
  apply NOV. exists (i + msub 64 a (x ⊕ i)), (msub 64 a (rsp ⊖ 96)).
  split. lia. split. exact H. mlia.
Qed.

Lemma frm96_word:
  forall s0 m M x n i, frm96 s0 m M -> ~ overlap 64 x n (s0 R_RSP ⊖ 96) 96 -> i + 4 <= n ->
  M Ⓓ[x ⊕ i] = m Ⓓ[x ⊕ i].
Proof.
  intros s0 m M x n i [F _] NOV I. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply F. exact (word_byte96 x n _ i a NOV I A).
Qed.

Lemma frm96_q:
  forall s0 m M p, frm96 s0 m M -> ~ overlap 64 p 8 (s0 R_RSP ⊖ 96) 96 -> M Ⓠ[p] = m Ⓠ[p].
Proof.
  intros s0 m M p [F _] NOV. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply F.
  destruct (N.le_gt_cases 96 (msub 64 a (s0 R_RSP ⊖ 96))) as [H|H]. exact H. exfalso.
  apply NOV. exists (msub 64 a p), (msub 64 a (s0 R_RSP ⊖ 96)). split. exact A. split. exact H. mlia.
Qed.

Lemma sub96_64: forall x L rsp, ~ overlap 64 x L (rsp ⊖ 96) 96 -> ~ overlap 64 x L (rsp ⊖ 32 ⊖ 64) 64.
Proof.
  intros x L rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. exact I. split. lia.
  rewrite E. f_equal. f_equal. mlia.
Qed.

Lemma noverlap_shift:
  forall a n X F k n', ~ overlap 64 a n X F -> k + n' <= n -> ~ overlap 64 (a ⊕ k) n' X F.
Proof.
  intros a n X F k n' NOV K [i [j [I [J E]]]]. apply NOV. exists (k + i), j.
  split. lia. split. exact J. rewrite <- E. mlia.
Qed.

Lemma wshift: forall x k i, (x ⊕ 4*k) ⊕ 4*i = x ⊕ 4*(k + i).
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia. Qed.

Lemma wshift_mul: forall x k i, (x ⊕ 4*k) ⊕ 4*i = x ⊕ (4*k + 4*i).
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia. Qed.

Lemma spanpre_agree:
  forall (M m:memory) p c K L Lc,
  (forall i, i <= L -> M Ⓓ[p ⊕ 4*i] = m Ⓓ[p ⊕ 4*i]) -> m Ⓓ[p ⊕ 4*L] = 0 ->
  (forall i, i <= Lc -> M Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i]) -> m Ⓓ[c ⊕ 4*Lc] = 0 ->
  spanpre M p c K -> K <= L /\ spanpre m p c K.
Proof.
  intros M m p c K L Lc AP ZP AC ZC SP.
  assert (KL: K <= L).
  { destruct (N.le_gt_cases K L) as [H|H]. exact H. exfalso. apply (proj1 (SP L H)).
    rewrite (AP L (N.le_refl L)). exact ZP. }
  split. exact KL. intros i I. destruct (SP i I) as [A B].
  rewrite <- (AP i) by (clear - I KL; lia). split. exact A.
  exact (inset_agree M m c _ Lc AC ZC B).
Qed.

Lemma oth_byte_q: forall (M:memory) p v b, 8 <= msub 64 b p -> (M [Ⓠp := v]) Ⓑ[b] = M Ⓑ[b].
Proof. intros. apply getmem_noverlap. intros [x [y [X [Y E]]]]. mlia. Qed.

Lemma oth_byte_d: forall (M:memory) e v b, 4 <= msub 64 b e -> (M [Ⓓe := v]) Ⓑ[b] = M Ⓑ[b].
Proof. intros. apply getmem_noverlap. intros [x [y [X [Y E]]]]. mlia. Qed.

Lemma slot_q: forall (M:memory) p v rsp j, ~ overlap 64 p 8 (rsp ⊖ 96) 96 ->
  (j = 8 \/ j = 16 \/ j = 24) -> (M [Ⓠp := v]) Ⓠ[rsp ⊖ j] = M Ⓠ[rsp ⊖ j].
Proof.
  intros M p v rsp j POV J. apply getmem_noverlap. intros [x [y [X [Y E]]]]. apply POV.
  exists y, (96 - j + x). split. exact Y. split. destruct J as [J|[J|J]]; subst j; lia.
  destruct J as [J|[J|J]]; subst j; mlia.
Qed.

Lemma slot_d: forall (M:memory) a v rsp j, ~ overlap 64 a 4 (rsp ⊖ 96) 96 ->
  (j = 8 \/ j = 16 \/ j = 24) -> (M [Ⓓa := v]) Ⓠ[rsp ⊖ j] = M Ⓠ[rsp ⊖ j].
Proof.
  intros M a v rsp j AOV J. apply getmem_noverlap. intros [x [y [X [Y E]]]]. apply AOV.
  exists y, (96 - j + x). split. exact Y. split. destruct J as [J|[J|J]]; subst j; lia.
  destruct J as [J|[J|J]]; subst j; mlia.
Qed.

Lemma nov_pe: forall p x n i, ~ overlap 64 p 8 x n -> i + 4 <= n -> ~ overlap 64 (x ⊕ i) 4 p 8.
Proof.
  intros p x n i H I [a [bb [A [B E]]]]. apply H. exists bb, (i + a). split. exact B. split. lia. mlia.
Qed.

Lemma ex_d: forall (M:memory) b k, (M [Ⓓb + k*4 := 0]) Ⓓ[b ⊕ 4*k] = 0.
Proof. intros. rewrite getmem_mod_l, (N.mul_comm 4 k), getmem_setmem by discriminate. reflexivity. Qed.

Lemma qv: forall b k, (4 + b + k*4) mod 2^64 = (b ⊕ 4*k) ⊕ 4.
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia. Qed.

Lemma oth_byte_d': forall (M:memory) x k v b0, 4 <= msub 64 b0 (x ⊕ 4*k) -> (M [Ⓓx + k*4 := v]) Ⓑ[b0] = M Ⓑ[b0].
Proof. intros. apply getmem_noverlap. intros [x' [y [X [Y E]]]]. mlia. Qed.

Lemma eov: forall t k1 k2 L rsp, ~ overlap 64 t (4*L + 4) (rsp ⊖ 96) 96 -> k1 + k2 <= L ->
  ~ overlap 64 (t ⊕ 4*k1 + k2*4) 4 (rsp ⊖ 96) 96.
Proof.
  intros t k1 k2 L rsp OV K [x [y [X [Y E]]]].
  apply (noverlap_shift _ (4*L + 4) _ _ (4*(k1 + k2)) 4 OV ltac:(lia)). exists x, y.
  split. exact X. split. exact Y. rewrite <- E. clear - K. mlia.
Qed.

Lemma wcsspn_in_sp: wcsspn_amd64 ⊆2 wcsspn_program.
Proof.
  intros s a insn SC. unfold wcsspn_program, wcschr_program, updateall2, updateall.
  destruct (wcslen_amd64 s a) eqn:SL.
  - exfalso. revert SC SL. unfold wcsspn_amd64, wcslen_amd64.
    repeat first
    [ discriminate
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - destruct (wcschr_amd64 s a) eqn:SC2; [|exact SC].
    exfalso. revert SC SC2. unfold wcsspn_amd64, wcschr_amd64.
    repeat first
    [ discriminate
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma wcschr_in_sp: wcschr_amd64 ⊆2 wcsspn_program.
Proof. intros s a insn H. apply subset_updateall2. apply wcschr_in_prog, H. Qed.

Lemma wcslen_in_sp: wcslen_amd64 ⊆2 wcsspn_program.
Proof. intros s a insn H. apply subset_updateall2. unfold wcschr_program. apply subset_updateall2, H. Qed.

Theorem wcstok_correct:
  forall prog s t s' x' m w c p
         (WCSTOK: wcstok_amd64 ⊆2 prog) (WCSSPN: wcsspn_amd64 ⊆2 prog) (WCSCSPN: wcscspn_amd64 ⊆2 prog)
         (WCSCHR: wcschr_amd64 ⊆2 prog) (WCSLEN: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x166021, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (W: s R_RDI = w) (C: s R_RSI = c) (P: s R_RDX = p)
         (OK: wcstok_ok m w c p (s R_RSP)),
  satisfies_all prog (wcstok_invs s m w c p) wcstok_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m w c p WCSTOK WCSSPN WCSCSPN WCSCHR WCSLEN ENTRY MDL MEM W C P OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDX 64); reflexivity).
  assert (CB: c < 2^64) by (rewrite <- C; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcstok_program).
    unfold wcstok_program, wcscspn_program, wcschr_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcstok_invs.
    unfold wcstok_program, wcscspn_program, wcschr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m w c p MDL MEM W C P OK RB RBXB RBPB R12B PB CB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcstok_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B PB CB. rename t1 into t.
  destruct OK as [POV OKs].
  pose proof (frm96_init s0 m R12B RBPB RBXB) as FR0.
  assert (MQ: mpush s0 m Ⓠ[p] = m Ⓠ[p]) by exact (frm96_q _ _ _ p FR0 POV).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [Wd [C [P [RSP CS]]]]].
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5).
    repeat x64_step.
    all: rewrite ?B0, ?B1, ?B2 in *; fold (mpush s0 m) in *; rewrite ?MQ in *.
    + match goal with BC: (w =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into W0 end.
      match goal with BC: (m Ⓠ[p] =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into Q0 end.
      split. left. split. rewrite W0, ts_z. exact Q0. split. reflexivity. exact (proj1 FR0).
      split. apply N.mod_small, RB.
      unfold callee_saved_eq; repeat split; reg; first [sassumption | (apply N.mod_small; assumption)].
    + match goal with BC: (w =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into W0 end.
      match goal with BC: (m Ⓠ[p] =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into Q0 end.
      rewrite W0, ts_z. conj_tac. unfold cs3; repeat split; reg; sassumption.
    + match goal with BC: (w =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into W0 end.
      rewrite (ts_nz m w p W0). conj_tac. unfold cs3; repeat split; reg; sassumption.
  - (* call wcsspn *)
    destruct PRE as [TNZ [MEM [RDI [RSI [RBX [RBP [R12 [RSP CS]]]]]]]].
    destruct OKs as [TZ|[(L & NL & ZL & LB & TW & OVs & OVp) (Lc & NLc & ZLc & C0 & CW & OVc)]]; [contradiction|].
    pose proof FR0 as FR. rewrite <- MEM in FR. clear MEM.
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcstok_program _ _ _ _ s2 nil _ s1 t MDL1 wcstok_program_welltyped).
    intro MDL2.
    pose proof (frm96_ra _ _ _ 0x16603b FR) as FR2.
    assert (S2M: s2 V_MEM64 = s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x16603b]) by (unfold s2; reg; sreflexivity).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 32) by (unfold s2; reg; reflexivity).
    assert (AGs: forall i, i <= L -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x16603b]) Ⓓ[ts m w p ⊕ 4*i] = m Ⓓ[ts m w p ⊕ 4*i])
      by (intros i I; apply (frm96_word _ _ _ _ (4*L + 4) _ FR2 OVs); clear - I; lia).
    assert (AGc: forall i, i <= Lc -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x16603b]) Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i])
      by (intros i I; apply (frm96_word _ _ _ _ (4*Lc + 4) _ FR2 OVc); clear - I; lia).
    eapply (call_leaf_ni wcstok_program wcsspn_program _ _ (wcsspn_invs s2 (s2 V_MEM64) (ts m w p) c) wcsspn_exit).
    + exact wcsspn_in_tok.
    + intros a s t' EXIT NOCODE. unfold wcsspn_invs.
      unfold wcsspn_program, wcschr_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s''] START. apply wcsspn_correct; first
        [ apply wcsspn_in_sp | apply wcschr_in_sp | apply wcslen_in_sp | reflexivity | assumption
        | (unfold s2; reg; first [reflexivity | assumption]) | idtac ].
      rewrite S2M, S2R. split.
      * exists L. split. exact (wnilfree_agree _ m _ L AGs NL).
        split. rewrite (AGs L (N.le_refl L)). exact ZL.
        split. exact LB. apply sub96_64, OVs.
      * exists Lc. split. exact (wnilfree_agree _ m c Lc AGc NLc).
        split. rewrite (AGc Lc (N.le_refl Lc)). exact ZLc.
        split. exact C0. split. exact CW. apply sub96_64, OVc.
    + intros a s t' NC. unfold wcstok_invs, wcstok_exit.
      unfold wcsspn_program, wcschr_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcsspn_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wcsspn_exit _) eqn:EX; [|destruct PRE].
      unfold wcsspn_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcstok_program_welltyped).
      intro MDL3.
      destruct PRE as [[K [SP [RES RAXK]]] [SF [RSP' CS']]].
      rewrite S2M in SP, RES, SF. rewrite S2R in SF, RSP'.
      destruct (spanpre_agree _ m _ c K L Lc AGs ZL AGc ZLc SP) as [KL SPm].
      rewrite (AGs K KL) in RES.
      pose proof (frm96_after _ _ _ _ FR2 SF) as FR3.
      pose proof (ra_after96 _ _ _ _ SF ltac:(rewrite getmem_setmem by discriminate; reflexivity)) as RA.
      assert (WK: s' V_MEM64 Ⓓ[ts m w p ⊕ 4*K] = m Ⓓ[ts m w p ⊕ 4*K])
        by (apply (frm96_word _ _ _ _ (4*L + 4) _ FR3 OVs); clear - KL; lia).
      destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
      unfold s2 in D0, D1, D2, D3, D4, D5.
      rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
      x64_step. rewrite RA. repeat x64_step.
      all: rewrite ?RBX, ?R12, ?RBP in *.
      all: assert (WK': s' V_MEM64 Ⓓ[ts m w p + K*4] = m Ⓓ[ts m w p ⊕ 4*K])
             by (rewrite (N.mul_comm K 4), <- (dword_load_off (s' V_MEM64) _ (4*K)); exact WK).
      all: match goal with BC: (_ =? 0) = _ |- _ => rewrite WK' in BC end.
      all: pose proof CS as (B3 & B4 & B5).
      * match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into Z end.
        split. right. exists K. split. exact TNZ. split. exact SPm. left.
          split. exact Z. split. reflexivity.
          split. rewrite getmem_setmem by discriminate. reflexivity.
          intros b BB1 BB2. rewrite oth_byte_q by exact BB2. exact (proj1 FR3 b BB1).
        split. apply N.mod_small, RB.
        pose proof FR3 as [_ [T8 [T16 T24]]].
        unfold callee_saved_eq; repeat split; reg;
          rewrite ?(slot_q _ p 0 _ _ POV) by (clear; lia);
          first [sassumption | (rewrite ?D3, ?D4, ?D5; sassumption)].
      * match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into NZ end.
        destruct RES as [Z|NI]; [contradiction|].
        exists K. split. exact TNZ. split. exact SPm. split. exact NZ.
        split. exact (notin_agree _ m c _ Lc AGc ZLc NI).
        split. exact FR3.
        split. rewrite (N.mul_comm K 4). reflexivity.
        split. reflexivity.
        split. rewrite (N.mul_comm K 4). reflexivity.
        split. reflexivity.
        split. rewrite D2; reg; first [reflexivity | exact R12].
        split. reflexivity.
        unfold cs3; repeat split; reg; rewrite ?D3, ?D4, ?D5; sassumption.
  - (* call wcscspn *)
    destruct PRE as [K1 [TNZ [SPm1 [NZ1 [NI1 [FR [RDI [RSI [RBX [RBP [R12 [RSP CS]]]]]]]]]]]].
    destruct OKs as [TZ|[(L & NL & ZL & LB & TW & OVs & OVp) (Lc & NLc & ZLc & C0 & CW & OVc)]]; [contradiction|].
    assert (KL1: K1 <= L) by exact (spanpre_len m _ c K1 L SPm1 ZL).
    assert (BW: ts m w p ⊕ 4*K1 = ts m w p + 4*K1) by (apply N.mod_small; clear - KL1 TW; lia).
    assert (NLb: wnilfree m (ts m w p ⊕ 4*K1) (L - K1))
      by (intros i I; rewrite wshift; apply NL; clear - I KL1; lia).
    assert (ZLb: m Ⓓ[(ts m w p ⊕ 4*K1) ⊕ 4*(L - K1)] = 0)
      by (rewrite wshift; replace (K1 + (L - K1)) with L by (clear - KL1; lia); exact ZL).
    assert (OVb: ~ overlap 64 (ts m w p ⊕ 4*K1) (4*(L - K1) + 4) (s0 R_RSP ⊖ 96) 96)
      by (apply (noverlap_shift _ (4*L + 4)); [exact OVs | clear - KL1; lia]).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps wcstok_program _ _ _ _ s2 nil _ s1 t MDL1 wcstok_program_welltyped).
    intro MDL2.
    pose proof (frm96_ra _ _ _ 0x166050 FR) as FR2.
    assert (S2M: s2 V_MEM64 = s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x166050]) by (unfold s2; reg; sreflexivity).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 32) by (unfold s2; reg; reflexivity).
    assert (AGb: forall i, i <= L - K1 -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x166050]) Ⓓ[(ts m w p ⊕ 4*K1) ⊕ 4*i] =
                                         m Ⓓ[(ts m w p ⊕ 4*K1) ⊕ 4*i])
      by (intros i I; rewrite wshift; apply (frm96_word _ _ _ _ (4*L + 4) _ FR2 OVs); clear - I KL1; lia).
    assert (AGc: forall i, i <= Lc -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x166050]) Ⓓ[c ⊕ 4*i] = m Ⓓ[c ⊕ 4*i])
      by (intros i I; apply (frm96_word _ _ _ _ (4*Lc + 4) _ FR2 OVc); clear - I; lia).
    eapply (call_leaf_ni wcstok_program wcscspn_program _ _
              (wcscspn_invs s2 (s2 V_MEM64) (ts m w p ⊕ 4*K1) c) (wcscspn_exit s2)).
    + exact wcscspn_in_tok.
    + intros a s t' EXIT NOCODE. unfold wcscspn_invs.
      unfold wcscspn_program, wcschr_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s''] START. apply wcscspn_correct; first
        [ apply wcscspn_in_prog | apply wcschr_in_cspn | apply wcslen_in_cspn | reflexivity | assumption
        | (unfold s2; reg; first [reflexivity | assumption]) | idtac ].
      rewrite S2M, S2R. split.
      * exists (L - K1). split. exact (wnilfree_agree _ m _ _ AGb NLb).
        split. rewrite (AGb (L - K1) (N.le_refl _)). exact ZLb.
        split. clear - LB; lia. split. rewrite BW. clear - TNZ; lia.
        split. rewrite BW. clear - KL1 TW; lia. apply sub96_64, OVb.
      * exists Lc. split. exact (wnilfree_agree _ m c Lc AGc NLc).
        split. rewrite (AGc Lc (N.le_refl Lc)). exact ZLc.
        split. exact C0. split. exact CW. apply sub96_64, OVc.
    + intros a s t' NC. unfold wcstok_invs, wcstok_exit.
      unfold wcscspn_program, wcschr_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcscspn_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (wcscspn_exit _ _) eqn:EX; [|destruct PRE].
      unfold wcscspn_exit in EX. addr_cases EX.
      all: set (bb := ts m w p ⊕ 4*K1) in PRE.
      all: simpl in PRE.
      all: match goal with H: context [wcscspn_post] |- _ => rename H into PR0 end.
      all: unfold bb in PR0; clear bb.
      all: try (rewrite EX in PR0; cbv beta iota in PR0).
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 wcstok_program_welltyped).
      all: intro MDL3.
      all: destruct PR0 as [[K2 [SP2 [RES2 RAX2]]] [SF [RSP' CS']]].
      all: rewrite S2M in SP2, RES2, SF. all: rewrite S2R in SF, RSP'.
      all: destruct (cspre_agree _ m _ c K2 (L - K1) Lc AGb ZLb AGc ZLc SP2) as [K2L SPm2].
      all: rewrite (AGb K2 K2L) in RES2.
      all: pose proof (frm96_after _ _ _ _ FR2 SF) as FR3.
      all: pose proof (ra_after96 _ _ _ _ SF ltac:(rewrite getmem_setmem by discriminate; reflexivity)) as RA.
      all: assert (WK: s' V_MEM64 Ⓓ[(ts m w p ⊕ 4*K1) ⊕ 4*K2] = m Ⓓ[(ts m w p ⊕ 4*K1) ⊕ 4*K2])
             by (rewrite wshift; apply (frm96_word _ _ _ _ (4*L + 4) _ FR3 OVs); clear - K2L KL1; lia).
      all: destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
      all: unfold s2 in D0, D1, D2, D3, D4, D5.
      all: rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
      all: x64_step; rewrite RA; repeat x64_step.
      all: rewrite ?RBX, ?R12, ?RBP in *.
      all: assert (WK': s' V_MEM64 Ⓓ[ts m w p ⊕ 4*K1 + K2*4] = m Ⓓ[(ts m w p ⊕ 4*K1) ⊕ 4*K2])
             by (rewrite (N.mul_comm K2 4), <- (dword_load_off (s' V_MEM64) _ (4*K2)); exact WK).
      all: match goal with BC: (_ =? 0) = _ |- _ => rewrite WK' in BC end.
      all: pose proof CS as (B3 & B4 & B5).
      all: pose proof FR3 as [_ [T8 [T16 T24]]].
      all: assert (EOV: ~ overlap 64 (ts m w p ⊕ 4*K1 + K2*4) 4 (s0 R_RSP ⊖ 96) 96)
             by (apply (eov _ _ _ L); [exact OVs | clear - K2L KL1; lia]).
      all: match goal with
           | BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into Z2;
               split; [right; exists K1; split; [exact TNZ |]; split; [exact SPm1 |]; right;
                 split; [exact NZ1 |]; split; [exact NI1 |]; split; [reflexivity |];
                 exists K2; split; [exact SPm2 |]; left;
                 split; [exact Z2 |];
                 split; [rewrite getmem_setmem by discriminate; reflexivity |];
                 intros b0 BB1 BB2; rewrite oth_byte_q by exact BB2; exact (proj1 FR3 b0 BB1) |]
           | BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into NZ2;
               destruct RES2 as [Z|IS]; [contradiction |];
               split; [right; exists K1; split; [exact TNZ |]; split; [exact SPm1 |]; right;
                 split; [exact NZ1 |]; split; [exact NI1 |]; split; [reflexivity |];
                 exists K2; split; [exact SPm2 |]; right;
                 split; [exact NZ2 |];
                 split; [exact (inset_agree _ m c _ Lc AGc ZLc IS) |];
                 split; [rewrite getmem_noverlap by (rewrite wshift; apply (nov_pe _ _ (4*L + 4));
                                                     [exact OVp | clear - K2L KL1; lia]);
                         apply ex_d |];
                 split; [rewrite getmem_setmem by discriminate; apply qv |];
                 intros b0 BB1 BB2 BB3; rewrite oth_byte_q by exact BB2;
                 rewrite oth_byte_d' by exact BB3; exact (proj1 FR3 b0 BB1) |]
           end.
      all: split; [apply N.mod_small, RB |].
      all: unfold callee_saved_eq; repeat split; reg;
             rewrite ?(slot_q _ p _ _ _ POV) by (clear; lia);
             rewrite ?(slot_d _ _ _ _ _ EOV) by (clear; lia);
             first [sassumption | (rewrite ?D3, ?D4, ?D5; sassumption)].
Qed.

(* strxfrm_l -- transform a string for collation (musl x86_64, C),
   composed with strlen and strcpy (-> stpcpy)

   SEMANTICS
   ---------
   musl's __strxfrm_l (src/locale/strxfrm.c), exported as strxfrm_l, is

       size_t __strxfrm_l(char *restrict dest, const char *restrict src,
                          size_t n, locale_t loc)
       {
           size_t l = strlen(src);
           if (n > l) strcpy(dest, src);
           return l;
       }

   The binary saves R14 (= dest), RBP (= n) and RBX (= src), CALLs strlen
   (0x1348c0), and if l < n spills l and CALLs strcpy (0x1659c7).  Both
   contracts (strlen_proof.v, strcpy_proof.v) are used through call_leaf_ni.

   SPECIFICATION (man 3 strxfrm, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     size_t strxfrm_l(char dest[restrict .n], const char src[restrict .n],
                      size_t n, locale_t locale);
     strxfrm transforms src so that strcmp on transformed strings agrees
     with strcoll, and places at most n bytes of the result in dest.  It
     returns the length of the transformed string (excluding the NUL); if
     that is >= n, dest is indeterminate.  (musl's transformation is the
     identity.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            __strxfrm_l (strxfrm_l) at 0x462ed, strlen at 0x348c0, strcpy at
            0x659c7 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strxfrm_l_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dest, RSI = src, RDX = n (RCX = locale, ignored); RSP = rsp;
            m = memory.  Precondition (xfrm_ok): src is a string of length L
            whose L+1 bytes do not overlap the 64 bytes below rsp; if L < n,
            the L+1 bytes at dest do not overlap src's (nov) nor the 64 bytes
            below rsp.
   Output:  At the RET (0x146319): RAX = L; if L < n then dest[i] = src[i]
            for i <= L; every byte outside (if L < n) the L+1 bytes at dest
            and outside the 64 bytes below rsp is unchanged.  RSP = rsp; RBX,
            RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strxfrm_l_amd64 CoqEtTu.programs.strlen_amd64
               CoqEtTu.programs.strcpy_amd64 CoqEtTu.programs.stpcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_memcpy_sets.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.stpcpy_proof CoqEtTu.proofs.strcpy_proof.
Open Scope N.

Definition strxfrm_l_program : program :=
  updateall2 (updateall2 strxfrm_l_amd64 strlen_amd64) strcpy_program.

Theorem strxfrm_l_welltyped: welltyped_prog x64typctx strxfrm_l_amd64.
Proof. exact strxfrm_l_amd64.welltyped. Qed.

Lemma strxfrm_l_program_welltyped: welltyped_prog x64typctx strxfrm_l_program.
Proof.
  intros s a. unfold strxfrm_l_program, updateall2 at 1, updateall.
  destruct (strcpy_program s a) as [[sz q]|] eqn:SC.
    pose proof (strcpy_program_welltyped s a) as WT. rewrite SC in WT. exact WT.
  unfold updateall2, updateall.
  destruct (strlen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (strlen_welltyped s a) as WT. rewrite SL in WT. exact WT.
  apply strxfrm_l_welltyped.
Qed.

Lemma strcpy_in_prog: strcpy_amd64 ⊆2 strcpy_program.
Proof.
  intros s a insn SC. unfold strcpy_program, updateall2, updateall.
  destruct (stpcpy_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold strcpy_amd64, stpcpy_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma strlen_in_xfrm: strlen_amd64 ⊆2 strxfrm_l_program.
Proof.
  intros s a insn SL. unfold strxfrm_l_program, updateall2 at 1, updateall.
  destruct (strcpy_program s a) eqn:SC.
  - exfalso. revert SC SL. unfold strcpy_program, updateall2, updateall, strcpy_amd64, stpcpy_amd64, strlen_amd64.
    cbv beta.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  - unfold updateall2, updateall. rewrite SL. reflexivity.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition xfrm_ok (m d s n rsp:N) :=
  exists L, nilfree m s L /\ m Ⓑ[s ⊕ L] = 0 /\ ~ overlap 64 s (L + 1) (rsp ⊖ 64) 64 /\
    (L < n -> nov d s (L + 1) /\ ~ overlap 64 d (L + 1) (rsp ⊖ 64) 64).

Definition strxfrm_l_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x146319 => true
  | _ => false end | _ => false end.

Definition strxfrm_l_post (s0:store) (m d src n:N) (s:store) :=
  (exists L, nilfree m src L /\ m Ⓑ[src ⊕ L] = 0 /\ s R_RAX = L /\
     (L < n -> forall i, i < L + 1 -> s V_MEM64 Ⓑ[d ⊕ i] = m Ⓑ[src ⊕ i]) /\
     (forall b, (L < n -> ~ (msub 64 b d < L + 1)) -> 64 <= msub 64 b (s0 R_RSP ⊖ 64) ->
                s V_MEM64 Ⓑ[b] = m Ⓑ[b])) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition cs3 (s0 s:store) := s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\ s R_R15 = s0 R_R15.

Definition mpush (s0:store) (m:N) :=
  m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R14] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX].

Definition strxfrm_l_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1462ed => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x146301 => Some (s V_MEM64 = mpush s0 m /\ s R_RDI = src /\ s R_R14 = d /\ s R_RBP = n /\
                      s R_RBX = src /\ s R_RSP = s0 R_RSP ⊖ 40 /\ cs3 s0 s)
  | 0x146325 => Some (exists L, nilfree m src L /\ m Ⓑ[src ⊕ L] = 0 /\ L < n /\
                      s V_MEM64 = mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := 0x146306] [Ⓠs0 R_RSP ⊖ 32 := L] /\
                      s R_RDI = d /\ s R_RSI = src /\ s R_RSP = s0 R_RSP ⊖ 40 /\
                      s R_R14 = d /\ s R_RBP = n /\ s R_RBX = src /\ cs3 s0 s)
  | 0x146319 => Some (strxfrm_l_post s0 m d src n s)
  | _ => None
  end | _ => None end.

(* ---- address facts, each proved in an empty context ---- *)

Lemma qslot64:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 64) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma outside64:
  forall x n rsp i, ~ overlap 64 x n (rsp ⊖ 64) 64 -> i < n -> 64 <= msub 64 (x ⊕ i) (rsp ⊖ 64).
Proof.
  intros x n rsp i NOV I. assert (BB: rsp ⊖ 64 < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ 64) in *. clearbody b.
  destruct (N.le_gt_cases 64 (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D. mlia.
Qed.

(* the stack stores (three pushes, two return addresses, the spill) *)
Lemma stores_frame:
  forall m rsp v1 v2 v3 v4 v5 b, 64 <= msub 64 b (rsp ⊖ 64) ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 24 := v3] [Ⓠrsp ⊖ 48 := v4] [Ⓠrsp ⊖ 32 := v5]) Ⓑ[b] = m Ⓑ[b]
  /\ (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 24 := v3] [Ⓠrsp ⊖ 48 := v4]) Ⓑ[b] = m Ⓑ[b].
Proof.
  intros m rsp v1 v2 v3 v4 v5 b O. split.
  - rewrite (stack_store_frame _ rsp 32 v5 b 64) by (assumption || lia).
    rewrite (stack_store_frame _ rsp 48 v4 b 64) by (assumption || lia).
    rewrite (stack_store_frame _ rsp 24 v3 b 64) by (assumption || lia).
    rewrite (stack_store_frame _ rsp 16 v2 b 64) by (assumption || lia).
    rewrite (stack_store_frame _ rsp 8 v1 b 64) by (assumption || lia).
    reflexivity.
  - rewrite (stack_store_frame _ rsp 48 v4 b 64) by (assumption || lia).
    rewrite (stack_store_frame _ rsp 24 v3 b 64) by (assumption || lia).
    rewrite (stack_store_frame _ rsp 16 v2 b 64) by (assumption || lia).
    rewrite (stack_store_frame _ rsp 8 v1 b 64) by (assumption || lia).
    reflexivity.
Qed.

Lemma sub64_16: forall x L rsp, ~ overlap 64 x L (rsp ⊖ 64) 64 -> ~ overlap 64 x L (rsp ⊖ 48 ⊖ 16) 16.
Proof.
  intros x L rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. exact I. split. lia.
  rewrite E. f_equal. f_equal. mlia.
Qed.

(* bytes of the saved-register slots, the spill and the first return address
   lie outside dest and above strcpy's 16-byte frame *)
Lemma slot_ok:
  forall d L rsp j a, ~ overlap 64 d (L + 1) (rsp ⊖ 64) 64 ->
  (j = 8 \/ j = 16 \/ j = 24 \/ j = 32 \/ j = 48) -> msub 64 a (rsp ⊖ j) < 8 ->
  ~ (msub 64 a d < L + 1) /\ 16 <= msub 64 a (rsp ⊖ 48 ⊖ 16).
Proof.
  intros d L rsp j a NOV J A. split.
  - intro H. apply NOV. exists (msub 64 a d), (64 - j + msub 64 a (rsp ⊖ j)).
    split. exact H. split. destruct J as [J|[J|[J|[J|J]]]]; subst j; lia.
    destruct J as [J|[J|[J|[J|J]]]]; subst j; mlia.
  - destruct J as [J|[J|[J|[J|J]]]]; subst j; mlia.
Qed.

Lemma f64_16: forall b rsp, 64 <= msub 64 b (rsp ⊖ 64) -> 16 <= msub 64 b (rsp ⊖ 48 ⊖ 16).
Proof. intros. mlia. Qed.

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Lemma nilfree_unique':
  forall m p a b, nilfree m p a -> m Ⓑ[p ⊕ a] = 0 -> nilfree m p b -> m Ⓑ[p ⊕ b] = 0 -> a = b.
Proof.
  intros m p a b NA ZA NB ZB. destruct (N.lt_trichotomy a b) as [H|[H|H]].
  - exfalso. exact (NB a H ZA).
  - exact H.
  - exfalso. exact (NA b H ZB).
Qed.

Ltac sframe := unfold mpush;
  repeat (rewrite (stack_store_frame _ _ _ _ _ 64) by first [assumption | pure_lia]); reflexivity.

Lemma frameA: forall s0 m v b, 64 <= msub 64 b (s0 R_RSP ⊖ 64) ->
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := v]) Ⓑ[b] = m Ⓑ[b].
Proof. intros. sframe. Qed.

Lemma frameC: forall s0 m v w b, 64 <= msub 64 b (s0 R_RSP ⊖ 64) ->
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓑ[b] = m Ⓑ[b].
Proof. intros. sframe. Qed.

Lemma slotsA: forall s0 m v, s0 R_R14 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 ->
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := v]) Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := v]) Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := v]) Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R14.
Proof.
  intros s0 m v B1 B2 B3. unfold mpush. split; [|split].
  - rewrite getmem_noverlap by exact (qslot64 _ 24 48 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 16 48 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 8 48 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma slotsC: forall s0 m v w, s0 R_R14 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 -> v < 2^64 ->
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R14 /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 32] = v /\
  (mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := v] [Ⓠs0 R_RSP ⊖ 48 := w]) Ⓠ[s0 R_RSP ⊖ 48] = w mod 2^64.
Proof.
  intros s0 m v w B1 B2 B3 B4. unfold mpush. split; [|split; [|split; [|split]]].
  - rewrite getmem_noverlap by exact (qslot64 _ 24 48 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 24 32 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 16 48 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 16 32 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 8 48 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 8 32 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 32 48 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_setmem by discriminate. reflexivity.
Qed.

Lemma slots0: forall s0 m, s0 R_R14 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 ->
  mpush s0 m Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX /\
  mpush s0 m Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\
  mpush s0 m Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R14.
Proof.
  intros s0 m B1 B2 B3. unfold mpush. split; [|split].
  - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot64 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot64 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac cs3_close :=
  match goal with CS: cs3 ?s0 _ |- cs3 ?s0 _ =>
    let a := fresh in let b := fresh in let c := fresh in
    destruct CS as (a & b & c); unfold cs3; repeat split; reg; assumption end.

Theorem strxfrm_l_correct:
  forall prog s t s' x' m d src n
         (XFRM: strxfrm_l_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (STRCPY: strcpy_amd64 ⊆2 prog) (STPCPY: stpcpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1462ed, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (OK: xfrm_ok m d src n (s R_RSP)),
  satisfies_all prog (strxfrm_l_invs s m d src n) strxfrm_l_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n XFRM STRLEN STRCPY STPCPY ENTRY MDL MEM D S Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R14B: s0 R_R14 < 2^64) by (apply (MDL R_R14 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strxfrm_l_program).
    unfold strxfrm_l_program, strcpy_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strxfrm_l_invs.
    unfold strxfrm_l_program, strcpy_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src n MDL MEM D S Nn OK RB RBXB RBPB R14B NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strxfrm_l_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R14B NB. rename t1 into t.
  destruct OK as (L0 & NL0 & ZL0 & OVs & DOK).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP CS]]]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B4. unfold mpush.
    conj_tac. unfold cs3. repeat split; reg; assumption.
  - destruct PRE as [MEM [RDI [R14 [RBP [RBX [RSP CS]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strxfrm_l_program _ _ _ _ s2 nil _ s1 t MDL1 strxfrm_l_program_welltyped).
    intro MDL2.
    assert (SB: forall i, i < L0 + 1 -> (mpush s0 m [Ⓠs0 R_RSP ⊖ 48 := 1336070]) Ⓑ[src ⊕ i] = m Ⓑ[src ⊕ i])
      by (intros i I; apply frameA, (outside64 src (L0 + 1)); assumption).
    eapply (call_leaf_ni strxfrm_l_program strlen_amd64 _ _ (strlen_invs s2 (s2 V_MEM64) src) strlen_exit).
    + apply strlen_in_xfrm.
    + intros a s t' EXIT NOCODE. unfold strlen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strlen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
    + intros a s t' NC. unfold strxfrm_l_invs, strxfrm_l_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold strlen_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (strlen_exit _) eqn:EX; [|destruct PRE].
      unfold strlen_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strxfrm_l_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [RAX [NF Z]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM', NF, Z, RSP'.
      assert (KE: k = L0).
      { apply (nilfree_unique' _ src k L0 NF Z).
        - intros i I. rewrite SB by (clear - I; lia). apply NL0, I.
        - rewrite SB by (clear; lia). exact ZL0. }
      subst k.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      destruct (slotsA s0 m 1336070 R14B RBPB RBXB) as [T24 [T16 T8]].
      destruct (slots0 s0 m R14B RBPB RBXB) as [U24 [U16 U8]].
      repeat x64_step.
      * match goal with BC: (L0 <? _) = true |- _ => apply N.ltb_lt in BC; rename BC into LN end.
        exists L0. split. exact NL0. split. exact ZL0. split. rewrite <- RBP. exact LN.
        split. reflexivity.
        repeat split; try sassumption.
        all: reg; rewrite ?C2, ?C3, ?C5; destruct CS as (B2 & B3 & B5); assumption.
      * match goal with BC: (L0 <? _) = false |- _ => apply N.ltb_ge in BC; rename BC into LN end.
        rewrite U24, U16, U8.
        split. exists L0. split. exact NL0. split. exact ZL0. split. reflexivity.
          split. intro H. exfalso. rewrite RBP in LN. clear - H LN. lia.
          intros b B1 B2. apply frameA. exact B2.
        split. apply N.mod_small. exact RB.
        destruct CS as (B2 & B3 & B5). unfold callee_saved_eq. repeat split; reg; first [sassumption | (rewrite ?C2, ?C3, ?C5; sassumption)].
  - destruct PRE as [L [NL [ZL [LN [MEM [RDI [RSI [RSP [R14 [RBP [RBX CS]]]]]]]]]]].
    assert (LE: L = L0) by exact (nilfree_unique' m src L L0 NL ZL NL0 ZL0). subst L.
    destruct (DOK LN) as [NOVds OVd].
    assert (LB: L0 < 2^64) by (clear - LN NB; lia).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strxfrm_l_program _ _ _ _ s2 nil _ s1 t MDL1 strxfrm_l_program_welltyped).
    intro MDL2.
    set (M3 := mpush s0 m [Ⓠs0 R_RSP ⊖ 32 := L0] [Ⓠs0 R_RSP ⊖ 48 := 1336106]) in *.
    assert (S2M: s2 V_MEM64 = M3) by (unfold s2; apply update_updated).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 48) by (unfold s2; rewrite update_frame by discriminate; apply update_updated).
    assert (SB: forall i, i < L0 + 1 -> M3 Ⓑ[src ⊕ i] = m Ⓑ[src ⊕ i])
      by (intros i I; unfold M3; apply frameC, (outside64 src (L0 + 1)); assumption).
    destruct (slotsC s0 m L0 1336106 R14B RBPB RBXB LB) as [V24 [V16 [V8 [V32 V48]]]].
    fold M3 in V24, V16, V8, V32, V48.
    eapply (call_leaf_ni strxfrm_l_program strcpy_program _ _
              (strcpy_invs s2 (s2 V_MEM64) d src L0) strcpy_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold strcpy_invs.
      unfold strcpy_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strcpy_correct; first
        [ apply strcpy_in_prog | apply subset_updateall2 | assumption | reflexivity
        | (unfold s2; reg; assumption) | idtac ].
      rewrite S2M, S2R. split; [split; [|split] | split].
      * intros i I. rewrite SB by (clear - I; lia). apply NL0, I.
      * rewrite SB by (clear; lia). exact ZL0.
      * exact NOVds.
      * apply sub64_16, OVd.
      * apply sub64_16, OVs.
    + intros a s t' NC. unfold strxfrm_l_invs, strxfrm_l_exit.
      unfold strcpy_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold strcpy_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (strcpy_exit _) eqn:EX; [|destruct PRE].
      unfold strcpy_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strxfrm_l_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [CPY [FR [RSP' CS']]]].
      rewrite S2M in CPY, FR. rewrite S2R in FR, RSP'.
      assert (RQ: forall j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32 \/ j = 48) ->
                s' V_MEM64 Ⓠ[s0 R_RSP ⊖ j] = M3 Ⓠ[s0 R_RSP ⊖ j]).
      { intros j J. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
        destruct (slot_ok d L0 _ j a OVd J A) as [A1 A2]. exact (FR a A1 A2). }
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 48] = 1336106)
        by (rewrite (RQ 48), V48 by (right; right; right; right; reflexivity); reflexivity).
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). unfold s2 in C0, C1, C2, C3, C4, C5.
      rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      x64_step. rewrite RA. repeat x64_step.
      rewrite (RQ 32), V32 by (right; right; right; left; reflexivity).
      rewrite (RQ 24), V24 by (right; right; left; reflexivity).
      rewrite (RQ 16), V16 by (right; left; reflexivity).
      rewrite (RQ 8), V8 by (left; reflexivity).
      split. exists L0. split. exact NL0. split. exact ZL0. split. reflexivity.
        split. intros _ i I. rewrite CPY by exact I. apply SB, I.
        intros b B1 B2. rewrite (FR b (B1 LN) (f64_16 b _ B2)). unfold M3. apply frameC. exact B2.
      split. apply N.mod_small. exact RB.
      destruct CS as (B2 & B3 & B5). unfold callee_saved_eq. repeat split; reg;
        first [sassumption | (rewrite ?C2, ?C3, ?C5; sassumption)].
Qed.

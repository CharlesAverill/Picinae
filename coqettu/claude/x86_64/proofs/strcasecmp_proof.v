(* strcasecmp -- compare two strings ignoring case (musl x86_64, C),
   composed with tolower (four call sites)

   SEMANTICS
   ---------
   musl's strcasecmp (src/string/strcasecmp.c) is

       const unsigned char *l=(void * )_l, *r=(void * )_r;
       for (; *l && *r && ( *l == *r || tolower( *l) == tolower( *r)); l++, r++);
       return tolower( *l) - tolower( *r);

   The binary saves R12, RBP (= l) and RBX (= r) and CALLs tolower
   (0x141924) twice inside the loop (when the bytes differ) and twice after
   it.  tolower's contract (ctype_proof.v: RAX = tolower_spec c, no memory
   writes, callee-saved registers kept) is used through call_leaf_ni at
   each call site.

   SPECIFICATION (man 3 strcasecmp, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------------
     int strcasecmp(const char *s1, const char *s2);
     strcasecmp performs a byte-by-byte comparison of the strings s1 and
     s2, ignoring the case of the characters.  It returns an integer less
     than, equal to, or greater than zero if s1 is, after ignoring case,
     found to be less than, to match, or be greater than s2.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strcasecmp at 0x658e8, tolower at 0x41924 (Ghidra image base
            0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strcasecmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = l, RSI = r; RSP = rsp; m = memory.  Precondition
            (casecmp_ok): l and r are NUL-terminated and neither string
            (through its terminator) overlaps the 32 bytes below rsp.
   Output:  At the RET (0x165943): for the stop index K (ceq: for i < K,
            l[i] and r[i] are nonzero with tl l[i] = tl r[i], where tl is
            tolower_spec on a byte; cstop: l[K] = 0, r[K] = 0, or
            tl l[K] <> tl r[K]), RAX = (tl l[K] - tl r[K]) mod 2^32 (EAX,
            zero-extended).  Nothing outside the 32 bytes below rsp changes;
            RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strcasecmp_amd64 CoqEtTu.programs.tolower_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_ctype.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.ctype_proof.
Open Scope N.

Definition strcasecmp_program : program := updateall2 strcasecmp_amd64 tolower_amd64.

Theorem strcasecmp_welltyped: welltyped_prog x64typctx strcasecmp_amd64.
Proof. exact strcasecmp_amd64.welltyped. Qed.

Lemma strcasecmp_program_welltyped: welltyped_prog x64typctx strcasecmp_program.
Proof.
  intros s a. unfold strcasecmp_program, updateall2, updateall.
  destruct (tolower_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (tolower_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply strcasecmp_welltyped.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition tl (b:N) := tolower_spec b.

(* the first k byte pairs are nonzero and equal up to case *)
Definition ceq (m:memory) (l r k:N) :=
  forall i, i < k -> m Ⓑ[l ⊕ i] <> 0 /\ m Ⓑ[r ⊕ i] <> 0 /\ tl (m Ⓑ[l ⊕ i]) = tl (m Ⓑ[r ⊕ i]).

Definition cstop (m:memory) (l r K:N) :=
  m Ⓑ[l ⊕ K] = 0 \/ m Ⓑ[r ⊕ K] = 0 \/ tl (m Ⓑ[l ⊕ K]) <> tl (m Ⓑ[r ⊕ K]).

Definition casecmp_ok (m l r rsp:N) :=
  (exists L, nilfree m l L /\ m Ⓑ[l ⊕ L] = 0 /\ ~ overlap 64 l (L + 1) (rsp ⊖ 32) 32) /\
  (exists L, nilfree m r L /\ m Ⓑ[r ⊕ L] = 0 /\ ~ overlap 64 r (L + 1) (rsp ⊖ 32) 32).

(* the memory during the loop: unchanged above the 32 bytes below rsp, and
   the three saved registers in their slots *)
Definition frm (s0:store) (m M:memory) :=
  (forall b, 32 <= msub 64 b (s0 R_RSP ⊖ 32) -> M Ⓑ[b] = m Ⓑ[b]) /\
  M Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R12 /\ M Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\ M Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX.

Definition cs3 (s0 s:store) :=
  s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition strcasecmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165943 => true
  | _ => false end | _ => false end.

Definition strcasecmp_post (s0:store) (m l r:N) (s:store) :=
  (exists K, ceq m l r K /\ cstop m l r K /\
     s R_RAX = msub 32 (tl (m Ⓑ[l ⊕ K])) (tl (m Ⓑ[r ⊕ K]))) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 32 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strcasecmp_invs (s0:store) (m l r:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1658e8 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1658fc => Some (exists k, ceq m l r k /\ frm s0 m (s V_MEM64) /\
                      s R_RBP = l ⊕ k /\ s R_RBX = r ⊕ k /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165911 => Some (exists k, ceq m l r k /\ m Ⓑ[l ⊕ k] <> 0 /\ m Ⓑ[r ⊕ k] <> 0 /\
                      m Ⓑ[l ⊕ k] <> m Ⓑ[r ⊕ k] /\ frm s0 m (s V_MEM64) /\ s R_RDI = m Ⓑ[l ⊕ k] /\
                      s R_RBP = l ⊕ k /\ s R_RBX = r ⊕ k /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x16591c => Some (exists k, ceq m l r k /\ m Ⓑ[l ⊕ k] <> 0 /\ m Ⓑ[r ⊕ k] <> 0 /\
                      frm s0 m (s V_MEM64) /\ s R_RDI = m Ⓑ[r ⊕ k] /\ s R_R12 = tl (m Ⓑ[l ⊕ k]) /\
                      s R_RBP = l ⊕ k /\ s R_RBX = r ⊕ k /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x16592a => Some (exists k, ceq m l r k /\ cstop m l r k /\ frm s0 m (s V_MEM64) /\
                      s R_RDI = m Ⓑ[l ⊕ k] /\ s R_RBX = r ⊕ k /\ s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165934 => Some (exists k, ceq m l r k /\ cstop m l r k /\ frm s0 m (s V_MEM64) /\
                      s R_RDI = m Ⓑ[r ⊕ k] /\ s R_RBP = tl (m Ⓑ[l ⊕ k]) /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165943 => Some (strcasecmp_post s0 m l r s)
  | _ => None
  end | _ => None end.

(* ---- facts, each proved in an empty context ---- *)

Lemma qslot:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 32) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma frm_init:
  forall s0 m, s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 ->
  frm s0 m (m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX]).
Proof.
  intros s0 m B1 B2 B3. split; [|split; [|split]].
  - intros b B.
    rewrite (stack_store_frame _ (s0 R_RSP) 24 _ b 32) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 32) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 32) by (assumption || lia).
    reflexivity.
  - rewrite getmem_noverlap by exact (qslot _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma frm_ra: forall s0 m M v, frm s0 m M -> frm s0 m (M [Ⓠs0 R_RSP ⊖ 32 := v]).
Proof.
  intros s0 m M v [F [S8 [S16 S24]]]. split; [|split; [|split]].
  - intros b B. rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 32) by (assumption || lia). apply F, B.
  - rewrite getmem_noverlap by exact (qslot _ 8 32 eq_refl). exact S8.
  - rewrite getmem_noverlap by exact (qslot _ 16 32 eq_refl). exact S16.
  - rewrite getmem_noverlap by exact (qslot _ 24 32 eq_refl). exact S24.
Qed.

Lemma outside32:
  forall x n rsp i, ~ overlap 64 x n (rsp ⊖ 32) 32 -> i < n -> 32 <= msub 64 (x ⊕ i) (rsp ⊖ 32).
Proof.
  intros x n rsp i NOV I. assert (BB: rsp ⊖ 32 < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ 32) in *. clearbody b.
  destruct (N.le_gt_cases 32 (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D. mlia.
Qed.

(* a string byte read during the loop sees m *)
Lemma frm_byte:
  forall s0 m M x L i, frm s0 m M -> ~ overlap 64 x (L + 1) (s0 R_RSP ⊖ 32) 32 -> i <= L ->
  M Ⓑ[x ⊕ i] = m Ⓑ[x ⊕ i].
Proof. intros s0 m M x L i [F _] NOV I. apply F. apply (outside32 x (L + 1)). exact NOV. lia. Qed.

(* the stop index is at most each string's length *)
Lemma ceq_le:
  forall m l r k L, ceq m l r k -> m Ⓑ[l ⊕ L] = 0 -> k <= L.
Proof.
  intros m l r k L C Z. destruct (N.le_gt_cases k L) as [H|H]. exact H.
  exfalso. exact (proj1 (C L H) Z).
Qed.

Lemma ceq_le_r:
  forall m l r k L, ceq m l r k -> m Ⓑ[r ⊕ L] = 0 -> k <= L.
Proof.
  intros m l r k L C Z. destruct (N.le_gt_cases k L) as [H|H]. exact H.
  exfalso. exact (proj1 (proj2 (C L H)) Z).
Qed.

Lemma ceq_succ:
  forall m l r k, ceq m l r k -> m Ⓑ[l ⊕ k] <> 0 -> m Ⓑ[r ⊕ k] <> 0 ->
  tl (m Ⓑ[l ⊕ k]) = tl (m Ⓑ[r ⊕ k]) -> ceq m l r (k + 1).
Proof.
  intros m l r k C A B T i I. destruct (N.lt_ge_cases i k). apply C. assumption.
  replace i with k by lia. split. exact A. split. exact B. exact T.
Qed.

Lemma byte_lt: forall (m:memory) a, m Ⓑ[a] < 2^32.
Proof.
  intros. eapply N.lt_le_trans. apply (getmem_bound 64 LittleE 1). change (2^(1*8)) with 256. discriminate.
Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac cs3_close :=
  match goal with CS: cs3 ?s0 _ |- cs3 ?s0 _ =>
    let a := fresh in let b := fresh in let c := fresh in
    destruct CS as (a & b & c); unfold cs3; repeat split; reg; assumption end.

Lemma tl_lt: forall b, b < 256 -> tl b < 2^32.
Proof. intros b B. unfold tl, tolower_spec. destruct (inr 65 90 b); change (2^32) with 4294967296; lia. Qed.

Lemma tl_byte: forall (m:memory) a, tl (m Ⓑ[a]) < 2^32.
Proof. intros. apply tl_lt. exact (getmem_bound 64 LittleE 1 m a). Qed.

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Theorem strcasecmp_correct:
  forall prog s t s' x' m l r
         (STRCASECMP: strcasecmp_amd64 ⊆2 prog) (TOLOWER: tolower_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1658e8, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r)
         (OK: casecmp_ok m l r (s R_RSP)),
  satisfies_all prog (strcasecmp_invs s m l r) strcasecmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r STRCASECMP TOLOWER ENTRY MDL MEM L R OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (LB: l < 2^64) by (rewrite <- L; apply (MDL R_RDI 64); reflexivity).
  assert (RRB: r < 2^64) by (rewrite <- R; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strcasecmp_program).
    unfold strcasecmp_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strcasecmp_invs.
    unfold strcasecmp_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m l r MDL MEM L R OK RB RBXB RBPB R12B LB RRB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcasecmp_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B LB RRB. rename t1 into t.
  destruct OK as [(Ll & NLl & ZLl & OVl) (Lr & NLr & ZLr & OVr)].
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [L [R [RSP CS]]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B2.
    exists 0. split. intros i I. exfalso. exact (N.nlt_0_r i I).
    split. apply frm_init; assumption.
    split. rewrite N.add_0_r, N.mod_small by exact LB. reflexivity.
    split. rewrite N.add_0_r, N.mod_small by exact RRB. reflexivity.
    split. reflexivity.
    unfold cs3. repeat split; reg; assumption.
  - destruct PRE as [k [CQ [FR [RBP [RBX [RSP CS]]]]]].
    assert (KL: k <= Ll) by exact (ceq_le m l r k Ll CQ ZLl).
    assert (KR: k <= Lr) by exact (ceq_le_r m l r k Lr CQ ZLr).
    assert (BL: s1 V_MEM64 Ⓑ[l + k] = m Ⓑ[l ⊕ k])
      by (rewrite <- getmem_mod_l; exact (frm_byte s0 m _ l Ll k FR OVl KL)).
    assert (BR: s1 V_MEM64 Ⓑ[r + k] = m Ⓑ[r ⊕ k])
      by (rewrite <- getmem_mod_l; exact (frm_byte s0 m _ r Lr k FR OVr KR)).
    repeat x64_step.
    all: rewrite ?BL, ?BR in *.
    + (* l[k] = 0 *)
      match goal with BC: (m Ⓑ[l ⊕ k] =? 0) = true |- _ => apply N.eqb_eq in BC end.
      exists k. conj_tac. left. assumption. cs3_close.
    + (* r[k] = 0 *)
      match goal with BC: (m Ⓑ[r ⊕ k] =? 0) = true |- _ => apply N.eqb_eq in BC end.
      exists k. conj_tac. right. left. assumption. cs3_close.
    + (* equal bytes *)
      match goal with BC: (m Ⓑ[l ⊕ k] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (m Ⓑ[r ⊕ k] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (m Ⓑ[l ⊕ k] =? m Ⓑ[r ⊕ k]) = true |- _ => apply N.eqb_eq in BC; rename BC into EQ end.
      exists (k + 1). conj_tac.
      * apply ceq_succ; try assumption. rewrite EQ. reflexivity.
      * f_equal. pure_lia.
      * f_equal. pure_lia.
      * cs3_close.
    + (* different bytes: call tolower *)
      match goal with BC: (m Ⓑ[l ⊕ k] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (m Ⓑ[r ⊕ k] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (m Ⓑ[l ⊕ k] =? m Ⓑ[r ⊕ k]) = false |- _ => apply N.eqb_neq in BC end.
      exists k. conj_tac. cs3_close.
  - destruct PRE as [k [CQ [NL0 [NR0 [NE [FR [RDI [RBP [RBX [RSP CS]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcasecmp_program _ _ _ _ s2 nil _ s1 t MDL1 strcasecmp_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strcasecmp_program tolower_amd64 _ _ (tolower_invs s2 (s2 R_RDI)) tolower_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold tolower_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply tolower_correct; first [ apply pf2sub_refl | assumption | reflexivity ].
    + intros a s t' NC. unfold strcasecmp_invs, strcasecmp_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold tolower_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (tolower_exit _) eqn:EX; [|destruct PRE].
      unfold tolower_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcasecmp_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [MEM' [RSP' CS']]].
      unfold s2 in RAX', MEM', RSP', CS'. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM'.
      rewrite !update_frame in RAX' by discriminate. rewrite RDI, N.mod_small in RAX' by apply byte_lt.
      repeat x64_step.
      assert (RBXs: s' R_RBX = r ⊕ k) by (rewrite (proj1 CS'); reg; exact RBX).
      assert (RBPs: s' R_RBP = l ⊕ k) by (rewrite (proj1 (proj2 CS')); reg; exact RBP).
      assert (KR: k <= Lr) by exact (ceq_le_r m l r k Lr CQ ZLr).
      exists k. split. exact CQ. split. exact NL0. split. exact NR0.
      split. apply frm_ra, FR.
      split. rewrite RBXs. exact (frm_byte s0 m _ r Lr k (frm_ra _ _ _ _ FR) OVr KR).
      split. unfold tl. apply N.mod_small, tl_byte.
      split. exact RBPs. split. exact RBXs. split. reflexivity.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C3, C4, C5 by discriminate.
      destruct CS as (B3 & B4 & B5). unfold cs3. reg. rewrite C3, C4, C5. repeat split; assumption.
  - destruct PRE as [k [CQ [NL0 [NR0 [FR [RDI [R12 [RBP [RBX [RSP CS]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcasecmp_program _ _ _ _ s2 nil _ s1 t MDL1 strcasecmp_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strcasecmp_program tolower_amd64 _ _ (tolower_invs s2 (s2 R_RDI)) tolower_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold tolower_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply tolower_correct; first [ apply pf2sub_refl | assumption | reflexivity ].
    + intros a s t' NC. unfold strcasecmp_invs, strcasecmp_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold tolower_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (tolower_exit _) eqn:EX; [|destruct PRE].
      unfold tolower_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcasecmp_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [MEM' [RSP' CS']]].
      unfold s2 in RAX', MEM', RSP', CS'.
      rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM'.
      rewrite !update_frame in RAX' by discriminate. rewrite RDI, N.mod_small in RAX' by apply byte_lt.
      assert (RBXs: s' R_RBX = r ⊕ k) by (rewrite (proj1 CS'); reg; exact RBX).
      assert (RBPs: s' R_RBP = l ⊕ k) by (rewrite (proj1 (proj2 CS')); reg; exact RBP).
      assert (R12s: s' R_R12 = tl (m Ⓑ[l ⊕ k])) by (rewrite (proj1 (proj2 (proj2 CS'))); reg; exact R12).
      assert (KL: k <= Ll) by exact (ceq_le m l r k Ll CQ ZLl).
      assert (KR: k <= Lr) by exact (ceq_le_r m l r k Lr CQ ZLr).
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C3, C4, C5 by discriminate.
      repeat x64_step.
      all: change (tolower_spec (m Ⓑ[r ⊕ k])) with (tl (m Ⓑ[r ⊕ k])) in *.
      all: rewrite (N.mod_small (tl (m Ⓑ[l ⊕ k]))), (N.mod_small (tl (m Ⓑ[r ⊕ k]))) in * by apply tl_byte.
      * match goal with BC: (tl _ =? tl _) = true |- _ => apply N.eqb_eq in BC; rename BC into EQ end.
        exists (k + 1). split. exact (ceq_succ m l r k CQ NL0 NR0 EQ).
        split. apply frm_ra, FR.
        split. f_equal. pure_lia. split. f_equal. pure_lia. split. reflexivity.
        destruct CS as (B3 & B4 & B5). unfold cs3. reg. rewrite C3, C4, C5. repeat split; assumption.
      * match goal with BC: (tl _ =? tl _) = false |- _ => apply N.eqb_neq in BC; rename BC into NE end.
        exists k. split. exact CQ. split. right. right. exact NE.
        split. apply frm_ra, FR.
        split. rewrite <- getmem_mod_l. exact (frm_byte s0 m _ l Ll k (frm_ra _ _ _ _ FR) OVl KL).
        split. exact RBXs. split. reflexivity.
        destruct CS as (B3 & B4 & B5). unfold cs3. reg. rewrite C3, C4, C5. repeat split; assumption.
  - destruct PRE as [k [CQ [CST [FR [RDI [RBX [RSP CS]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcasecmp_program _ _ _ _ s2 nil _ s1 t MDL1 strcasecmp_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strcasecmp_program tolower_amd64 _ _ (tolower_invs s2 (s2 R_RDI)) tolower_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold tolower_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply tolower_correct; first [ apply pf2sub_refl | assumption | reflexivity ].
    + intros a s t' NC. unfold strcasecmp_invs, strcasecmp_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold tolower_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (tolower_exit _) eqn:EX; [|destruct PRE].
      unfold tolower_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcasecmp_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [MEM' [RSP' CS']]].
      unfold s2 in RAX', MEM', RSP', CS'.
      rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM'.
      rewrite !update_frame in RAX' by discriminate. rewrite RDI, N.mod_small in RAX' by apply byte_lt.
      assert (RBXs: s' R_RBX = r ⊕ k) by (rewrite (proj1 CS'); reg; exact RBX).
      assert (KR: k <= Lr) by exact (ceq_le_r m l r k Lr CQ ZLr).
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C3, C4, C5 by discriminate.
      repeat x64_step.
      change (tolower_spec (m Ⓑ[l ⊕ k])) with (tl (m Ⓑ[l ⊕ k])) in *.
      rewrite (N.mod_small (tl (m Ⓑ[l ⊕ k]))) in * by apply tl_byte.
      exists k. split. exact CQ. split. exact CST.
      split. apply frm_ra, FR.
      split. rewrite <- (getmem_mod_l _ _ _ _ (r + k)).
        exact (frm_byte s0 m _ r Lr k (frm_ra _ _ _ _ FR) OVr KR).
      split. reflexivity. split. reflexivity.
      destruct CS as (B3 & B4 & B5). unfold cs3. reg. rewrite C3, C4, C5. repeat split; assumption.
  - destruct PRE as [k [CQ [CST [FR [RDI [RBP [RSP CS]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcasecmp_program _ _ _ _ s2 nil _ s1 t MDL1 strcasecmp_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strcasecmp_program tolower_amd64 _ _ (tolower_invs s2 (s2 R_RDI)) tolower_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold tolower_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply tolower_correct; first [ apply pf2sub_refl | assumption | reflexivity ].
    + intros a s t' NC. unfold strcasecmp_invs, strcasecmp_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold tolower_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (tolower_exit _) eqn:EX; [|destruct PRE].
      unfold tolower_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcasecmp_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [MEM' [RSP' CS']]].
      unfold s2 in RAX', MEM', RSP', CS'.
      rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM'.
      rewrite !update_frame in RAX' by discriminate. rewrite RDI, N.mod_small in RAX' by apply byte_lt.
      assert (RBPs: s' R_RBP = tl (m Ⓑ[l ⊕ k])) by (rewrite (proj1 (proj2 CS')); reg; exact RBP).
      pose proof (frm_ra _ _ _ 1464633 FR) as FR'.
      destruct FR' as [FB _]. destruct FR as [_ [T8 [T16 T24]]].
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C3, C4, C5 by discriminate.
      repeat x64_step.
      change (tolower_spec (m Ⓑ[r ⊕ k])) with (tl (m Ⓑ[r ⊕ k])) in *.
      rewrite T8, T16, T24.
      split. exists k. split. exact CQ. split. exact CST. reflexivity.
      split. intros b B. apply FB, B.
      split. apply N.mod_small. exact RB.
      destruct CS as (B3 & B4 & B5). unfold callee_saved_eq. reg. rewrite C3, C4, C5.
      repeat split; sassumption.
Qed.

(* strncasecmp -- compare at most n bytes of two strings ignoring case
   (musl x86_64, C), composed with tolower (four call sites)

   SEMANTICS
   ---------
   musl's strncasecmp (src/string/strncasecmp.c) is

       const unsigned char *l=(void * )_l, *r=(void * )_r;
       if (!n--) return 0;
       for (; *l && *r && n && ( *l == *r || tolower( *l) == tolower( *r)); l++, r++, n--);
       return tolower( *l) - tolower( *r);

   The binary returns 0 at once for n = 0; otherwise it saves R13, R12,
   RBP and RBX, keeps l in RBX, r in RBP and the last allowed position
   l+n-1 in R12, and CALLs tolower (0x141924) at four sites as strcasecmp
   does.  tolower's contract (ctype_proof.v) is used through call_leaf_ni.

   SPECIFICATION (man 3 strncasecmp, Linux man-pages 6.9.1, paraphrased)
   --------------------------------------------------------------------
     int strncasecmp(const char s1[.n], const char s2[.n], size_t n);
     strncasecmp is like strcasecmp except that it compares no more than n
     bytes of s1 and s2.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strncasecmp at 0x65ab9, tolower at 0x41924 (Ghidra image base
            0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strncasecmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = l, RSI = r, RDX = n; RSP = rsp; m = memory.  Precondition
            (ncase_ok): the n bytes at l and the n bytes at r do not overlap
            the 48 bytes below rsp.  The strings need not be terminated
            within n bytes.
   Output:  At the RETs (0x165b30, 0x165b33): if n = 0, RAX = 0; otherwise
            for the stop index K < n (ceq: for i < K, l[i], r[i] nonzero and
            equal up to case; and K = n-1 or cstop as in strcasecmp_proof.v),
            RAX = (tl l[K] - tl r[K]) mod 2^32.  Nothing outside the 48
            bytes below rsp changes; RSP = rsp; RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strncasecmp_amd64 CoqEtTu.programs.tolower_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_ctype.
Require Import CoqEtTu.proofs.ctype_proof CoqEtTu.proofs.strcasecmp_proof.
Open Scope N.

Definition strncasecmp_program : program := updateall2 strncasecmp_amd64 tolower_amd64.

Theorem strncasecmp_welltyped: welltyped_prog x64typctx strncasecmp_amd64.
Proof. exact strncasecmp_amd64.welltyped. Qed.

Lemma strncasecmp_program_welltyped: welltyped_prog x64typctx strncasecmp_program.
Proof.
  intros s a. unfold strncasecmp_program, updateall2, updateall.
  destruct (tolower_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (tolower_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply strncasecmp_welltyped.
Qed.

Definition ncase_ok (l r n rsp:N) :=
  ~ overlap 64 l n (rsp ⊖ 48) 48 /\ ~ overlap 64 r n (rsp ⊖ 48) 48.

Definition frm48 (s0:store) (m M:memory) :=
  (forall b, 48 <= msub 64 b (s0 R_RSP ⊖ 48) -> M Ⓑ[b] = m Ⓑ[b]) /\
  M Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R13 /\ M Ⓠ[s0 R_RSP ⊖ 16] = s0 R_R12 /\
  M Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBP /\ M Ⓠ[s0 R_RSP ⊖ 32] = s0 R_RBX.

Definition cs2 (s0 s:store) := s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition cstopn (m:memory) (l r n K:N) := K = n - 1 \/ cstop m l r K.

Definition strncasecmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165b30 | 0x165b33 => true
  | _ => false end | _ => false end.

Definition strncasecmp_post (s0:store) (m l r n:N) (s:store) :=
  ((n = 0 /\ s R_RAX = 0) \/
   (exists K, K < n /\ ceq m l r K /\ cstopn m l r n K /\
      s R_RAX = msub 32 (tl (m Ⓑ[l ⊕ K])) (tl (m Ⓑ[r ⊕ K])))) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 48 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strncasecmp_invs (s0:store) (m l r n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165ab9 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165add => Some (exists k, k < n /\ ceq m l r k /\ frm48 s0 m (s V_MEM64) /\
                      s R_RBX = l ⊕ k /\ s R_RBP = r ⊕ k /\ s R_R12 = l ⊕ (n - 1) /\
                      s R_RSP = s0 R_RSP ⊖ 40 /\ cs2 s0 s)
  | 0x165af7 => Some (exists k, k < n - 1 /\ ceq m l r k /\ m Ⓑ[l ⊕ k] <> 0 /\ m Ⓑ[r ⊕ k] <> 0 /\
                      m Ⓑ[l ⊕ k] <> m Ⓑ[r ⊕ k] /\ frm48 s0 m (s V_MEM64) /\ s R_RDI = m Ⓑ[l ⊕ k] /\
                      s R_RBX = l ⊕ k /\ s R_RBP = r ⊕ k /\ s R_R12 = l ⊕ (n - 1) /\
                      s R_RSP = s0 R_RSP ⊖ 40 /\ cs2 s0 s)
  | 0x165b03 => Some (exists k, k < n - 1 /\ ceq m l r k /\ m Ⓑ[l ⊕ k] <> 0 /\ m Ⓑ[r ⊕ k] <> 0 /\
                      frm48 s0 m (s V_MEM64) /\ s R_RDI = m Ⓑ[r ⊕ k] /\ s R_R13 = tl (m Ⓑ[l ⊕ k]) /\
                      s R_RBX = l ⊕ k /\ s R_RBP = r ⊕ k /\ s R_R12 = l ⊕ (n - 1) /\
                      s R_RSP = s0 R_RSP ⊖ 40 /\ cs2 s0 s)
  | 0x165b10 => Some (exists k, k < n /\ ceq m l r k /\ cstopn m l r n k /\ frm48 s0 m (s V_MEM64) /\
                      s R_RDI = m Ⓑ[l ⊕ k] /\ s R_RBP = r ⊕ k /\ s R_RSP = s0 R_RSP ⊖ 40 /\ cs2 s0 s)
  | 0x165b1b => Some (exists k, k < n /\ ceq m l r k /\ cstopn m l r n k /\ frm48 s0 m (s V_MEM64) /\
                      s R_RDI = m Ⓑ[r ⊕ k] /\ s R_RBX = tl (m Ⓑ[l ⊕ k]) /\
                      s R_RSP = s0 R_RSP ⊖ 40 /\ cs2 s0 s)
  | 0x165b30 | 0x165b33 => Some (strncasecmp_post s0 m l r n s)
  | _ => None
  end | _ => None end.

(* ---- facts, each proved in an empty context ---- *)

Lemma qslot48:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 48) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma frm48_init:
  forall s0 m, s0 R_R13 < 2^64 -> s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 ->
  frm48 s0 m (m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R13] [Ⓠs0 R_RSP ⊖ 16 := s0 R_R12]
                [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 32 := s0 R_RBX]).
Proof.
  intros s0 m B1 B2 B3 B4. split; [|split; [|split; [|split]]].
  - intros b B.
    rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 48) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 24 _ b 48) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 48) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 48) by (assumption || lia).
    reflexivity.
  - rewrite getmem_noverlap by exact (qslot48 _ 8 32 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot48 _ 16 32 eq_refl).
    rewrite getmem_noverlap by exact (qslot48 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot48 _ 24 32 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma frm48_ra: forall s0 m M v, frm48 s0 m M -> frm48 s0 m (M [Ⓠs0 R_RSP ⊖ 48 := v]).
Proof.
  intros s0 m M v [F [S8 [S16 [S24 S32]]]]. split; [|split; [|split; [|split]]].
  - intros b B. rewrite (stack_store_frame _ (s0 R_RSP) 48 _ b 48) by (assumption || lia). apply F, B.
  - rewrite getmem_noverlap by exact (qslot48 _ 8 48 eq_refl). exact S8.
  - rewrite getmem_noverlap by exact (qslot48 _ 16 48 eq_refl). exact S16.
  - rewrite getmem_noverlap by exact (qslot48 _ 24 48 eq_refl). exact S24.
  - rewrite getmem_noverlap by exact (qslot48 _ 32 48 eq_refl). exact S32.
Qed.

Lemma outside48:
  forall x n rsp i, ~ overlap 64 x n (rsp ⊖ 48) 48 -> i < n -> 48 <= msub 64 (x ⊕ i) (rsp ⊖ 48).
Proof.
  intros x n rsp i NOV I. assert (BB: rsp ⊖ 48 < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ 48) in *. clearbody b.
  destruct (N.le_gt_cases 48 (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D. mlia.
Qed.

Lemma frm48_byte:
  forall s0 m M x n i, frm48 s0 m M -> ~ overlap 64 x n (s0 R_RSP ⊖ 48) 48 -> i < n ->
  M Ⓑ[x ⊕ i] = m Ⓑ[x ⊕ i].
Proof. intros s0 m M x n i [F _] NOV I. apply F. exact (outside48 x n _ i NOV I). Qed.

Lemma end_eq: forall l n k, n < 2^64 -> k < n -> ((l ⊕ k) =? (l ⊕ (n - 1))) = (k =? n - 1).
Proof.
  intros l n k NB K. destruct (N.eqb_spec k (n - 1)) as [E|E].
  - subst k. apply N.eqb_refl.
  - apply N.eqb_neq. intro H. apply E. mlia.
Qed.

Lemma r12_init: forall l n, 0 < n -> l < 2^64 -> n < 2^64 -> (l ⊖ 1 + n) mod 2^64 = l ⊕ (n - 1).
Proof. intros. mlia. Qed.

Lemma k_mod: forall k n, k < n -> n < 2^64 -> k mod 2^64 = k.
Proof. intros. apply N.mod_small. lia. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Ltac cs2_close :=
  match goal with CS: cs2 ?s0 _ |- cs2 ?s0 _ =>
    let a := fresh in let b := fresh in
    destruct CS as (a & b); unfold cs2; repeat split; reg; assumption end.

Theorem strncasecmp_correct:
  forall prog s t s' x' m l r n
         (STRNCASECMP: strncasecmp_amd64 ⊆2 prog) (TOLOWER: tolower_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165ab9, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r) (Nn: s R_RDX = n)
         (OK: ncase_ok l r n (s R_RSP)),
  satisfies_all prog (strncasecmp_invs s m l r n) strncasecmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r n STRNCASECMP TOLOWER ENTRY MDL MEM L R Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (R13B: s0 R_R13 < 2^64) by (apply (MDL R_R13 64); reflexivity).
  assert (LB: l < 2^64) by (rewrite <- L; apply (MDL R_RDI 64); reflexivity).
  assert (RRB: r < 2^64) by (rewrite <- R; apply (MDL R_RSI 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strncasecmp_program).
    unfold strncasecmp_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strncasecmp_invs.
    unfold strncasecmp_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m l r n MDL MEM L R Nn OK RB RBXB RBPB R12B R13B LB RRB NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncasecmp_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B R13B LB RRB NB. rename t1 into t.
  destruct OK as [OVl OVr].
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [L [R [Nn [RSP CS]]]]].
    repeat x64_step.
    + (* n = 0 *)
      match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC end.
      split. left. split. assumption. reflexivity.
      split. rewrite MEM. apply stack_frame_refl.
      conj_tac.
    + match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC end.
      pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B2, B3.
      exists 0. split. clear - BC; lia.
      split. intros i I. exfalso. exact (N.nlt_0_r i I).
      split. apply frm48_init; assumption.
      split. rewrite N.add_0_r, N.mod_small by exact LB. reflexivity.
      split. rewrite N.add_0_r, N.mod_small by exact RRB. reflexivity.
      split. apply r12_init; [clear - BC; lia | exact LB | exact NB].
      split. reflexivity.
      unfold cs2. repeat split; reg; assumption.
  - destruct PRE as [k [KN [CQ [FR [RBX [RBP [R12 [RSP CS]]]]]]]].
    assert (BL: s1 V_MEM64 Ⓑ[l + k] = m Ⓑ[l ⊕ k])
      by (rewrite <- getmem_mod_l; exact (frm48_byte s0 m _ l n k FR OVl KN)).
    assert (BR: s1 V_MEM64 Ⓑ[r + k] = m Ⓑ[r ⊕ k])
      by (rewrite <- getmem_mod_l; exact (frm48_byte s0 m _ r n k FR OVr KN)).
    repeat x64_step.
    all: rewrite ?BL, ?BR in *.
    all: try rewrite (k_mod k n KN NB) in *.
    + match goal with BC: (m Ⓑ[l ⊕ k] =? 0) = true |- _ => apply N.eqb_eq in BC end.
      exists k. conj_tac. right. left. assumption. cs2_close.
    + match goal with BC: (k =? n - 1) = true |- _ => apply N.eqb_eq in BC end.
      exists k. conj_tac. left. assumption. cs2_close.
    + match goal with BC: (m Ⓑ[r ⊕ k] =? 0) = true |- _ => apply N.eqb_eq in BC end.
      exists k. conj_tac. right. right. left. assumption. cs2_close.
    + match goal with BC: (m Ⓑ[l ⊕ k] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (m Ⓑ[r ⊕ k] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (k =? n - 1) = false |- _ => apply N.eqb_neq in BC; rename BC into KE end.
      match goal with BC: (m Ⓑ[l ⊕ k] =? m Ⓑ[r ⊕ k]) = true |- _ => apply N.eqb_eq in BC; rename BC into EQ end.
      exists (k + 1). conj_tac.
      * clear - KN KE; lia.
      * apply ceq_succ; try assumption. rewrite EQ. reflexivity.
      * f_equal. pure_lia.
      * f_equal. pure_lia.
      * cs2_close.
    + match goal with BC: (m Ⓑ[l ⊕ k] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (m Ⓑ[r ⊕ k] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (k =? n - 1) = false |- _ => apply N.eqb_neq in BC; rename BC into KE end.
      match goal with BC: (m Ⓑ[l ⊕ k] =? m Ⓑ[r ⊕ k]) = false |- _ => apply N.eqb_neq in BC end.
      exists k. conj_tac. clear - KN KE; lia. cs2_close.
  - destruct PRE as [k [KN [CQ [NL0 [NR0 [NE [FR [RDI [RBX [RBP [R12 [RSP CS]]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strncasecmp_program _ _ _ _ s2 nil _ s1 t MDL1 strncasecmp_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strncasecmp_program tolower_amd64 _ _ (tolower_invs s2 (s2 R_RDI)) tolower_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold tolower_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply tolower_correct; first [ apply pf2sub_refl | assumption | reflexivity ].
    + intros a s t' NC. unfold strncasecmp_invs, strncasecmp_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strncasecmp_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [MEM' [RSP' CS']]].
      unfold s2 in RAX', MEM', RSP', CS'.
      rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM'.
      rewrite !update_frame in RAX' by discriminate. rewrite RDI, N.mod_small in RAX' by apply byte_lt.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      assert (KN': k < n) by (clear - KN; lia).
      repeat x64_step.
      exists k. split. exact KN. split. exact CQ. split. exact NL0. split. exact NR0.
      split. apply frm48_ra, FR.
      split. rewrite ?C1, ?RBP. exact (frm48_byte s0 m _ r n k (frm48_ra _ _ _ _ FR) OVr KN').
      split. unfold tl. apply N.mod_small, tl_byte.
      split. rewrite ?C0. sassumption. split. rewrite ?C1. sassumption. split. rewrite ?C2. sassumption.
      split. reflexivity.
      destruct CS as (B4 & B5). unfold cs2. reg. rewrite ?C4, ?C5. repeat split; assumption.
  - destruct PRE as [k [KN [CQ [NL0 [NR0 [FR [RDI [R13 [RBX [RBP [R12 [RSP CS]]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strncasecmp_program _ _ _ _ s2 nil _ s1 t MDL1 strncasecmp_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strncasecmp_program tolower_amd64 _ _ (tolower_invs s2 (s2 R_RDI)) tolower_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold tolower_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply tolower_correct; first [ apply pf2sub_refl | assumption | reflexivity ].
    + intros a s t' NC. unfold strncasecmp_invs, strncasecmp_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strncasecmp_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [MEM' [RSP' CS']]].
      unfold s2 in RAX', MEM', RSP', CS'.
      rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM'.
      rewrite !update_frame in RAX' by discriminate. rewrite RDI, N.mod_small in RAX' by apply byte_lt.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      assert (KN': k < n) by (clear - KN; lia).
      repeat x64_step.
      all: change (tolower_spec (m Ⓑ[r ⊕ k])) with (tl (m Ⓑ[r ⊕ k])) in *.
      all: rewrite ?C3, ?R13 in *.
      all: rewrite (N.mod_small (tl (m Ⓑ[l ⊕ k]))), (N.mod_small (tl (m Ⓑ[r ⊕ k]))) in * by apply tl_byte.
      * match goal with BC: (tl _ =? tl _) = true |- _ => apply N.eqb_eq in BC; rename BC into EQ end.
        exists (k + 1). split. clear - KN; lia. split. exact (ceq_succ m l r k CQ NL0 NR0 EQ).
        split. apply frm48_ra, FR.
        split. rewrite ?C0, RBX, ?N.add_mod_idemp_r by discriminate. f_equal. pure_lia.
        split. rewrite ?C1, RBP, ?N.add_mod_idemp_r by discriminate. f_equal. pure_lia.
        split. rewrite ?C2. sassumption. split. reflexivity.
        destruct CS as (B4 & B5). unfold cs2. reg. rewrite ?C4, ?C5. repeat split; assumption.
      * match goal with BC: (tl _ =? tl _) = false |- _ => apply N.eqb_neq in BC; rename BC into NE end.
        exists k. split. exact KN'. split. exact CQ. split. right. right. right. exact NE.
        split. apply frm48_ra, FR.
        split. rewrite ?C0, ?RBX. rewrite <- ?(getmem_mod_l _ _ _ _ (l + k)).
          exact (frm48_byte s0 m _ l n k (frm48_ra _ _ _ _ FR) OVl KN').
        split. rewrite ?C1. sassumption. split. reflexivity.
        destruct CS as (B4 & B5). unfold cs2. reg. rewrite ?C4, ?C5. repeat split; assumption.
  - destruct PRE as [k [KN [CQ [CST [FR [RDI [RBP [RSP CS]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strncasecmp_program _ _ _ _ s2 nil _ s1 t MDL1 strncasecmp_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strncasecmp_program tolower_amd64 _ _ (tolower_invs s2 (s2 R_RDI)) tolower_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold tolower_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply tolower_correct; first [ apply pf2sub_refl | assumption | reflexivity ].
    + intros a s t' NC. unfold strncasecmp_invs, strncasecmp_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strncasecmp_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [MEM' [RSP' CS']]].
      unfold s2 in RAX', MEM', RSP', CS'.
      rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM'.
      rewrite !update_frame in RAX' by discriminate. rewrite RDI, N.mod_small in RAX' by apply byte_lt.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      repeat x64_step.
      change (tolower_spec (m Ⓑ[l ⊕ k])) with (tl (m Ⓑ[l ⊕ k])) in *.
      rewrite (N.mod_small (tl (m Ⓑ[l ⊕ k]))) in * by apply tl_byte.
      exists k. split. exact KN. split. exact CQ. split. exact CST.
      split. apply frm48_ra, FR.
      split. rewrite ?C1, ?RBP. rewrite <- ?(getmem_mod_l _ _ _ _ (r + k)).
        exact (frm48_byte s0 m _ r n k (frm48_ra _ _ _ _ FR) OVr KN).
      split. reflexivity. split. reflexivity.
      destruct CS as (B4 & B5). unfold cs2. reg. rewrite ?C4, ?C5. repeat split; assumption.
  - destruct PRE as [k [KN [CQ [CST [FR [RDI [RBX [RSP CS]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strncasecmp_program _ _ _ _ s2 nil _ s1 t MDL1 strncasecmp_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strncasecmp_program tolower_amd64 _ _ (tolower_invs s2 (s2 R_RDI)) tolower_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold tolower_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply tolower_correct; first [ apply pf2sub_refl | assumption | reflexivity ].
    + intros a s t' NC. unfold strncasecmp_invs, strncasecmp_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strncasecmp_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX' [MEM' [RSP' CS']]].
      unfold s2 in RAX', MEM', RSP', CS'.
      rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM'.
      rewrite !update_frame in RAX' by discriminate. rewrite RDI, N.mod_small in RAX' by apply byte_lt.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      pose proof (frm48_ra _ _ _ 0x165b20 FR) as FR'.
      destruct FR' as [FB _]. destruct FR as [_ [T8 [T16 [T24 T32]]]].
      repeat x64_step.
      change (tolower_spec (m Ⓑ[r ⊕ k])) with (tl (m Ⓑ[r ⊕ k])) in *.
      rewrite ?C0, ?RBX in *.
      rewrite ?T8, ?T16, ?T24, ?T32.
      split. right. exists k. split. exact KN. split. exact CQ. split. exact CST. reflexivity.
      split. intros b B. apply FB, B.
      split. apply N.mod_small. exact RB.
      destruct CS as (B4 & B5). unfold callee_saved_eq. reg. rewrite ?C4, ?C5.
      repeat split; sassumption.
Qed.

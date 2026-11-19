(* strcasestr -- locate a substring ignoring case (musl x86_64, C),
   composed with strlen and strncasecmp (-> tolower)

   SEMANTICS
   ---------
   musl's strcasestr (src/string/strcasestr.c) is

       char *strcasestr(const char *h, const char *n)
       {
           size_t l = strlen(n);
           for (; *h; h++) if (!strncasecmp(h, n, l)) return (char * )h;
           return 0;
       }

   The binary returns h at once when l = 0 (strncasecmp(h, n, 0) is 0), so
   that test is hoisted out of the loop.  Both CALLs (strlen 0x1348c0,
   strncasecmp 0x165ab9) are cuts composed with call_leaf_ni.

   SPECIFICATION (man 3 strcasestr, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------------
     char *strcasestr(const char *haystack, const char *needle);
     strcasestr finds the first occurrence of the substring needle in the
     string haystack, ignoring the case of both arguments; the terminating
     null bytes are not compared.  It returns a pointer to the beginning of
     the substring, or NULL if it is not found.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strcasestr at 0x65949, strlen at 0x348c0, strncasecmp at 0x65ab9,
            tolower at 0x41924 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strcasestr_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = h, RSI = n; RSP = rsp; m = memory.  Precondition (cs_ok):
            n is a string of length L and h a string of length Lh, with n's
            L+1 bytes and h's Lh+L+1 bytes outside the 80 bytes below rsp
            (strncasecmp reads up to L bytes at each h+i).
   Output:  At the RET (0x16598b): L = 0 and RAX = h; or L >= 1 and there is
            I such that for i < I, h[i] <> 0 and the L bytes at h+i do not
            match n ignoring case (imatch), and either h[I] = 0 and RAX = 0,
            or h[I] <> 0, they match at h+I and RAX = h+I.  Nothing outside
            the 80 bytes below rsp changes; RSP = rsp; RBX, RBP, R12-R15 are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strcasestr_amd64 CoqEtTu.programs.strlen_amd64
               CoqEtTu.programs.strncasecmp_amd64 CoqEtTu.programs.tolower_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_ctype.
Require Import CoqEtTu.proofs.ctype_proof CoqEtTu.proofs.strcasecmp_proof CoqEtTu.proofs.strncasecmp_proof
               CoqEtTu.proofs.strlen_proof.
Open Scope N.

Definition strcasestr_program : program :=
  updateall2 strcasestr_amd64 (updateall2 strlen_amd64 strncasecmp_program).

Theorem strcasestr_welltyped: welltyped_prog x64typctx strcasestr_amd64.
Proof. exact strcasestr_amd64.welltyped. Qed.

Lemma strcasestr_program_welltyped: welltyped_prog x64typctx strcasestr_program.
Proof.
  intros s a. unfold strcasestr_program, updateall2 at 1, updateall.
  destruct (updateall2 strlen_amd64 strncasecmp_program s a) as [[sz q]|] eqn:SL.
  - unfold updateall2, updateall in SL. destruct (strncasecmp_program s a) as [[sz' q']|] eqn:SL2.
    + inversion SL; subst. pose proof (strncasecmp_program_welltyped s a) as WT. rewrite SL2 in WT. exact WT.
    + pose proof (strlen_welltyped s a) as WT. rewrite SL in WT. exact WT.
  - apply strcasestr_welltyped.
Qed.

Lemma strlen_in_cs: strlen_amd64 ⊆2 strcasestr_program.
Proof.
  intros s a insn SC. unfold strcasestr_program. apply subset_updateall2.
  unfold strncasecmp_program, updateall2, updateall.
  destruct (tolower_amd64 s a) eqn:T.
  - exfalso. revert SC T. unfold strlen_amd64, tolower_amd64.
    repeat first
    [ discriminate
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - destruct (strncasecmp_amd64 s a) eqn:T2; [|exact SC].
    exfalso. revert SC T2. unfold strlen_amd64, strncasecmp_amd64.
    repeat first
    [ discriminate
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma ncase_in_cs: strncasecmp_program ⊆2 strcasestr_program.
Proof. intros s a insn H. unfold strcasestr_program. apply subset_updateall2, subset_updateall2, H. Qed.

Lemma ncase_in_np: strncasecmp_amd64 ⊆2 strncasecmp_program.
Proof.
  intros s a insn SC. unfold strncasecmp_program, updateall2, updateall.
  destruct (tolower_amd64 s a) eqn:T; [|exact SC].
  exfalso. revert SC T. unfold strncasecmp_amd64, tolower_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

(* the L bytes at a match those at b ignoring case: strncasecmp(a, b, L) = 0 *)
Definition imatch (m:memory) (a b L:N) :=
  exists K, K < L /\ ceq m a b K /\ cstopn m a b L K /\ tl (m Ⓑ[a ⊕ K]) = tl (m Ⓑ[b ⊕ K]).

Definition cs_ok (m h n rsp:N) :=
  exists L Lh, nilfree m n L /\ m Ⓑ[n ⊕ L] = 0 /\ nilfree m h Lh /\ m Ⓑ[h ⊕ Lh] = 0 /\
    ~ overlap 64 n (L + 1) (rsp ⊖ 80) 80 /\ ~ overlap 64 h (Lh + L + 1) (rsp ⊖ 80) 80.

Definition strcasestr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x16598b => true
  | _ => false end | _ => false end.

Definition strcasestr_post (s0:store) (m h n:N) (s:store) :=
  (exists L, nilfree m n L /\ m Ⓑ[n ⊕ L] = 0 /\
    ((L = 0 /\ s R_RAX = h) \/
     (1 <= L /\ exists I, (forall i, i < I -> m Ⓑ[h ⊕ i] <> 0 /\ ~ imatch m (h ⊕ i) n L) /\
        ((m Ⓑ[h ⊕ I] = 0 /\ s R_RAX = 0) \/
         (m Ⓑ[h ⊕ I] <> 0 /\ imatch m (h ⊕ I) n L /\ s R_RAX = h ⊕ I))))) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 80 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition frm80 (s0:store) (m M:memory) :=
  (forall b, 80 <= msub 64 b (s0 R_RSP ⊖ 80) -> M Ⓑ[b] = m Ⓑ[b]) /\
  M Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R12 /\ M Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBP /\ M Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBX.

Definition mpush3 (s0:store) (m:N) :=
  m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R12] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBX].

Definition cs3 (s0 s:store) := s R_R13 = s0 R_R13 /\ s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

(* searched so far: positions 0..i-1 are nonzero and do not match *)
Definition srch (m:memory) (h n L i:N) := forall j, j < i -> m Ⓑ[h ⊕ j] <> 0 /\ ~ imatch m (h ⊕ j) n L.

Definition strcasestr_invs (s0:store) (m h n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165949 => Some (s V_MEM64 = m /\ s R_RDI = h /\ s R_RSI = n /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165956 => Some (s V_MEM64 = mpush3 s0 m /\ s R_RDI = n /\ s R_RBX = h /\ s R_RBP = n /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165963 => Some (exists L i, nilfree m n L /\ m Ⓑ[n ⊕ L] = 0 /\ 1 <= L /\ srch m h n L i /\
                      frm80 s0 m (s V_MEM64) /\ s R_RBX = h ⊕ i /\ s R_RBP = n /\ s R_R12 = L /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x165971 => Some (exists L i, nilfree m n L /\ m Ⓑ[n ⊕ L] = 0 /\ 1 <= L /\ srch m h n L i /\
                      m Ⓑ[h ⊕ i] <> 0 /\
                      frm80 s0 m (s V_MEM64) /\ s R_RDI = h ⊕ i /\ s R_RSI = n /\ s R_RDX = L /\
                      s R_RBX = h ⊕ i /\ s R_RBP = n /\ s R_R12 = L /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ cs3 s0 s)
  | 0x16598b => Some (strcasestr_post s0 m h n s)
  | _ => None
  end | _ => None end.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.
Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

(* ---- facts ---- *)

Lemma qs: forall rsp a b, ((a + 8 <=? b) && (b <=? 80) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma frm80_init:
  forall s0 m, s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 -> frm80 s0 m (mpush3 s0 m).
Proof.
  intros s0 m B1 B2 B3. unfold mpush3. split; [|split; [|split]].
  - intros b B.
    rewrite (stack_store_frame _ (s0 R_RSP) 24 _ b 80) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 80) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 80) by (assumption || lia).
    reflexivity.
  - rewrite getmem_noverlap by exact (qs _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qs _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qs _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma frm80_ra: forall s0 m M v, frm80 s0 m M -> frm80 s0 m (M [Ⓠs0 R_RSP ⊖ 32 := v]).
Proof.
  intros s0 m M v [F [S8 [S16 S24]]]. split; [|split; [|split]].
  - intros b B. rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 80) by (assumption || lia). apply F, B.
  - rewrite getmem_noverlap by exact (qs _ 8 32 eq_refl). exact S8.
  - rewrite getmem_noverlap by exact (qs _ 16 32 eq_refl). exact S16.
  - rewrite getmem_noverlap by exact (qs _ 24 32 eq_refl). exact S24.
Qed.

Lemma f80_48: forall b rsp, 80 <= msub 64 b (rsp ⊖ 80) -> 48 <= msub 64 b (rsp ⊖ 32 ⊖ 48).
Proof. intros. mlia. Qed.

Lemma slot80: forall a rsp j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32) ->
  msub 64 a (rsp ⊖ j) < 8 -> 48 <= msub 64 a (rsp ⊖ 32 ⊖ 48).
Proof. intros a rsp j J A. destruct J as [J|[J|[J|J]]]; subst j; mlia. Qed.

Lemma frm80_after:
  forall s0 m M M', frm80 s0 m M -> stack_frame M M' (s0 R_RSP ⊖ 32) 48 -> frm80 s0 m M'.
Proof.
  intros s0 m M M' [F [S8 [S16 S24]]] SF. split; [|split; [|split]].
  - intros b B. rewrite (SF b (f80_48 b _ B)). apply F, B.
  - rewrite <- S8. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot80 a _ 8). left; reflexivity. exact A.
  - rewrite <- S16. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot80 a _ 16). right; left; reflexivity. exact A.
  - rewrite <- S24. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot80 a _ 24). right; right; left; reflexivity. exact A.
Qed.

Lemma ra_after80:
  forall M M' rsp v, stack_frame M M' (rsp ⊖ 32) 48 -> M Ⓠ[rsp ⊖ 32] = v -> M' Ⓠ[rsp ⊖ 32] = v.
Proof.
  intros M M' rsp v SF V. rewrite <- V. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply SF. apply (slot80 a _ 32). right; right; right; reflexivity. exact A.
Qed.

Lemma frm80_byte:
  forall s0 m M x n i, frm80 s0 m M -> ~ overlap 64 x n (s0 R_RSP ⊖ 80) 80 -> i < n ->
  M Ⓑ[x ⊕ i] = m Ⓑ[x ⊕ i].
Proof.
  intros s0 m M x n i [F _] NOV I. apply F.
  destruct (N.le_gt_cases 80 (msub 64 (x ⊕ i) (s0 R_RSP ⊖ 80))) as [H|H]. exact H. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) (s0 R_RSP ⊖ 80)). split. exact I. split. exact H. mlia.
Qed.

Lemma frame80: forall s0 m M, frm80 s0 m M -> stack_frame m M (s0 R_RSP) 80.
Proof. intros s0 m M [F _] b B. apply F, B. Qed.

Lemma sub80_48: forall x L rsp, ~ overlap 64 x L (rsp ⊖ 80) 80 -> ~ overlap 64 x L (rsp ⊖ 32 ⊖ 48) 48.
Proof.
  intros x L rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. exact I. split. lia.
  rewrite E. f_equal. f_equal. mlia.
Qed.

Lemma nov_shift1: forall a n X F k n', ~ overlap 64 a n X F -> k + n' <= n -> ~ overlap 64 (a ⊕ k) n' X F.
Proof.
  intros a n X F k n' NOV K [i [j [I [J E]]]]. apply NOV. exists (k + i), j.
  split. lia. split. exact J. rewrite <- E. mlia.
Qed.

Lemma add_mod_assoc: forall h i k, (h ⊕ i) ⊕ k = h ⊕ (i + k).
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia. Qed.

Lemma nilfree_unique':
  forall m p a b, nilfree m p a -> m Ⓑ[p ⊕ a] = 0 -> nilfree m p b -> m Ⓑ[p ⊕ b] = 0 -> a = b.
Proof.
  intros m p a b NA ZA NB ZB. destruct (N.lt_trichotomy a b) as [H|[H|H]].
  - exfalso. exact (NB a H ZA).
  - exact H.
  - exfalso. exact (NA b H ZB).
Qed.

Lemma srch_len: forall m h n L i Lh, srch m h n L i -> m Ⓑ[h ⊕ Lh] = 0 -> i <= Lh.
Proof.
  intros m h n L i Lh SR Z. destruct (N.le_gt_cases i Lh) as [H|H]. exact H.
  exfalso. exact (proj1 (SR Lh H) Z).
Qed.

Lemma nov_sub: forall a n X F n', ~ overlap 64 a n X F -> n' <= n -> ~ overlap 64 a n' X F.
Proof. intros a n X F n' NOV K [i [j [I [J E]]]]. apply NOV. exists i, j. split. lia. split; assumption. Qed.

Lemma ceq_agree: forall (M m:memory) l r K,
  (forall k, k <= K -> M Ⓑ[l ⊕ k] = m Ⓑ[l ⊕ k] /\ M Ⓑ[r ⊕ k] = m Ⓑ[r ⊕ k]) -> ceq M l r K -> ceq m l r K.
Proof.
  intros M m l r K AG C i I. destruct (AG i ltac:(lia)) as [A1 A2]. rewrite <- A1, <- A2. apply C, I.
Qed.

Lemma cstopn_agree: forall (M m:memory) l r n K,
  M Ⓑ[l ⊕ K] = m Ⓑ[l ⊕ K] -> M Ⓑ[r ⊕ K] = m Ⓑ[r ⊕ K] -> cstopn M l r n K -> cstopn m l r n K.
Proof. intros M m l r n K A1 A2 C. unfold cstopn, cstop in *. rewrite <- A1, <- A2. exact C. Qed.

(* the stop index of a case-insensitive comparison is unique *)
Lemma ncase_unique: forall m a b L K K', K < L -> K' < L ->
  ceq m a b K -> cstopn m a b L K -> ceq m a b K' -> cstopn m a b L K' -> K = K'.
Proof.
  intros m a b L K K' KL KL' C1 S1 C2 S2.
  destruct (N.lt_trichotomy K K') as [H|[H|H]]; [|exact H|].
  - exfalso. destruct (C2 K H) as [A [B T]]. destruct S1 as [S1|[S1|[S1|S1]]]; [lia|contradiction..].
  - exfalso. destruct (C1 K' H) as [A [B T]]. destruct S2 as [S2|[S2|[S2|S2]]]; [lia|contradiction..].
Qed.

Lemma msub32_eq0: forall x y, x < 2^32 -> y < 2^32 -> (msub 32 x y =? 0) = (x =? y).
Proof.
  intros x y X Y. destruct (N.eqb_spec x y) as [E|E].
  - subst. apply N.eqb_eq. unfold msub. change (2^32) with 4294967296 in *. lia.
  - apply N.eqb_neq. intro H. apply E. unfold msub in H. change (2^32) with 4294967296 in *. lia.
Qed.

Theorem strcasestr_correct:
  forall prog s t s' x' m h n
         (STRCASESTR: strcasestr_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (STRNCASECMP: strncasecmp_amd64 ⊆2 prog) (TOLOWER: tolower_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165949, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (H: s R_RDI = h) (Nd: s R_RSI = n)
         (OK: cs_ok m h n (s R_RSP)),
  satisfies_all prog (strcasestr_invs s m h n) strcasestr_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m h n STRCASESTR STRLEN STRNCASECMP TOLOWER ENTRY MDL MEM H Nd OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (HB: h < 2^64) by (rewrite <- H; apply (MDL R_RDI 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nd; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strcasestr_program).
    unfold strcasestr_program, strncasecmp_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strcasestr_invs.
    unfold strcasestr_program, strncasecmp_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m h n MDL MEM H Nd OK RB RBXB RBPB R12B HB NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcasestr_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B HB NB. rename t1 into t.
  destruct OK as (L & Lh & NL & ZL & NH & ZH & OVn & OVh).
  pose proof (frm80_init s0 m R12B RBPB RBXB) as FR0.
  assert (LB: L < 2^64) by exact (nilfree_bound m n L NL ZL).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [Hd [Nd [RSP CS]]]].
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5).
    repeat x64_step.
    all: rewrite ?B0, ?B1, ?B2 in *; fold (mpush3 s0 m) in *.
    conj_tac. unfold cs3; repeat split; reg; sassumption.
  - (* call strlen(n) *)
    destruct PRE as [MEM [RDI [RBX [RBP [RSP CS]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcasestr_program _ _ _ _ s2 nil _ s1 t MDL1 strcasestr_program_welltyped).
    intro MDL2.
    pose proof (frm80_ra _ _ _ 0x16595b FR0) as FR2.
    eapply (call_leaf_ni strcasestr_program strlen_amd64 _ _ (strlen_invs s2 (s2 V_MEM64) n) strlen_exit).
    + exact strlen_in_cs.
    + intros a s t' EXIT NOCODE. unfold strlen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s''] START. apply strlen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
    + intros a s t' NC. unfold strcasestr_invs, strcasestr_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcasestr_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [RAX [NF Z]]] [MEM' [RSP' CS']]].
      assert (S2M: s2 V_MEM64 = mpush3 s0 m [Ⓠs0 R_RSP ⊖ 32 := 0x16595b]) by (unfold s2; reg; sreflexivity).
      rewrite S2M in MEM', NF, Z.
      assert (KE: k = L).
      { apply (nilfree_unique' _ n k L NF Z).
        - intros i I. rewrite (frm80_byte _ _ _ _ (L + 1) _ FR2 OVn) by (clear - I; lia). apply NL, I.
        - rewrite (frm80_byte _ _ _ _ (L + 1) _ FR2 OVn) by (clear; lia). exact ZL. }
      subst k.
      destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
      unfold s2 in D0, D1, D2, D3, D4, D5, RSP'. rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
      rewrite !update_frame, update_updated in RSP' by discriminate.
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 32] = 0x16595b) by (rewrite MEM'; rewrite getmem_setmem by discriminate; reflexivity).
      assert (FR3: frm80 s0 m (s' V_MEM64)) by (rewrite MEM'; exact FR2).
      x64_step. try rewrite RA. repeat x64_step.
      all: pose proof FR0 as [_ [T8 [T16 T24]]].
      all: pose proof CS as (B3 & B4 & B5).
      * match goal with BC: (L =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into L0 end.
        split. exists L. split. exact NL. split. exact ZL. left. split. exact L0. exact RBX.
        split. exact (frame80 _ _ _ FR2). split. apply N.mod_small, RB.
        unfold callee_saved_eq; repeat split; reg; first [sassumption | (rewrite ?D3, ?D4, ?D5; sassumption)].
      * match goal with BC: (L =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into L0 end.
        exists L, 0. split. exact NL. split. exact ZL. split. clear - L0; lia.
        split. intros j J. exfalso. clear - J; lia.
        split. exact FR2.
        split. rewrite D0, RBX, N.add_0_r. symmetry. apply N.mod_small, HB.
        split. rewrite D1. exact RBP.
        split. reflexivity. split. reflexivity.
        unfold cs3; repeat split; reg; rewrite ?D3, ?D4, ?D5; sassumption.
  - destruct PRE as [L' [i [NL' [ZL' [L1 [SR [FR [RBX [RBP [R12 [RSP CS]]]]]]]]]]].
    assert (LE: L' = L) by exact (nilfree_unique' m n L' L NL' ZL' NL ZL). rewrite LE in *. clear LE NL' ZL'.
    assert (BI: forall k, k <= Lh -> s1 V_MEM64 Ⓑ[h ⊕ k] = m Ⓑ[h ⊕ k])
      by (intros k K; apply (frm80_byte _ _ _ _ (Lh + L + 1) _ FR OVh); clear - K; lia).
    repeat x64_step.
    all: assert (IL: i <= Lh) by exact (srch_len m h n L i Lh SR ZH).
    all: assert (BI': s1 V_MEM64 Ⓑ[h + i] = m Ⓑ[h ⊕ i]) by (rewrite <- getmem_mod_l; exact (BI i IL)).
    all: match goal with BC: (_ =? 0) = _ |- _ => rewrite BI' in BC end.
    all: pose proof FR as [_ [T8 [T16 T24]]].
    all: pose proof CS as (B3 & B4 & B5).
    + match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into Z0 end.
      split. exists L. split. exact NL. split. exact ZL. right. split. exact L1.
        exists i. split. exact SR. left. split. exact Z0. reflexivity.
      split. exact (frame80 _ _ _ FR). split. apply N.mod_small, RB.
      unfold callee_saved_eq; repeat split; reg; sassumption.
    + match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into NZ end.
      exists L, i. split. exact NL. split. exact ZL. split. exact L1. split. exact SR. split. exact NZ.
      split. exact FR. unfold cs3. repeat split; reg; first [reflexivity | sassumption].
  - (* call strncasecmp(h+i, n, L) *)
    destruct PRE as [L' [i [NL' [ZL' [L1 [SR [NZ [FR [RDI [RSI [RDX [RBX [RBP [R12 [RSP CS]]]]]]]]]]]]]]].
    assert (LE: L' = L) by exact (nilfree_unique' m n L' L NL' ZL' NL ZL).
    rewrite LE in *. clear LE NL' ZL'.
    assert (IL: i <= Lh) by exact (srch_len m h n L i Lh SR ZH).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcasestr_program _ _ _ _ s2 nil _ s1 t MDL1 strcasestr_program_welltyped).
    intro MDL2.
    pose proof (frm80_ra _ _ _ 0x165976 FR) as FR2.
    assert (S2M: s2 V_MEM64 = s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x165976]) by (unfold s2; reg; sreflexivity).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 32) by (unfold s2; reg; reflexivity).
    assert (AG: forall k, k <= L -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x165976]) Ⓑ[(h ⊕ i) ⊕ k] = m Ⓑ[(h ⊕ i) ⊕ k] /\
                                 (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 32 := 0x165976]) Ⓑ[n ⊕ k] = m Ⓑ[n ⊕ k]).
    { intros k K. split.
      - rewrite add_mod_assoc. apply (frm80_byte _ _ _ _ (Lh + L + 1) _ FR2 OVh). clear - K IL; lia.
      - apply (frm80_byte _ _ _ _ (L + 1) _ FR2 OVn). clear - K; lia. }
    eapply (call_leaf_ni strcasestr_program strncasecmp_program _ _
              (strncasecmp_invs s2 (s2 V_MEM64) (h ⊕ i) n L) strncasecmp_exit).
    + exact ncase_in_cs.
    + intros a s t' EXIT NOCODE. unfold strncasecmp_invs.
      unfold strncasecmp_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s''] START. apply strncasecmp_correct; first
        [ apply ncase_in_np | apply subset_updateall2 | reflexivity | assumption
        | (unfold s2; reg; first [reflexivity | assumption]) | idtac ].
      rewrite S2R. split.
      * apply sub80_48. apply (nov_shift1 _ (Lh + L + 1)). exact OVh. clear - IL; lia.
      * apply sub80_48. apply (nov_sub _ (L + 1)). exact OVn. clear; lia.
    + intros a s t' NC. unfold strcasestr_invs, strcasestr_exit.
      unfold strncasecmp_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i'] s] t'; reflexivity.
    + intros [[a|i'] s] t'; reflexivity.
    + intros a s t' X. unfold strncasecmp_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (strncasecmp_exit _) eqn:EX; [|destruct PRE].
      unfold strncasecmp_exit in EX. addr_cases EX.
      all: set (hb := h ⊕ i) in PRE.
      all: simpl in PRE.
      all: unfold hb in PRE; clear hb.
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcasestr_program_welltyped).
      all: intro MDL3.
      all: destruct PRE as [[[L0 _]|[K [KL [CE [CST RAXK]]]]] [SF [RSP' CS']]];
             [exfalso; clear - L0 L1; lia|].
      all: rewrite S2M in CE, CST, RAXK, SF. all: rewrite S2R in SF, RSP'.
      all: pose proof (ceq_agree _ m _ _ K (fun k Hk => AG k ltac:(lia)) CE) as CEm.
      all: destruct (AG K ltac:(lia)) as [A1 A2].
      all: pose proof (cstopn_agree _ m _ _ L K A1 A2 CST) as CSTm.
      all: rewrite A1, A2 in RAXK.
      all: pose proof (frm80_after _ _ _ _ FR2 SF) as FR3.
      all: pose proof (ra_after80 _ _ _ _ SF ltac:(rewrite getmem_setmem by discriminate; reflexivity)) as RA.
      all: destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
      all: unfold s2 in D0, D1, D2, D3, D4, D5.
      all: rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
      all: x64_step; try rewrite RA; repeat x64_step.
      all: match goal with BC: (_ =? _) = _ |- _ =>
             rewrite (N.mod_small (tl (m Ⓑ[(h ⊕ i) ⊕ K]))), (N.mod_small (tl (m Ⓑ[n ⊕ K]))) in BC by apply tl_byte end.
      all: pose proof FR3 as [_ [T8 [T16 T24]]].
      all: pose proof CS as (B3 & B4 & B5).
      all: lazymatch goal with
           | BC: (_ =? _) = true |- _ => apply N.eqb_eq in BC; rename BC into TE;
               split; [exists L; split; [exact NL |]; split; [exact ZL |]; right; split; [exact L1 |];
                 exists i; split; [exact SR |]; right; split; [exact NZ |];
                 split; [exists K; split; [exact KL |]; split; [exact CEm |]; split; [exact CSTm | exact TE] |];
                 exact RBX |];
               split; [exact (frame80 _ _ _ FR3) |]; split; [apply N.mod_small, RB |];
               unfold callee_saved_eq; repeat split; reg; first [sassumption | (rewrite ?D3, ?D4, ?D5; sassumption)]
           | BC: (_ =? _) = false |- _ => apply N.eqb_neq in BC; rename BC into TNE;
               exists L, (i + 1); split; [exact NL |]; split; [exact ZL |]; split; [exact L1 |];
               split;
               [ intros j J; destruct (N.eq_dec j i) as [->|NE];
                 [ split; [exact NZ |]; intros [K' [KL' [CE' [CST' TE']]]];
                   pose proof (ncase_unique m _ _ L K' K KL' KL CE' CST' CEm CSTm) as KE;
                   rewrite KE in TE'; exact (TNE TE')
                 | apply SR; clear - J NE; lia ] |];
               split; [exact FR3 |];
               split; [rewrite RBX, N.add_mod_idemp_r by discriminate; f_equal; clear; lia |];
               split; [rewrite D1; exact RBP |]; split; [rewrite D2; exact R12 |];
               split; [reflexivity |];
               unfold cs3; repeat split; reg; rewrite ?D3, ?D4, ?D5; sassumption
           end.
Qed.

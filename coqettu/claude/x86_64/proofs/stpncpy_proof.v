(* stpncpy -- copy a fixed-size string, zero-padding (musl x86_64, C),
   composed with the hand-written assembly memset

   SEMANTICS
   ---------
   musl's __stpncpy (src/string/stpncpy.c) is

       if (((uintptr_t)s & ALIGN) == ((uintptr_t)d & ALIGN)) {
           for (; ((uintptr_t)s & ALIGN) && n && ( *d=*s); n--, s++, d++);
           if (!n || !*s) goto tail;
           wd=(void * )d; ws=(const void * )s;
           for (; n>=sizeof(size_t) && !HASZERO( *ws);
                  n-=sizeof(size_t), ws++, wd++) *wd = *ws;
           d=(void * )wd; s=(const void * )ws;
       }
       for (; n && ( *d=*s); n--, s++, d++);
   tail:
       memset(d, 0, n);
       return d;

   The binary saves RBX (it holds d+k across the call and is also a scratch
   register in the word loop), and CALLs memset (0x166095, the assembly
   function proved in memset_proof.v) for the zero padding; memset's
   contract (its `filled` memory post) is used through call_leaf_ni.  The
   copy is tracked by `upto` (bytes d[0..k) copied; nothing outside d[0..n)
   changed, relative to the memory after PUSH RBX).

   SPECIFICATION (man 3 stpncpy, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *stpncpy(char dst[restrict .dsize],
                          const char *restrict src, size_t dsize);

     DESCRIPTION
            These functions copy non-null bytes from the string pointed to
            by src into the array pointed to by dst.  If the source has too
            few non-null bytes to fill the destination, the functions pad
            the destination with trailing null bytes.  If the destination
            buffer, limited by its size, isn't large enough to hold the copy,
            the resulting character sequence is truncated.

     RETURN VALUE
            stpncpy()
                   returns a pointer to one after the last character in the
                   destination character sequence.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            stpncpy at 0x24040, memset at 0x66095 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/stpncpy_amd64.v, memset_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dst, RSI = src, RDX = n; RSP = rsp; m = memory; DF clear.
            Precondition (stpncpy_ok): n < 2^63; the n bytes at dst, the n
            bytes at src and the 16 bytes below rsp are pairwise disjoint
            (restrict, plus strncpy's own stack).  src need not be
            terminated within n bytes.
   Output:  At the RET (0x124128) there is K <= n such that src[0..K) are
            nonzero and K = n or src[K] = 0 (K = strnlen(src, n)); RAX =
            dst + K; dst[i] = src[i] for i < K and dst[i] = 0 for K <= i < n;
            every byte outside dst[0..n) and the 16 bytes below rsp is
            unchanged.  RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.stpncpy_amd64 CoqEtTu.programs.memset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_haszero
               CoqEtTu.lib.x64_memcpy_sets CoqEtTu.lib.x64_fill_sets CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.memset_proof.
Open Scope N.

Definition stpncpy_program : program := updateall2 stpncpy_amd64 memset_amd64.

Theorem stpncpy_welltyped: welltyped_prog x64typctx stpncpy_amd64.
Proof. exact stpncpy_amd64.welltyped. Qed.

Lemma stpncpy_program_welltyped: welltyped_prog x64typctx stpncpy_program.
Proof.
  intros s a. unfold stpncpy_program, updateall2, updateall.
  destruct (memset_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (memset_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply stpncpy_welltyped.
Qed.

(* d[0..k) holds s[0..k) and nothing outside d[0..n) differs from m *)
Definition upto (m M d s k n:N) :=
  (forall i, i < k -> M Ⓑ[d ⊕ i] = m Ⓑ[s ⊕ i]) /\
  (forall b, ~ (msub 64 b d < n) -> M Ⓑ[b] = m Ⓑ[b]).

(* the n bytes at d, the n bytes at s and the 16 bytes below rsp are pairwise disjoint *)
Definition stpncpy_ok (d s n rsp:N) :=
  nov d s n /\ ~ overlap 64 d n (rsp ⊖ 16) 16 /\ ~ overlap 64 s n (rsp ⊖ 16) 16 /\ n < 2^63.

Definition stpncpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x124128 => true
  | _ => false end | _ => false end.

(* the source bytes s[0..k) are nonzero *)
Definition nz (m s k:N) := forall i, i < k -> m Ⓑ[s ⊕ i] <> 0.

Definition cs_but_rbx (s0 s:store) :=
  s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
  s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

(* the state shared by every point after PUSH RBX *)
Definition st (s0:store) (m d src n k:N) (s:store) :=
  k <= n /\ upto (m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX]) (s V_MEM64) d src k n /\ nz m src k /\
  s R_RSP = s0 R_RSP ⊖ 8 /\ s R_DF = 0 /\ cs_but_rbx s0 s.

Definition stpncpy_post (s0:store) (m d src n:N) (s:store) :=
  (exists K, K <= n /\ nz m src K /\ (K = n \/ m Ⓑ[src ⊕ K] = 0) /\ s R_RAX = d ⊕ K /\
     (forall i, i < K -> s V_MEM64 Ⓑ[d ⊕ i] = m Ⓑ[src ⊕ i]) /\
     (forall i, K <= i < n -> s V_MEM64 Ⓑ[d ⊕ i] = 0)) /\
  (forall b, ~ (msub 64 b d < n) -> 16 <= msub 64 b (s0 R_RSP ⊖ 16) -> s V_MEM64 Ⓑ[b] = m Ⓑ[b]) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

(* Source bytes inside the n-byte area are untouched by the copy and the push. *)
Lemma src_read:
  forall m M d src n rsp v i, upto (m [Ⓠrsp ⊖ 8 := v]) M d src 0 n -> stpncpy_ok d src n rsp -> i < n ->
  M Ⓑ[src ⊕ i] = m Ⓑ[src ⊕ i].
Proof.
  intros m M d src n rsp v i [_ F] [NOV [ND [NS NB]]] I.
  rewrite F.
  - apply getmem_noverlap. intros [x [y [X [Y E]]]]. apply NS. exists i, (8 + y).
    split. assumption. split. lia. mlia.
  - intro H. apply (NOV (msub 64 (src ⊕ i) d) i H I). rewrite add_msub. apply N.mod_mod. discriminate.
Qed.

Lemma upto_frame0: forall m M d src k n, upto m M d src k n -> upto m M d src 0 n.
Proof. intros m M d src k n [_ F]. split. intros i I. lia. exact F. Qed.

Lemma src_read_q:
  forall m M d src n rsp v k, upto (m [Ⓠrsp ⊖ 8 := v]) M d src 0 n -> stpncpy_ok d src n rsp -> k + 8 <= n ->
  M Ⓠ[src + k] = m Ⓠ[src + k].
Proof.
  intros m M d src n rsp v k U OK K. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE).
  assert (E: a mod 2^64 = (src + (k + msub 64 a (src + k))) mod 2^64) by mlia.
  rewrite <- (getmem_mod_l _ _ _ M a), <- (getmem_mod_l _ _ _ m a), E.
  apply (src_read m M d src n rsp v); assumption || lia.
Qed.

(* One more byte copied. *)
Lemma upto_byte:
  forall m1 M d src k n v, upto m1 M d src k n -> k < n -> n < 2^63 -> v = m1 Ⓑ[src ⊕ k] ->
  upto m1 (setmem 64 LittleE 1 M (d + k) v) d src (k + 1) n.
Proof.
  intros m1 M d src k n v [C F] K NB V. split.
  - intros i I. rewrite byte_setmem_cases by (discriminate || reflexivity).
    destruct (N.ltb_spec (msub 64 (d ⊕ i) (d + k)) 1) as [H|H].
    + assert (i = k) by mlia. subst i.
      replace (msub 64 (d ⊕ k) (d + k)) with 0 by mlia.
      change (xbits v (8*0) (8*0+8)) with (v mod 2^8). rewrite V.
      apply (getmem_mod_r 64 LittleE 1).
    + apply C. destruct (N.eq_dec i k). subst i. exfalso. mlia. lia.
  - intros b B. rewrite byte_setmem_cases by (discriminate || reflexivity).
    destruct (N.ltb_spec (msub 64 b (d + k)) 1) as [H|H].
    + exfalso. apply B. mlia.
    + apply F, B.
Qed.

(* Eight more bytes copied by one word store. *)
Lemma upto_word:
  forall m1 M d src k n, upto m1 M d src k n -> k + 8 <= n -> n < 2^63 ->
  (forall j, j < 8 -> m1 Ⓑ[src ⊕ (k + j)] = M Ⓑ[src ⊕ (k + j)]) ->
  upto m1 (setmem 64 LittleE 8 M (d + k) (M Ⓠ[src + k])) d src (k + 8) n.
Proof.
  intros m1 M d src k n [C F] K NB SR. split.
  - intros i I. rewrite byte_setmem_cases by (discriminate || reflexivity).
    destruct (N.ltb_spec (msub 64 (d ⊕ i) (d + k)) 8) as [H|H].
    + assert (J: msub 64 (d ⊕ i) (d + k) = i - k) by mlia. rewrite J.
      replace (8 * (i - k) + 8) with (8 * (i - k) + 8) by reflexivity.
      rewrite byte_of_getmem by mlia.
      replace ((src + k) ⊕ (i - k)) with (src ⊕ i) by (f_equal; lia).
      specialize (SR (i - k) ltac:(mlia)). replace (k + (i - k)) with i in SR by lia.
      symmetry. exact SR.
    + apply C. mlia.
  - intros b B. rewrite byte_setmem_cases by (discriminate || reflexivity).
    destruct (N.ltb_spec (msub 64 b (d + k)) 8) as [H|H].
    + exfalso. apply B. mlia.
    + apply F, B.
Qed.

Lemma src_read1:
  forall m M d src n rsp v i, upto (m [Ⓠrsp ⊖ 8 := v]) M d src 0 n -> stpncpy_ok d src n rsp -> i < n ->
  M Ⓑ[src + i] = (m [Ⓠrsp ⊖ 8 := v]) Ⓑ[src ⊕ i].
Proof.
  intros m M d src n rsp v i U OK I. rewrite <- getmem_mod_l.
  rewrite (src_read m M d src n rsp v i U OK I).
  destruct OK as [_ [_ [NS _]]]. symmetry. apply getmem_noverlap.
  intros [x [y [X [Y E]]]]. apply NS. exists i, (8 + y). split. assumption. split. lia. mlia.
Qed.

Lemma upto_mono: forall m M d src k j n, upto m M d src k n -> j <= k -> upto m M d src j n.
Proof. intros m M d src k j n [C F] J. split. intros i I. apply C. lia. exact F. Qed.

Lemma nz_succ: forall m src k, nz m src k -> m Ⓑ[src ⊕ k] <> 0 -> nz m src (k + 1).
Proof. intros m src k NZ B i I. destruct (N.lt_ge_cases i k). apply NZ. assumption. replace i with k by lia. exact B. Qed.

Ltac upto_tac :=
  lazymatch goal with
  | |- upto ?m1 (setmem 64 LittleE 1 ?M (?d + ?k) ?v) ?d ?src ?K ?n =>
      first [ apply upto_byte | apply (upto_mono _ _ _ _ (k + 1)); [apply upto_byte | lia] ];
      [ assumption | lia
      | match goal with OK: stpncpy_ok _ _ _ _ |- _ => let H := fresh in destruct OK as [_ [_ [_ H]]]; exact H end
      | eapply src_read1; [eapply upto_frame0; eassumption | eassumption | lia] ]
  | |- upto _ _ _ _ _ _ => assumption
  end.

Lemma land_align8_: forall x, x < 2^64 -> x .& 18446744073709551608 = x - x mod 8.
Proof.
  intros x X.
  assert (E: x - x mod 8 = x >> 3 << 3).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^3) with 8.
    rewrite (N.div_mod x 8) at 1 by discriminate. lia. }
  rewrite E. change 18446744073709551608 with (N.ldiff (N.ones 64) (N.ones 3)).
  apply N.bits_inj. intro i. rewrite N.land_spec, N.ldiff_spec.
  destruct (N.ltb_spec i 3).
  - rewrite (N.ones_spec_low 3 i), N.shiftl_spec_low by lia. cbn [negb].
    rewrite !Bool.andb_false_r. reflexivity.
  - rewrite (N.ones_spec_high 3 i) by lia. rewrite N.shiftl_spec_high, N.shiftr_spec by lia.
    replace (i - 3 + 3) with i by lia. cbn [negb]. rewrite Bool.andb_true_r.
    destruct (N.ltb_spec i 64).
    + rewrite N.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite N.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      destruct x as [|q]. apply N.bits_0.
      apply N.bits_above_log2. apply N.lt_le_trans with 64; [|lia].
      apply N.log2_lt_pow2; [reflexivity|exact X].
Qed.

(* d+i for i < k lies outside memset's range [d+k, d+n) *)
Lemma before_fill: forall d i k n, i < k -> k <= n -> n < 2^63 -> ~ (msub 64 (d ⊕ i) (d ⊕ k) < n - k).
Proof. intros. mlia. Qed.

(* bytes outside [d, d+n) lie outside [d+k, d+n) *)
Lemma outside_fill: forall d b k n, k <= n -> n < 2^63 -> ~ (msub 64 b d < n) -> ~ (msub 64 b (d ⊕ k) < n - k).
Proof. intros. mlia. Qed.

(* bytes of a quadword at rsp-j (j in {8,16}) are outside [d, d+n) *)
Lemma stack_outside_dest: forall d n rsp j a, ~ overlap 64 d n (rsp ⊖ 16) 16 -> (j = 8 \/ j = 16) ->
  msub 64 a (msub 64 rsp j) < 8 -> ~ (msub 64 a d < n).
Proof.
  intros d n rsp j a NOV J A H. apply NOV. exists (msub 64 a d), (16 - j + msub 64 a (msub 64 rsp j)).
  split. exact H. split. lia. mlia.
Qed.

Lemma k8_le: forall k e, k <= e -> e < 2^64 -> k mod 2^64 <> e mod 2^64 -> (e - k) mod 8 = 0 -> k + 8 <= e.
Proof.
  intros k e KE EB NE M. rewrite !N.mod_small in NE by lia.
  assert (e - k <> 0) by lia. pose proof (N.div_mod (e - k) 8 ltac:(discriminate)). nia.
Qed.

Lemma kmod_eq: forall k e, k < 2^64 -> e < 2^64 -> k mod 2^64 = e mod 2^64 -> k = e.
Proof. intros k e K E H. rewrite !N.mod_small in H by assumption. exact H. Qed.

Lemma above_stack_noverlap:
  forall b rsp k, 16 <= msub 64 b (msub 64 rsp 16) -> (k = 8 \/ k = 16) -> ~ overlap 64 b 1 (msub 64 rsp k) 8.
Proof. intros b rsp k B K [x [y [X [Y E]]]]. mlia. Qed.

Lemma area_noverlap:
  forall x n rsp k i, ~ overlap 64 x n (rsp ⊖ 16) 16 -> i < n -> (k = 8 \/ k = 16) ->
  ~ overlap 64 (x ⊕ i) 1 (msub 64 rsp k) 8.
Proof.
  intros x n rsp k i NOV I K [a [y [A [Y E]]]]. apply NOV. exists i, (16 - k + y).
  split. exact I. split. lia. mlia.
Qed.

Lemma fill_addr: forall d k i, k <= i -> (d ⊕ k) ⊕ (i - k) = d ⊕ i.
Proof. intros. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac cs_tac :=
  match goal with
  | CS: cs_but_rbx ?s0 _ |- cs_but_rbx ?s0 _ =>
      let B1 := fresh in let B2 := fresh in let B3 := fresh in let B4 := fresh in let B5 := fresh in
      destruct CS as (B1 & B2 & B3 & B4 & B5); repeat split; reg; sassumption
  | CS: callee_saved_eq ?s0 _ |- cs_but_rbx ?s0 _ =>
      let B0 := fresh in let B1 := fresh in let B2 := fresh in let B3 := fresh in let B4 := fresh in let B5 := fresh in
      destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); repeat split; reg; sassumption
  end.

(* Re-establish st on a stepped state: k bound, memory, nz, RSP, DF, registers. *)
Ltac st_tac :=
  unfold st; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
  [ try lia | reg; try upto_tac | try assumption | reg; try sassumption | reg; try sassumption | cs_tac ].

Definition stpncpy_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x124040 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ s R_DF = 0 /\ callee_saved_eq s0 s)
  (* alignment loop *)
  | 0x124063 => Some (exists k, st s0 m d src n k s /\ s R_RAX = src ⊕ k /\ s R_RCX = d ⊕ k /\
                      s R_RDX = n - k)
  (* a byte is left and the copy is aligned *)
  | 0x124086 => Some (exists k, st s0 m d src n k s /\ k < n /\ s R_RAX = src ⊕ k /\
                      s R_RCX = d ⊕ k /\ s R_RDX = n - k)
  (* word loop *)
  | 0x1240cb => Some (exists k e, st s0 m d src n k s /\ k <= e /\ e <= n /\ n - e < 8 /\
                      (e - k) mod 8 = 0 /\ s R_RAX = src ⊕ k /\ s R_RCX = d ⊕ k /\
                      s R_R10 = src ⊕ n /\ s R_R9 = src ⊕ e /\
                      s R_RBX = 0xfefefefefefefeff /\ s R_R11 = 0x8080808080808080)
  (* final byte loop *)
  | 0x12410c => Some (exists k, st s0 m d src n k s /\ s R_RAX = src ⊕ k /\ s R_RBX = d ⊕ k /\
                      s R_RDX = n - k)
  (* the call to memset(d+k, 0, n-k) *)
  | 0x12411f => Some (exists k, st s0 m d src n k s /\ (k = n \/ m Ⓑ[src ⊕ k] = 0) /\
                      s R_RDI = d ⊕ k /\ s R_RSI = 0 /\ s R_RDX = n - k /\ s R_RBX = d ⊕ k)
  | 0x124128 => Some (stpncpy_post s0 m d src n s)
  | _ => None
  end | _ => None end.

Theorem stpncpy_correct:
  forall prog s t s' x' m d src n
         (STPNCPY: stpncpy_amd64 ⊆2 prog) (MEMSET: memset_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x124040, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (DF: s R_DF = 0) (OK: stpncpy_ok d src n (s R_RSP)),
  satisfies_all prog (stpncpy_invs s m d src n) stpncpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n STPNCPY MEMSET ENTRY MDL MEM D S Nn DF OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RDI 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=stpncpy_program).
    unfold stpncpy_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold stpncpy_invs.
    unfold stpncpy_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src n MDL MEM D S Nn DF OK RB RBXB DB SB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply stpncpy_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB DB SB. rename t1 into t.
  assert (NB: n < 2^63) by (destruct OK as [_ [_ [_ NB]]]; exact NB).
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP [DF CS]]]]]].
    repeat x64_step. all: bc_norm.
    all: pose proof (proj1 CS) as B.
    all: exists 0; split; [st_tac|].
    all: try (rewrite N.add_0_r, N.mod_small by assumption; reflexivity).
    all: try lia.
    all: try (rewrite B; split; [intros i I; lia | reflexivity]).
    all: try (intros i I; lia).
    all: repeat split; try (rewrite N.add_0_r, N.mod_small by assumption; reflexivity);
         try (rewrite N.sub_0_r; assumption).
  - (* alignment loop *)
    destruct PRE as [k [[KN [UP [NZ [RSP [DF CS]]]]] [RAX [RCX RDX]]]].
    repeat x64_step. all: bc_norm.
    all: pose proof (upto_frame0 _ _ _ _ _ _ UP) as UP0.
    all: try (rewrite (src_read m (s1 V_MEM64) d src n (s0 R_RSP) (s0 R_RBX) k) in BC0 by (assumption || mlia64)).
    all: try (rewrite (src_read m (s1 V_MEM64) d src n (s0 R_RSP) (s0 R_RBX) k) in BC1 by (assumption || mlia64)).
    all: try (rewrite <- getmem_mod_l in BC1; rewrite (src_read m (s1 V_MEM64) d src n (s0 R_RSP) (s0 R_RBX) k) in BC1 by (assumption || mlia64)).
    all: lazymatch goal with
    | |- exists _, st _ _ _ _ _ _ _ /\ (_ = _ \/ _) /\ _ =>
        exists k; split; [st_tac; try upto_tac|]; split; [left; lia|]; repeat split
    | |- exists _, st _ _ _ _ _ _ _ /\ _ < _ /\ _ =>
        exists k; split; [st_tac; try upto_tac|]; split; [lia|]; repeat split; reg; try sassumption
    | _ =>
        exists (k + 1); split; [st_tac; try upto_tac; try (apply nz_succ; assumption); lia|];
        split; [f_equal; lia|]; split; [f_equal; lia|];
        rewrite msub_nowrap; rewrite !N.mod_small; mlia64
    end.
  - (* 0x124086 *)
    destruct PRE as [k [[KN [UP [NZ [RSP [DF CS]]]]] [KLT [RAX [RCX RDX]]]]].
    repeat x64_step. all: bc_norm.
    all: pose proof (upto_frame0 _ _ _ _ _ _ UP) as UP0.
    all: try (rewrite <- getmem_mod_l in BC; rewrite (src_read m (s1 V_MEM64) d src n (s0 R_RSP) (s0 R_RBX) k) in BC by (assumption || mlia64)).
    + (* the next byte is the terminator: zero-fill from here *)
      exists k. split; [st_tac|]. split. right. assumption. repeat split; reg; try sassumption.
    + (* enter the word loop *)
      exists k, (k + (n - k .& 18446744073709551608)).
      assert (A: n - k .& 18446744073709551608 = (n - k) - (n - k) mod 8) by (apply land_align8_; mlia64).
      pose proof (N.mod_lt (n - k) 8 ltac:(discriminate)) as ML.
      pose proof (N.div_mod (n - k) 8 ltac:(discriminate)) as DM.
      split; [st_tac|].
      split. lia. split. lia. split. lia.
      split. rewrite A. replace (k + (n - k - (n - k) mod 8) - k) with (8 * ((n - k) / 8)) by lia.
        rewrite N.mul_comm. apply N.Div0.mod_mul.
      split. reflexivity. split. reflexivity.
      split. f_equal. lia. split. f_equal. lia.
      split; reflexivity.
  - (* word loop *)
    destruct PRE as [k [e [[KN [UP [NZ [RSP [DF CS]]]]] [KE [EN [NE [EK [RAX [RCX [R10 [R9 [RBX R11]]]]]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: pose proof (upto_frame0 _ _ _ _ _ _ UP) as UP0.
    all: lazymatch goal with
    | |- exists _ _, _ =>
        (* no zero byte in this word: copy it *)
        assert (K8: k + 8 <= e) by (apply k8_le; [assumption | lia | assumption | assumption]); clear BC;
        rewrite (N.land_comm (_ ⊖ _)) in BC0;
        rewrite (src_read_q m (s1 V_MEM64) d src n (s0 R_RSP) (s0 R_RBX) k UP0 OK) in BC0 by lia;
        exists (k + 8), e; split;
        [ unfold st; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
          [ lia
          | reg; apply upto_word; [assumption | lia | exact NB |];
            intros j J; rewrite (getmem_mod_l _ _ _ (s1 V_MEM64) (src + (k + j)));
            rewrite (src_read1 m (s1 V_MEM64) d src n (s0 R_RSP) (s0 R_RBX) (k + j) UP0 OK) by lia;
            reflexivity
          | intros i I; apply (nilfree_add8 m src k NZ BC0 i I)
          | reg; sassumption | reg; sassumption | cs_tac ] |];
        split; [lia|]; split; [lia|]; split; [lia|];
        split; [rewrite N.sub_add_distr; rewrite <- (N.mod_add (e - k - 8) 1) by discriminate;
                replace (e - k - 8 + 1 * 8) with (e - k) by lia; assumption|];
        split; [f_equal; lia|]; split; [f_equal; lia|]; repeat split
    | _ =>
        (* end of word region, or a zero byte ahead: the byte loop *)
        exists k; split; [st_tac|]; split; [reflexivity|]; split; [reflexivity|];
        rewrite msub_nowrap; rewrite !N.mod_small; mlia64
    end.
  - (* final byte loop *)
    destruct PRE as [k [[KN [UP [NZ [RSP [DF CS]]]]] [RAX [RBX RDX]]]].
    repeat x64_step. all: bc_norm.
    all: pose proof (upto_frame0 _ _ _ _ _ _ UP) as UP0.
    all: try (rewrite <- getmem_mod_l in BC0; rewrite (src_read m (s1 V_MEM64) d src n (s0 R_RSP) (s0 R_RBX) k) in BC0 by (assumption || mlia64)).
    all: lazymatch goal with
    | |- exists _, st _ _ _ _ _ _ _ /\ (_ = _ \/ _) /\ _ =>
        exists k; split; [st_tac|];
        split; [first [left; lia | right; assumption]|]; repeat split; reg; try sassumption
    | _ =>
        exists (k + 1); split; [st_tac; try (apply nz_succ; assumption); lia|];
        split; [f_equal; lia|]; split; [f_equal; lia|];
        rewrite msub_nowrap; rewrite !N.mod_small; mlia64
    end.
  - (* the call memset(d+k, 0, n-k) *)
    destruct PRE as [k [[KN [UP [NZ [RSP [DF CS]]]]] [KS [RDI [RSI [RDX RBX]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps stpncpy_program _ _ _ _ s2 nil _ s1 t MDL1 stpncpy_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni stpncpy_program memset_amd64 _ _
              (memset_invs s2 (s2 V_MEM64) (d ⊕ k) 0 (n - k)) memset_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold memset_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply memset_correct; first
        [ apply pf2sub_refl | assumption | reflexivity
        | (unfold s2; reg; assumption) ].
    + intros a s t' NC. unfold stpncpy_invs, stpncpy_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold memset_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (memset_exit _) eqn:EX; [|destruct PRE].
      unfold memset_exit in EX. addr_cases EX.
      all: simpl in PRE.
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 stpncpy_program_welltyped).
      all: intro MDL3.
      all: destruct PRE as [RAX [RSP' [CS' FL]]].
      all: unfold s2 in *.
      all: rewrite update_updated in FL; replace (N.pos (2^64)) with (2^64) in FL by reflexivity;
           change (0 mod 2^8) with 0 in FL.
      all: rewrite update_frame, update_updated in RSP' by discriminate.
      all: destruct FL as [FZ FF].
      all: pose proof OK as [NOVds [ND [NS _]]].
      all: assert (DSTK: forall j a, (j = 8 \/ j = 16) -> msub 64 a (s0 R_RSP ⊖ j) < 8 ->
                    s' V_MEM64 Ⓑ[a] = (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 16 := 1196324]) Ⓑ[a]) by
             (intros j a J A; apply FF; apply outside_fill; [lia | exact NB |];
              apply (stack_outside_dest d n (s0 R_RSP) j a ND J A)).
      all: assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 1196324).
      all: try (transitivity ((s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 16 := 1196324]) Ⓠ[s0 R_RSP ⊖ 16]);
                [ apply getmem_frame_mem; intros a A; rewrite <- !getmem_1 with (e:=LittleE);
                  apply (DSTK 16); [right; reflexivity | exact A]
                | rewrite getmem_setmem by discriminate; reflexivity ]).
      all: assert (R8: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBX).
      all: try (transitivity ((m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX]) Ⓠ[s0 R_RSP ⊖ 8]);
                [ apply getmem_frame_mem; intros a A; rewrite <- !getmem_1 with (e:=LittleE);
                  rewrite (DSTK 8) by (first [left; reflexivity | exact A]);
                  rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia64);
                  apply (proj2 UP); apply (stack_outside_dest d n (s0 R_RSP) 8 a ND); [left; reflexivity | exact A]
                | rewrite getmem_setmem by discriminate; apply N.mod_small; assumption ]).
      all: x64_step; rewrite RA; repeat x64_step.
      all: assert (RBXv: s' R_RBX = d ⊕ k) by (rewrite (proj1 CS'); reg; exact RBX).
      all: assert (CSb: cs_but_rbx s0 s') by
             (destruct CS' as (_ & B1 & B2 & B3 & B4 & B5); destruct CS as (C1 & C2 & C3 & C4 & C5);
              repeat split; [rewrite B1 | rewrite B2 | rewrite B3 | rewrite B4 | rewrite B5]; reg; assumption).
      all: split; [ exists k; split; [assumption|]; split; [assumption|]; split; [assumption|];
        split; [exact RBXv|]; split;
        [ intros i I; rewrite FF by (apply before_fill; assumption || lia);
          rewrite getmem_noverlap by (apply (area_noverlap d n (s0 R_RSP) 16 i); [assumption | lia | right; reflexivity]);
          rewrite (proj1 UP i I); apply getmem_noverlap;
          apply (area_noverlap src n (s0 R_RSP) 8 i); [assumption | lia | left; reflexivity]
        | intros i [I1 I2]; rewrite <- (fill_addr d k i I1); apply FZ; lia ] |].
      all: split; [ intros b B1 B2; rewrite FF by (apply outside_fill; assumption || lia);
        rewrite getmem_noverlap by (apply above_stack_noverlap; [exact B2 | right; reflexivity]);
        rewrite (proj2 UP b B1); apply getmem_noverlap;
        apply above_stack_noverlap; [exact B2 | left; reflexivity] |].
      all: split; [apply N.mod_small; assumption|].
      all: destruct CSb as (C1 & C2 & C3 & C4 & C5).
      all: repeat split; reg; first [ assumption | exact R8 ].
Qed.

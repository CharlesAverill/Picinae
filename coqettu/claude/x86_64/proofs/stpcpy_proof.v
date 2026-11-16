(* stpcpy -- copy a string, returning a pointer to its end (musl x86_64, C)

   SEMANTICS
   ---------
   musl's __stpcpy (src/string/stpcpy.c) is

       if ((uintptr_t)s % ALIGN == (uintptr_t)d % ALIGN) {
           for (; (uintptr_t)s % ALIGN; s++, d++)
               if (!( *d=*s)) return d;
           wd=(void * )d; ws=(const void * )s;
           for (; !HASZERO( *ws); *wd++ = *ws++);
           d=(void * )wd; s=(const void * )ws;
       }
       for (; ( *d=*s); s++, d++);
       return d;

   The proof tracks the exact set of copied offsets (cpy, from
   lib/x64_memcpy_sets.v) and needs two facts about the word loop: a source
   word whose HASZERO test is 0 lies entirely before the terminator
   (word_bound, from haszero_bytes_msub), and the source bytes up to the
   terminator are never overwritten by the copy (src_byte, from the
   non-overlap precondition).  The final word read may extend up to 7 bytes
   past the terminator; those bytes never affect the result.

   SPECIFICATION (man 3 stpcpy, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *stpcpy(char *restrict dst, const char *restrict src);

     DESCRIPTION
            These functions copy the string pointed to by src, into a string
            at the buffer pointed to by dst.  The programmer is responsible
            for allocating a destination buffer large enough, that is,
            strlen(src) + 1.

     RETURN VALUE
            stpcpy()
                   This function returns a pointer to the terminating null
                   byte of the copied string.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            stpcpy at 0x347e0 (Ghidra image base 0x100000: 0x1347e0)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/stpcpy_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dst, RSI = src; m = memory on entry.  Precondition
            (cpy_ok): src is a string of length L (bytes src[0..L) nonzero,
            src[L] = 0) and the L+1 bytes at dst do not overlap the L+1 bytes
            at src (restrict; the man page's buffer requirement is implied
            by the theorem being about exactly those bytes).
   Output:  At the RET (0x134871): RAX = dst + L (mod 2^64), the copied
            terminator; memory is `copied`: dst[i] = src[i] for i <= L, and
            every byte whose offset from dst is at least L+1 is unchanged.
            RSP and RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.stpcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_haszero CoqEtTu.lib.x64_memcpy_sets.
Require Import CoqEtTu.proofs.strlen_proof.
Open Scope N.

Theorem stpcpy_nwc: forall s2 s1, stpcpy_amd64 s1 = stpcpy_amd64 s2.
Proof. reflexivity. Qed.

Theorem stpcpy_welltyped: welltyped_prog x64typctx stpcpy_amd64.
Proof. exact welltyped. Qed.

(* src is a string of length L whose L+1 bytes do not overlap the L+1 bytes
   of dest *)
Definition cpy_ok (m d s L:N) := nilfree m s L /\ m Ⓑ[s ⊕ L] = 0 /\ nov d s (L + 1).

Definition prefix (k:N) := fun i => i < k.

Lemma prefix_lt: forall k i, prefix k i -> i < k.
Proof. intros. exact H. Qed.

(* Source bytes up to the terminator are still intact while copying. *)
Lemma src_byte:
  forall m M d src L k j, cpy m M d src (prefix k) -> cpy_ok m d src L -> k <= L -> j <= L ->
  M Ⓑ[src + j] = m Ⓑ[src ⊕ j].
Proof.
  intros m M d src L k j [C F] [NF [Z NOV]] KL JL.
  rewrite <- (getmem_mod_l _ _ _ M). apply F. unfold prefix. intro H.
  apply (NOV (msub 64 (src ⊕ j) d) j). lia. lia.
  rewrite add_msub. rewrite N.mod_mod by discriminate. reflexivity.
Qed.

Lemma cpy_byte:
  forall m M d src L k, cpy m M d src (prefix k) -> cpy_ok m d src L -> k <= L ->
  cpy m (setmem 64 LittleE 1 M (d + k) (M Ⓑ[src + k])) d src (prefix (k + 1)).
Proof.
  intros m M d src L k CP OK KL.
  rewrite (src_byte m M d src L k k) by assumption.
  rewrite getmem_mod_l.
  eapply cpy_equiv; [|apply (cpy_store m M d src (prefix k) k 1 (d + k) (src + k) CP)].
  - intro i. unfold prefix. lia.
  - intros i I. unfold prefix in I. destruct OK as [_ [_ NOV]].
    change (2^64) with 18446744073709551616. assert (L < 18446744073709551616).
    { destruct (N.lt_ge_cases L 18446744073709551616) as [|G]. assumption. exfalso.
      apply (NOV (msub 64 src d) 0). change (2^64) with 18446744073709551616 in *.
      pose proof (msub_lt 64 src d). lia. lia.
      rewrite add_msub, N.add_0_r. reflexivity. }
    lia.
  - lia.
  - destruct OK as [_ [_ NOV]].
    destruct (N.lt_ge_cases L (2^64)) as [|G]. lia. exfalso.
    apply (NOV (msub 64 src d) 0). pose proof (msub_lt 64 src d). lia. lia.
    rewrite add_msub, N.add_0_r. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma cpy_ok_bound: forall m d src L, cpy_ok m d src L -> L < 2^64.
Proof.
  intros m d src L [_ [_ NOV]].
  destruct (N.lt_ge_cases L (2^64)) as [|G]. assumption. exfalso.
  apply (NOV (msub 64 src d) 0). pose proof (msub_lt 64 src d). lia. lia.
  rewrite add_msub, N.add_0_r. reflexivity.
Qed.

Lemma cpy_word:
  forall m M d src L k, cpy m M d src (prefix k) -> cpy_ok m d src L -> k + 8 <= L ->
  cpy m (setmem 64 LittleE 8 M (d + k) (M Ⓠ[src + k])) d src (prefix (k + 8)).
Proof.
  intros m M d src L k CP OK KL. pose proof (cpy_ok_bound _ _ _ _ OK) as LB.
  pose proof OK as [_ [_ NOV]].
  rewrite (cpy_load m M d src (prefix k) (L + 1) k 8 (src + k) CP) by
    (unfold prefix; intros; lia || reflexivity || assumption).
  eapply cpy_equiv; [|apply (cpy_store m M d src (prefix k) k 8 (d + k) (src + k) CP)].
  - intro i. unfold prefix. lia.
  - intros i I. unfold prefix in I. lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
Qed.

(* A HASZERO-clean source word read during the copy lies before the
   terminator. *)
Lemma word_bound:
  forall m M d src L k, cpy m M d src (prefix k) -> cpy_ok m d src L -> k <= L ->
  N.lnot (M Ⓠ[src + k]) 64 .& (M Ⓠ[src + k] ⊖ 0x0101010101010101) .& 0x8080808080808080 = 0 ->
  k + 8 <= L.
Proof.
  intros m M d src L k CP OK KL H.
  destruct (N.le_gt_cases (k + 8) L) as [|G]. assumption. exfalso.
  pose proof (haszero_bytes_msub _ (getmem_bound 64 LittleE 8 M (src + k)) H (L - k) ltac:(lia)) as B.
  rewrite byte_of_load in B by lia.
  rewrite getmem_mod_l in B. replace (src + k + (L - k)) with (src + L) in B by lia.
  rewrite (src_byte m M d src L k L) in B by (assumption || lia).
  apply B. destruct OK as [_ [Z _]]. exact Z.
Qed.

Definition stpcpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x134871 => true
  | _ => false end | _ => false end.

Definition stpcpy_post (s0:store) (m d src L:N) (s:store) :=
  s R_RAX = d ⊕ L /\ copied m (s V_MEM64) d src (L + 1) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition stpcpy_invs (s0:store) (m d src L:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1347e0 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1347ee | 0x134868 =>
      Some (exists k, k <= L /\ s R_RSI = src ⊕ k /\ s R_RAX = d ⊕ k /\
            cpy m (s V_MEM64) d src (prefix k) /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13482b =>
      Some (exists k, k <= L /\ s R_RSI = src ⊕ k /\ s R_RAX = d ⊕ k /\
            s R_R9 = 0xfefefefefefefeff /\ s R_R8 = 0x8080808080808080 /\
            cpy m (s V_MEM64) d src (prefix k) /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134871 => Some (stpcpy_post s0 m d src L s)
  | _ => None
  end | _ => None end.

Theorem stpcpy_correct:
  forall prog s t s' x' m d src L
         (STPCPY: stpcpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1347e0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src)
         (OK: cpy_ok m d src L),
  satisfies_all prog (stpcpy_invs s m d src L) stpcpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src L STPCPY ENTRY MDL MEM D S OK.
  assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RDI 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=stpcpy_amd64); [exact STPCPY| |].
    intros a s1 t1 EXIT NOCODE. unfold stpcpy_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src L MDL MEM D S OK DB SB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply stpcpy_welltyped. intro MDL1.
  clear - PRE MDL1 OK DB SB. rename t1 into t.
  pose proof (cpy_ok_bound _ _ _ _ OK) as LB.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [RSP CS]]]].
    repeat x64_step. all: bc_norm.
    all: exists 0; split; [lia|]; split; [rewrite N.add_0_r, N.mod_small by assumption; reflexivity|];
         split; [rewrite N.add_0_r, N.mod_small by assumption; reflexivity|];
         split; [rewrite MEM; eapply cpy_equiv; [|apply cpy_empty]; intro i; unfold prefix; lia|];
         conj_tac.
  - (* the alignment loop *)
    destruct PRE as [k [KL [RSI [RAX [CP [RSP CS]]]]]].
    repeat x64_step. all: bc_norm.
    all: try (rewrite (src_byte m (s1 V_MEM64) d src L k k) in BC by (assumption || lia)).
    all: try (rewrite (src_byte m (s1 V_MEM64) d src L k k) in BC0 by (assumption || lia)).
    all: try (rewrite (src_byte m (s1 V_MEM64) d src L k k) in BC1 by (assumption || lia)).
    all: lazymatch goal with
    | |- context [18374403900871474943] =>
        (* aligned: enter the word loop *)
        exists k; conj_tac
    | |- _ = _ /\ copied _ _ _ _ _ /\ _ =>
        (* terminator copied: k = L *)
        assert (KE: k = L) by
          (destruct (N.lt_ge_cases k L) as [KL'|]; [|lia]; exfalso;
           destruct OK as [NF _]; apply (NF k KL'); assumption);
        subst k; split; [reflexivity|]; split;
        [ replace (1 + L) with (L + 1) by lia; eapply cpy_copied; [|apply (cpy_byte m _ d src L L); assumption || lia];
          intro i; unfold prefix; lia |];
        conj_tac
    | |- exists _, _ =>
        (* nonzero byte copied: next *)
        assert (KL': k < L) by
          (destruct (N.lt_ge_cases k L) as [|KG]; [assumption|]; exfalso;
           replace k with L in * by lia; destruct OK as [_ [Z _]]; contradiction);
        exists (k + 1); split; [lia|]; split; [f_equal; lia|]; split; [f_equal; lia|];
        split; [apply (cpy_byte m _ d src L k); assumption|]; conj_tac
    end.
  - (* the word loop *)
    destruct PRE as [k [KL [RSI [RAX [R9 [R8 [CP [RSP CS]]]]]]]].
    repeat x64_step. all: bc_norm.
    + (* no zero byte in this word: copy it *)
      rewrite (N.land_comm (_ ⊖ _)) in BC.
      assert (K8: k + 8 <= L) by (eapply word_bound; eassumption).
      exists (k + 8). split. lia. split. f_equal. lia. split. f_equal. lia.
      split. reflexivity. split. reflexivity.
      split. apply (cpy_word m _ d src L k); assumption. conj_tac.
    + exists k. conj_tac.
  - (* the final byte loop *)
    destruct PRE as [k [KL [RSI [RAX [CP [RSP CS]]]]]].
    repeat x64_step. all: bc_norm.
    all: try (rewrite (src_byte m (s1 V_MEM64) d src L k k) in BC by (assumption || lia)).
    all: try (rewrite (src_byte m (s1 V_MEM64) d src L k k) in BC0 by (assumption || lia)).
    all: try (rewrite (src_byte m (s1 V_MEM64) d src L k k) in BC1 by (assumption || lia)).
    all: lazymatch goal with
    | |- context [18374403900871474943] =>
        (* aligned: enter the word loop *)
        exists k; conj_tac
    | |- _ = _ /\ copied _ _ _ _ _ /\ _ =>
        (* terminator copied: k = L *)
        assert (KE: k = L) by
          (destruct (N.lt_ge_cases k L) as [KL'|]; [|lia]; exfalso;
           destruct OK as [NF _]; apply (NF k KL'); assumption);
        subst k; split; [reflexivity|]; split;
        [ replace (1 + L) with (L + 1) by lia; eapply cpy_copied; [|apply (cpy_byte m _ d src L L); assumption || lia];
          intro i; unfold prefix; lia |];
        conj_tac
    | |- exists _, _ =>
        (* nonzero byte copied: next *)
        assert (KL': k < L) by
          (destruct (N.lt_ge_cases k L) as [|KG]; [assumption|]; exfalso;
           replace k with L in * by lia; destruct OK as [_ [Z _]]; contradiction);
        exists (k + 1); split; [lia|]; split; [f_equal; lia|]; split; [f_equal; lia|];
        split; [apply (cpy_byte m _ d src L k); assumption|]; conj_tac
    end.
Qed.

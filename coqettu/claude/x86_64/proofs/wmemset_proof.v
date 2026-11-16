(* wmemset -- fill an array of wide characters (musl x86_64, C)

   SEMANTICS
   ---------
   musl's wmemset (src/string/wmemset.c) is

       wchar_t *ret = d;
       while (n--) *d++ = c;
       return ret;

   GCC stores one element first when n is odd, then two per iteration.

   SPECIFICATION (man 3 wmemset, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <wchar.h>
            wchar_t *wmemset(wchar_t wcs[.n], wchar_t wc, size_t n);

     DESCRIPTION
            The wmemset() function is the wide-character equivalent of the
            memset(3) function.  It fills the array of n wide-characters
            starting at wcs with n copies of the wide character wc.

     RETURN VALUE
            wmemset() returns wcs.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wmemset at 0x3c480 (Ghidra image base 0x100000: 0x13c480)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/wmemset_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, ESI = c (c32 = RSI mod 2^32), RDX = n; m = memory.
            Precondition: 4n <= 2^64 (the array fits in the address space).
   Output:  At the RET (0x13c4a3): RAX = d; for every i < n the 32-bit word
            at d + 4i (mod 2^64) is c32, and every byte whose offset from d
            (mod 2^64) is at least 4n is unchanged (wfil).  RSP and RBX, RBP,
            R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wmemset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem wmemset_nwc: forall s2 s1, wmemset_amd64 s1 = wmemset_amd64 s2.
Proof. reflexivity. Qed.

Theorem wmemset_welltyped: welltyped_prog x64typctx wmemset_amd64.
Proof. exact welltyped. Qed.

(* the first k words at d hold c; bytes at offsets >= 4k are as in m *)
Definition wfil (m m':memory) (d c k:N) :=
  (forall i, i < k -> m' Ⓓ[d ⊕ 4*i] = c) /\
  (forall b, 4*k <= msub 64 b d -> m' Ⓑ[b] = m Ⓑ[b]).

Lemma wfil_store:
  forall m m' d c k a v, wfil m m' d c k -> 4*(k+1) <= 2^64 ->
  a mod 2^64 = (d + 4*k) mod 2^64 -> v mod 2^32 = c ->
  wfil m (setmem 64 LittleE 4 m' a v) d c (k + 1).
Proof.
  intros m m' d c k a v [W F] K A V. split.
  - intros i I. destruct (N.lt_ge_cases i k) as [IK|IK].
    + rewrite getmem_noverlap. apply W, IK.
      intros [x [y [X [Y E]]]]. unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
    + replace i with k by lia.
      rewrite <- A, getmem_mod_l, getmem_setmem by discriminate. exact V.
  - intros b B. rewrite getmem_noverlap. apply F. lia.
    intros [x [y [X [Y E]]]]. unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma wfil_empty: forall m d c, wfil m m d c 0.
Proof. intros. split. intros i I. lia. reflexivity. Qed.

Definition wmemset_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13c4a3 => true
  | _ => false end | _ => false end.

Definition wmemset_post (s0:store) (m d c n:N) (s:store) :=
  s R_RAX = d /\ wfil m (s V_MEM64) d (c mod 2^32) n /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wmemset_invs (s0:store) (m d c n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13c480 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = c /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c49b => Some (exists k, k <= n /\ (n - k) mod 2 = 0 /\ s R_RAX = k /\
                      wfil m (s V_MEM64) d (c mod 2^32) k /\
                      s R_RDI = d /\ s R_RSI = c /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c4a3 => Some (wmemset_post s0 m d c n s)
  | _ => None
  end | _ => None end.

Theorem wmemset_correct:
  forall prog s t s' x' m d c n
         (WMEMSET: wmemset_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13c480, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (C: s R_RSI = c) (Nn: s R_RDX = n)
         (NW: 4*n <= 2^64),
  satisfies_all prog (wmemset_invs s m d c n) wmemset_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d c n WMEMSET ENTRY MDL MEM D C Nn NW.
  eapply satisfies_all_pmono with (p1:=wmemset_amd64); [exact WMEMSET| |].
    intros a s1 t1 EXIT NOCODE. unfold wmemset_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d c n MDL MEM D C Nn NW START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemset_welltyped. intro MDL1.
  clear - PRE MDL1 NW. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [C [Nn [RSP CS]]]]].
    repeat x64_step. all: bc_norm.
    + exists 0. split. lia. split. rewrite N.sub_0_r. assumption. split. reflexivity.
      split. rewrite MEM. apply wfil_empty. conj_tac.
    + exists 1. split. destruct n. contradiction BC. reflexivity. lia.
      split. assert (n mod 2 = 1) by (pose proof (N.mod_lt n 2); lia).
        rewrite (N.div_mod n 2) in * by discriminate. mlia64.
      split. reflexivity.
      split. apply (wfil_store m m d (c mod 2^32) 0 d c (wfil_empty m d _)).
        change (2^64) with 18446744073709551616 in *. lia. rewrite N.add_0_r. reflexivity. reflexivity.
      conj_tac.
  - destruct PRE as [k [KN [PAR [RAX [WF [D [C [Nn [RSP CS]]]]]]]]].
    repeat x64_step. all: bc_norm.
    + rewrite <- BC in WF. split. reflexivity. split. exact WF. conj_tac.
    + assert (K2: k + 2 <= n) by (rewrite (N.div_mod (n - k) 2) in PAR by discriminate; mlia64).
      exists (k + 2). split. assumption. split. replace (n - (k + 2)) with (n - k - 2) by lia.
        rewrite <- (N.mod_add (n - k - 2) 1) by discriminate. replace (n - k - 2 + 1 * 2) with (n - k) by lia.
        assumption.
      split. change (2^64) with 18446744073709551616 in *. rewrite N.add_comm. apply N.mod_small. lia.
      split. replace (k + 2) with (k + 1 + 1) by lia.
        apply wfil_store. apply wfil_store. assumption.
        change (2^64) with 18446744073709551616 in *. lia. f_equal. lia. reflexivity.
        change (2^64) with 18446744073709551616 in *. lia. f_equal. lia. reflexivity.
      conj_tac.
Qed.

(* wmemchr -- search an array of wide characters (musl x86_64, C)

   SEMANTICS
   ---------
   musl's wmemchr (src/string/wmemchr.c) is

       for (; n && *s != c; n--, s++);
       return n ? (wchar_t * )s : 0;

   Ghidra split the function at the loop head; programs/wmemchr_amd64.v is
   the merge of both lifted pieces (tools/merge_lift.py, checked complete by
   tools/check_lift.py).

   SPECIFICATION (man 3 wmemchr, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <wchar.h>
            wchar_t *wmemchr(const wchar_t s[.n], wchar_t c, size_t n);

     DESCRIPTION
            The wmemchr() function is the wide-character equivalent of the
            memchr(3) function.  It searches the n wide characters starting
            at s for the first occurrence of the wide character c.

     RETURN VALUE
            The wmemchr() function returns a pointer to the first occurrence
            of c among the n wide characters starting at s, or NULL if c does
            not occur among these.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wmemchr at 0x34ec0 (Ghidra image base 0x100000: 0x134ec0)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing, merged with FUN_00134ee8.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, ESI = c (c32 = RSI mod 2^32), RDX = n; m = memory.
            No precondition.
   Output:  At either RET: either some K < n has s[i] <> c32 for i < K,
            s[K] = c32 and RAX = s + 4K (mod 2^64); or no s[i], i < n, equals
            c32 and RAX = 0.  (s[i] is the 32-bit word at s + 4i.)  Memory,
            RSP and RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wmemchr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem wmemchr_nwc: forall s2 s1, wmemchr_amd64 s1 = wmemchr_amd64 s2.
Proof. reflexivity. Qed.

Theorem wmemchr_welltyped: welltyped_prog x64typctx wmemchr_amd64.
Proof. exact welltyped. Qed.

Definition wabsent (m:memory) (p c k:N) := forall i, i < k -> m Ⓓ[p ⊕ 4*i] <> c.

Definition wmemchr_result (m:memory) (p c n r:N) :=
  (exists K, K < n /\ wabsent m p c K /\ m Ⓓ[p ⊕ 4*K] = c /\ r = p ⊕ 4*K) \/
  (wabsent m p c n /\ r = 0).

Definition wmemchr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x134ef4 | 0x134ef7 => true
  | _ => false end | _ => false end.

Definition wmemchr_post (s0:store) (m p c n:N) (s:store) :=
  wmemchr_result m p (c mod 2^32) n (s R_RAX) /\
  s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wmemchr_invs (s0:store) (m p c n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x134ec0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134ee8 => Some (exists k, k <= n /\ s R_RDX = n - k /\ s R_RDI = p ⊕ 4*k /\
                      wabsent m p (c mod 2^32) k /\ s R_RSI = c /\
                      s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134ef4 | 0x134ef7 => Some (wmemchr_post s0 m p c n s)
  | _ => None
  end | _ => None end.

Lemma dword_load_off: forall (m:memory) p k, m Ⓓ[p ⊕ k] = m Ⓓ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Theorem wmemchr_correct:
  forall prog s t s' x' m p c n
         (WMEMCHR: wmemchr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x134ec0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c) (Nn: s R_RDX = n),
  satisfies_all prog (wmemchr_invs s m p c n) wmemchr_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c n WMEMCHR ENTRY MDL MEM P C Nn.
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wmemchr_amd64); [exact WMEMCHR| |].
    intros a s1 t1 EXIT NOCODE. unfold wmemchr_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c n MDL MEM P C Nn PB NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemchr_welltyped. intro MDL1.
  clear - PRE MDL1 PB NB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [C [Nn [RSP CS]]]]].
    repeat x64_step.
    exists 0. split. lia. split. rewrite N.sub_0_r. assumption.
    split. rewrite N.mul_0_r, N.add_0_r, N.mod_small by assumption. assumption.
    split. intros i I. lia. conj_tac.
  - destruct PRE as [k [KN [RDX [RDI [WA [RSI [MEM [RSP CS]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?dword_load_off in *.
    + split. right. split. replace n with k by lia. assumption. reflexivity. conj_tac.
    + split. left. exists k. split. lia. split. assumption. split. assumption. reflexivity. conj_tac.
    + exists (k + 1). split. lia.
      split. rewrite msub_nowrap; rewrite !N.mod_small; mlia64.
      split. mlia64.
      split. intros i I. destruct (N.lt_ge_cases i k). apply WA. assumption.
        replace i with k by lia. assumption.
      conj_tac.
Qed.

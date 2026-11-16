(* memrchr -- scan memory backwards for a byte (musl x86_64, C)

   SEMANTICS
   ---------
   musl's memrchr (src/string/memrchr.c) is

       const unsigned char *s = m;
       c = (unsigned char)c;
       while (n--) if (s[n]==c) return (void * )(s+n);
       return 0;

   GCC walks a pointer from s+n-1 down to s-1.

   SPECIFICATION (man 3 memrchr, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #define _GNU_SOURCE
            #include <string.h>
            void *memrchr(const void s[.n], int c, size_t n);

     DESCRIPTION
            The memrchr() function is like the memchr() function, except that
            it searches backward from the end of the n bytes pointed to by s
            instead of forward from the beginning.

     RETURN VALUE
            The memchr() and memrchr() functions return a pointer to the
            matching byte or NULL if the character does not occur in the
            given memory area.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            memrchr at 0x347a0 (Ghidra image base 0x100000: 0x1347a0)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/memrchr_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, ESI = c (c8 = c mod 256), RDX = n; m = memory.
            No precondition.
   Output:  At the RET (0x1347da): either some K < n has s[K] = c8,
            s[i] <> c8 for K < i < n, and RAX = s + K (mod 2^64); or no byte
            of s[0..n) is c8 and RAX = 0.  Memory, RSP and RBX, RBP, R12-R15
            are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.memrchr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem memrchr_nwc: forall s2 s1, memrchr_amd64 s1 = memrchr_amd64 s2.
Proof. reflexivity. Qed.

Theorem memrchr_welltyped: welltyped_prog x64typctx memrchr_amd64.
Proof. exact welltyped. Qed.

(* no byte at an index in [j, n) is c *)
Definition rabsent (m:memory) (p c j n:N) := forall i, j <= i < n -> m Ⓑ[p ⊕ i] <> c.

Definition memrchr_result (m:memory) (p c n r:N) :=
  (exists K, K < n /\ m Ⓑ[p ⊕ K] = c /\ rabsent m p c (K + 1) n /\ r = p ⊕ K) \/
  (rabsent m p c 0 n /\ r = 0).

Definition memrchr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1347da => true
  | _ => false end | _ => false end.

Definition memrchr_post (s0:store) (m p c n:N) (s:store) :=
  memrchr_result m p (c mod 2^8) n (s R_RAX) /\
  s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition memrchr_invs (s0:store) (m p c n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1347a0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1347c0 => Some (exists j, j <= n /\ s R_RAX = (p ⊕ j) ⊖ 1 /\ s R_RDI = p ⊖ 1 /\
                      rabsent m p (c mod 2^8) j n /\ s R_RSI = c mod 2^8 /\
                      s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1347da => Some (memrchr_post s0 m p c n s)
  | _ => None
  end | _ => None end.

Lemma byte_load_off: forall (m:memory) p k, m Ⓑ[p ⊕ k] = m Ⓑ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Lemma byte_load_mod: forall (m:memory) p, m Ⓑ[p mod 2^64] = m Ⓑ[p].
Proof. intros. apply getmem_mod_l. Qed.

Lemma prev_addr: forall p j, 1 <= j -> p + j ⊖ 1 = p ⊕ (j - 1).
Proof. intros. unfold msub. change (2^64) with 18446744073709551616. lia. Qed.

Theorem memrchr_correct:
  forall prog s t s' x' m p c n
         (MEMRCHR: memrchr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1347a0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c) (Nn: s R_RDX = n),
  satisfies_all prog (memrchr_invs s m p c n) memrchr_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c n MEMRCHR ENTRY MDL MEM P C Nn.
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=memrchr_amd64); [exact MEMRCHR| |].
    intros a s1 t1 EXIT NOCODE. unfold memrchr_invs.
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
  eapply models_at_invariant; try eassumption. apply memrchr_welltyped. intro MDL1.
  clear - PRE MDL1 PB NB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [C [Nn [RSP CS]]]]].
    repeat x64_step.
    exists n. split. lia. split. mlia64. split. reflexivity.
    split. intros i I. lia. conj_tac.
  - destruct PRE as [j [JN [RAX [RDI [RA [RSI [MEM [RSP CS]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: assert (J: j < 2^64) by (change (2^64) with 18446744073709551616 in *; lia).
    + (* j = 0: not found *)
      rewrite N.mod_small in BC by exact J. subst j.
      split. right. split. assumption. reflexivity. conj_tac.
    + (* found at j - 1 *)
      rewrite N.mod_small in BC by exact J.
      rewrite prev_addr in * by lia.
      split. left. exists (j - 1). split. lia. split. assumption.
        split. replace (j - 1 + 1) with j by lia. assumption. reflexivity.
      conj_tac.
    + (* not equal: step down *)
      rewrite N.mod_small in BC by exact J.
      rewrite prev_addr in BC0 by lia.
      exists (j - 1). split. lia. split. mlia64. split. reflexivity.
      split. intros i I. destruct (N.eq_dec i (j - 1)) as [->|NE].
        assumption.
        apply RA. lia.
      conj_tac.
Qed.

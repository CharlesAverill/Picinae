(* wcscmp -- compare two wide-character strings (musl x86_64, C)

   SEMANTICS
   ---------
   musl's wcscmp (src/string/wcscmp.c) is

       for (; *l==*r && *l && *r; l++, r++);
       return *l < *r ? -1 : *l > *r;

   wchar_t is a signed 32-bit int on x86_64, so the final comparison is
   signed (GCC: CMP, SETL, CMOVG).  The result is exactly -1, 0 or 1.

   SPECIFICATION (man 3 wcscmp, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <wchar.h>
            int wcscmp(const wchar_t *s1, const wchar_t *s2);

     DESCRIPTION
            The wcscmp() function is the wide-character equivalent of the
            strcmp(3) function.  It compares the wide-character string
            pointed to by s1 and the wide-character string pointed to by s2.

     RETURN VALUE
            The wcscmp() function returns zero if the wide-character strings
            at s1 and s2 are equal.  It returns an integer greater than zero
            if at the first differing position i, the corresponding
            wide-character s1[i] is greater than s2[i].  It returns an
            integer less than zero if at the first differing position i, the
            corresponding wide-character s1[i] is less than s2[i].

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcscmp at 0x34b20 (Ghidra image base 0x100000: 0x134b20)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/wcscmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s1, RSI = s2; m = memory on entry.  No precondition.
   Output:  At the RET (0x134b61) there is K such that for i < K the words
            s1[i] = s2[i] <> 0, and s1[K] <> s2[K] or s1[K] = 0 (wcscmp_stop);
            RAX = wcmp s1[K] s2[K]: 0xffffffff (-1) if s1[K] < s2[K] as signed
            32-bit ints, 1 if greater, 0 if equal.  Memory, RSP and RBX, RBP,
            R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcscmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_signed.
Open Scope N.

Theorem wcscmp_nwc: forall s2 s1, wcscmp_amd64 s1 = wcscmp_amd64 s2.
Proof. reflexivity. Qed.

Theorem wcscmp_welltyped: welltyped_prog x64typctx wcscmp_amd64.
Proof. exact welltyped. Qed.

Definition wsame_prefix (m:memory) (l r k:N) :=
  forall i, i < k -> m Ⓓ[l ⊕ 4*i] = m Ⓓ[r ⊕ 4*i] /\ m Ⓓ[l ⊕ 4*i] <> 0.

Definition wcscmp_stop (m:memory) (l r K:N) :=
  wsame_prefix m l r K /\ (m Ⓓ[l ⊕ 4*K] <> m Ⓓ[r ⊕ 4*K] \/ m Ⓓ[l ⊕ 4*K] = 0).

(* signed three-way comparison of two 32-bit words, as an int *)
Definition wcmp (a b:N) : N :=
  if Z.ltb (toZ 32 a) (toZ 32 b) then 0xffffffff else if Z.ltb (toZ 32 b) (toZ 32 a) then 1 else 0.

Definition wcscmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x134b61 => true
  | _ => false end | _ => false end.

Definition wcscmp_post (s0:store) (m l r:N) (s:store) :=
  (exists K, wcscmp_stop m l r K /\ s R_RAX = wcmp (m Ⓓ[l ⊕ 4*K]) (m Ⓓ[r ⊕ 4*K])) /\
  s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wcscmp_invs (s0:store) (m l r:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x134b20 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134b40 => Some (exists k, s R_RAX = (4*k) mod 2^64 /\ wsame_prefix m l r k /\
                      s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134b61 => Some (wcscmp_post s0 m l r s)
  | _ => None
  end | _ => None end.

Lemma dword_load_off: forall (m:memory) p k, m Ⓓ[p ⊕ k] = m Ⓓ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Theorem wcscmp_correct:
  forall prog s t s' x' m l r
         (WCSCMP: wcscmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x134b20, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r),
  satisfies_all prog (wcscmp_invs s m l r) wcscmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r WCSCMP ENTRY MDL MEM L R.
  eapply satisfies_all_pmono with (p1:=wcscmp_amd64); [exact WCSCMP| |].
    intros a s1 t1 EXIT NOCODE. unfold wcscmp_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m l r MDL MEM L R START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [L [R [RSP CS]]]].
    repeat x64_step.
    exists 0. split. reflexivity. split. intros i I. lia. conj_tac.
  - destruct PRE as [k [RAX [SP [MEM [L [R [RSP CS]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?dword_load_off in *.
    all: unfold wcmp.
    all: set (a := m Ⓓ[l ⊕ 4*k]) in *; set (b := m Ⓓ[r ⊕ 4*k]) in *.
    all: assert (A: a < 2^32) by apply getmem_bound.
    all: assert (B: b < 2^32) by apply getmem_bound.
    all: lazymatch goal with
    | |- exists _, _ =>
      (* equal nonzero: advance *)
      exists (k + 1); split; [mlia64|];
      split; [intros i I; destruct (N.lt_ge_cases i k); [apply SP; assumption|];
        replace i with k by lia; split; assumption|];
      conj_tac
    | _ =>
      (* first difference or common terminator *)
      split; [exists k; split; [split; [assumption | first [left; assumption | right; assumption]]|];
        change (m Ⓓ[l ⊕ 4*k]) with a; change (m Ⓓ[r ⊕ 4*k]) with b; clearbody a b; arith_only;
        s32_norm a; s32_norm b; s32_msub_norm; flags_finish|];
      conj_tac
    end.
Qed.

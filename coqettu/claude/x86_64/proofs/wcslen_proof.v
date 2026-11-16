(* wcslen -- length of a wide-character string (musl x86_64, C)

   SEMANTICS
   ---------
   musl's wcslen (src/string/wcslen.c) is

       const wchar_t *a;
       for (a=s; *s; s++);
       return s-a;

   wchar_t is a 32-bit int on x86_64.  GCC computes s-a as the byte
   difference shifted right arithmetically by 2 (SAR), so the result is the
   element count k whenever 4k < 2^63, i.e. whenever the string fits in a
   C object (wcslen_ret).

   SPECIFICATION (man 3 wcslen, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <wchar.h>
            size_t wcslen(const wchar_t *s);

     DESCRIPTION
            The wcslen() function is the wide-character equivalent of the
            strlen(3) function.  It determines the length of the
            wide-character string pointed to by s, excluding the terminating
            null wide character (L'\0').

     RETURN VALUE
            The wcslen() function returns the number of wide characters in s.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcslen at 0x3c380 (Ghidra image base 0x100000: 0x13c380)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/wcslen_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; m = memory on entry.  No precondition.
   Output:  At the RET (0x13c3a1) there is k such that the 32-bit words at
            s, s+4, ..., s+4(k-1) are nonzero and the word at s+4k is zero,
            and RAX = (4k mod 2^64) >>> 2 (arithmetic shift), which is k when
            4k < 2^63 (wcslen_ret).  Memory is unchanged; RSP and RBX, RBP,
            R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem wcslen_nwc: forall s2 s1, wcslen_amd64 s1 = wcslen_amd64 s2.
Proof. reflexivity. Qed.

Theorem wcslen_welltyped: welltyped_prog x64typctx wcslen_amd64.
Proof. exact welltyped. Qed.

(* the wide chars s[0..k) are nonzero *)
Definition wnilfree (m:memory) (p k:N) := forall i, i < k -> m Ⓓ[p ⊕ 4*i] <> 0.

Definition wcslen_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13c3a1 => true
  | _ => false end | _ => false end.

Definition wcslen_post (s0:store) (m p:N) (s:store) :=
  (exists k, wnilfree m p k /\ m Ⓓ[p ⊕ 4*k] = 0 /\ s R_RAX = (4 ⊗ k) >>> 2) /\
  s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wcslen_invs (s0:store) (m p:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13c380 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c394 => Some (exists k, s R_RAX = p ⊕ 4*k /\ wnilfree m p k /\
                      s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c3a1 => Some (wcslen_post s0 m p s)
  | _ => None
  end | _ => None end.

Lemma dword_load_off: forall (m:memory) p k, m Ⓓ[p ⊕ k] = m Ⓓ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

(* The returned element count, for any string that fits in a C object. *)
Theorem wcslen_ret: forall k, 4*k < 2^63 -> (4 ⊗ k) >>> 2 = k.
Proof.
  intros k K. rewrite (N.mod_small (4*k)) by (change (2^64) with (2*2^63); lia).
  unfold ashiftr, sbop1. rewrite (proj1 (toZ_nonneg 64 (4*k))).
  - rewrite N.mod_small by (change (2^64) with (2*2^63); lia).
    change (Z.of_N 2) with 2%Z. rewrite Z.shiftr_div_pow2 by discriminate.
    change (2^2)%Z with 4%Z. rewrite N2Z.inj_mul, Z.mul_comm, Z.div_mul by discriminate.
    unfold ofZ. rewrite Z.mod_small. apply N2Z.id.
    split. apply N2Z.is_nonneg. change (2 ^ Z.of_N 64)%Z with (Z.of_N (2^64)).
    apply N2Z.inj_lt. change (2^64) with (2*2^63). lia.
  - rewrite N.mod_small by (change (2^64) with (2*2^63); lia). exact K.
Qed.

Theorem wcslen_correct:
  forall prog s t s' x' m p
         (WCSLEN: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13c380, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p),
  satisfies_all prog (wcslen_invs s m p) wcslen_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p WCSLEN ENTRY MDL MEM P.
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wcslen_amd64); [exact WCSLEN| |].
    intros a s1 t1 EXIT NOCODE. unfold wcslen_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p MDL MEM P PB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcslen_welltyped. intro MDL1.
  clear - PRE MDL1 PB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [RSP CS]]].
    repeat x64_step.
    exists 0. split. rewrite N.mul_0_r, N.add_0_r, N.mod_small by assumption. reflexivity.
    split. intros i I. lia. conj_tac.
  - destruct PRE as [k [RAX [NF [MEM [P [RSP CS]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?dword_load_off in *.
    + split. exists k. split. assumption. split. assumption. reflexivity. conj_tac.
    + exists (k + 1). split. f_equal. lia.
      split. intros i I. destruct (N.lt_ge_cases i k). apply NF. assumption.
        replace i with k by lia. assumption.
      conj_tac.
Qed.

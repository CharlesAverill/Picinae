(* memcmp -- compare memory areas (musl x86_64, C)

   SEMANTICS
   ---------
   musl's memcmp (src/string/memcmp.c) is

       const unsigned char *l=vl, *r=vr;
       for (; n && *l == *r; n--, l++, r++);
       return n ? *l-*r : 0;

   GCC compiled it to a loop that advances RDI and RSI and counts RDX down.
   Ghidra split the function at the loop head (it took the leading JMP for a
   tail call), so programs/memcmp_amd64.v is the merge of the two lifted
   pieces (tools/merge_lift.py); tools/check_lift.py confirms it covers every
   instruction of the symbol.

   SPECIFICATION (man 3 memcmp, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            int memcmp(const void s1[.n], const void s2[.n], size_t n);

     DESCRIPTION
            The memcmp() function compares the first n bytes (each
            interpreted as unsigned char) of the memory areas s1 and s2.

     RETURN VALUE
            The memcmp() function returns an integer less than, equal to, or
            greater than zero if the first n bytes of s1 is found,
            respectively, to be less than, to match, or be greater than the
            first n bytes of s2.
            For a nonzero return value, the sign is determined by the sign of
            the difference between the first pair of bytes (interpreted as
            unsigned char) that differ in s1 and s2.
            If n is zero, the return value is zero.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            memcmp at 0x34480 (Ghidra image base 0x100000: 0x134480)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing, merged with FUN_001344ac; see
            programs/memcmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s1, RSI = s2, RDX = n; m = memory on entry.  No precondition.
   Output:  At either RET (0x1344c0, 0x1344c3), memcmp_result holds: either
            the first n bytes agree and RAX = 0, or there is K < n with
            s1[i] = s2[i] for i < K, s1[K] <> s2[K] and
            EAX = s1[K] - s2[K] as a 32-bit int (RAX its zero extension;
            strcmp_sign in strcmp_proof.v gives the signed reading).  RSP and
            RBX, RBP, R12-R15 are unchanged; memory is unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.memcmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem memcmp_nwc: forall s2 s1, memcmp_amd64 s1 = memcmp_amd64 s2.
Proof. reflexivity. Qed.

Theorem memcmp_welltyped: welltyped_prog x64typctx memcmp_amd64.
Proof. exact welltyped. Qed.

Theorem memcmp_preserves_memory:
  forall_endstates memcmp_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition eq_prefix (m:memory) (l r k:N) := forall i, i < k -> m Ⓑ[l ⊕ i] = m Ⓑ[r ⊕ i].

Definition memcmp_result (m:memory) (l r n v:N) :=
  (eq_prefix m l r n /\ v = 0) \/
  (exists K, K < n /\ eq_prefix m l r K /\ m Ⓑ[l ⊕ K] <> m Ⓑ[r ⊕ K] /\
             v = msub 32 (m Ⓑ[l ⊕ K]) (m Ⓑ[r ⊕ K])).

Definition memcmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1344c0 | 0x1344c3 => true
  | _ => false end | _ => false end.

Definition memcmp_post (s0:store) (m l r n:N) (s:store) :=
  memcmp_result m l r n (s R_RAX) /\ s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition memcmp_invs (s0:store) (m l r n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x134480 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1344ac => Some (exists k, k <= n /\ s R_RDX = n - k /\ s R_RDI = l ⊕ k /\
                      s R_RSI = r ⊕ k /\ eq_prefix m l r k /\
                      s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1344c0 | 0x1344c3 => Some (memcmp_post s0 m l r n s)
  | _ => None
  end | _ => None end.

Lemma byte_load_off: forall (m:memory) p k, m Ⓑ[p ⊕ k] = m Ⓑ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Lemma byte_load_mod: forall (m:memory) p, m Ⓑ[p mod 2^64] = m Ⓑ[p].
Proof. intros. apply getmem_mod_l. Qed.

Theorem memcmp_correct:
  forall prog s t s' x' m l r n
         (MEMCMP: memcmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x134480, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r) (Nn: s R_RDX = n),
  satisfies_all prog (memcmp_invs s m l r n) memcmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r n MEMCMP ENTRY MDL MEM L R Nn.
  assert (LB: l < 2^64) by (rewrite <- L; apply (MDL R_RDI 64); reflexivity).
  assert (RB: r < 2^64) by (rewrite <- R; apply (MDL R_RSI 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=memcmp_amd64); [exact MEMCMP| |].
    intros a s1 t1 EXIT NOCODE. unfold memcmp_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m l r n MDL MEM L R Nn LB RB NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memcmp_welltyped. intro MDL1.
  clear - PRE MDL1 LB RB NB. rename t1 into t.
  destruct_inv 64 PRE.

  - (* entry *)
    destruct PRE as [MEM [L [R [Nn [RSP CS]]]]].
    repeat x64_step.
    exists 0. split. lia. split. rewrite N.sub_0_r. assumption.
    split. rewrite N.add_0_r, N.mod_small by assumption. assumption.
    split. rewrite N.add_0_r, N.mod_small by assumption. assumption.
    split. intros i I. lia. conj_tac.

  - (* loop *)
    destruct PRE as [k [K [RDX [RDI [RSI [EQ [MEM [RSP CS]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite ?byte_load_mod in *.
    all: rewrite <- ?byte_load_off in *.
    + (* n bytes compared, all equal *)
      split. left. split. replace n with k by lia. assumption. reflexivity. conj_tac.
    + (* equal bytes: advance *)
      exists (k + 1). split. lia.
      split. rewrite msub_nowrap; rewrite !N.mod_small; change (2^64) with 18446744073709551616 in *; lia.
      split. f_equal. lia. split. f_equal. lia.
      split. intros i I. destruct (N.lt_ge_cases i k). apply EQ. assumption.
        replace i with k by lia. assumption.
      conj_tac.
    + (* first difference *)
      split. right. exists k. split. lia. split. assumption. split. assumption. reflexivity.
      conj_tac.
Qed.

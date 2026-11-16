(* strlen -- length of a NUL-terminated string (musl x86_64, C)

   SEMANTICS
   ---------
   musl's strlen (src/string/strlen.c) is

       for (; (uintptr_t)s % ALIGN; s++) if (!*s) return s-a;
       for (w = (const void * )s; !HASZERO( *w); w++);
       s = (const void * )w;
       for (; *s; s++);
       return s-a;

   with ALIGN = 8 and HASZERO(x) = (x - ONES) & ~x & HIGHS.  GCC compiled it
   to three loops: a byte loop up to 8-byte alignment, a word loop that skips
   quadwords whose HASZERO test is 0, and a final byte loop.  The proof needs
   only that HASZERO never misses a zero byte (lib/x64_haszero.v); a false
   positive just hands over to the final byte loop.  The word loop reads up to
   7 bytes past the terminator (within the same aligned quadword); Picinae's
   memory model has no faults, so that needs no precondition.

   SPECIFICATION (man 3 strlen, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            size_t strlen(const char *s);

     DESCRIPTION
            The strlen() function calculates the length of the string pointed
            to by s, excluding the terminating null byte ('\0').

     RETURN VALUE
            The strlen() function returns the number of bytes in the string
            pointed to by s.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strlen at 0x348c0 (Ghidra image base 0x100000: 0x1348c0)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/strlen_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; m = memory on entry.  No precondition: the theorem does
            not assume the string is terminated (if it is not, strlen does not
            return and partial correctness holds vacuously).
   Output:  At the RET (0x13492c): RAX = k where the bytes s+0 .. s+k-1 are
            all nonzero and the byte at s+k is zero (so k is the length, and
            k < 2^64); memory is unchanged; RSP is unchanged; RBX, RBP,
            R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_haszero.
Open Scope N.

Theorem strlen_nwc: forall s2 s1, strlen_amd64 s1 = strlen_amd64 s2.
Proof. reflexivity. Qed.

Theorem strlen_welltyped: welltyped_prog x64typctx strlen_amd64.
Proof. exact welltyped. Qed.

Theorem strlen_preserves_memory:
  forall_endstates strlen_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* bytes p+0 .. p+k-1 are all nonzero *)
Definition nilfree (m:memory) (p k:N) := forall i, i < k -> m Ⓑ[p ⊕ i] <> 0.

Lemma nilfree_succ: forall m p k, nilfree m p k -> m Ⓑ[p ⊕ k] <> 0 -> nilfree m p (k + 1).
Proof. intros m p k NF B i I. destruct (N.lt_ge_cases i k). apply NF. assumption. replace i with k by lia. exact B. Qed.

(* A terminated scan never runs past 2^64 bytes. *)
Lemma nilfree_bound: forall m p k, nilfree m p k -> m Ⓑ[p ⊕ k] = 0 -> k < 2^64.
Proof.
  intros m p k NF Z. destruct (N.lt_ge_cases k (2^64)) as [|K]. assumption.
  exfalso. apply (NF (k mod 2^64)). eapply N.lt_le_trans. apply N.mod_lt. discriminate. exact K.
  rewrite N.add_mod_idemp_r by discriminate. exact Z.
Qed.

Definition strlen_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13492c => true
  | _ => false end | _ => false end.

Definition strlen_post (s0:store) (m p:N) (s:store) :=
  (exists k, s R_RAX = k /\ nilfree m p k /\ m Ⓑ[p ⊕ k] = 0) /\
  s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strlen_invs (s0:store) (m p:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1348c0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  (* the alignment loop, the word loop and the final byte loop *)
  | 0x1348d4 | 0x134924 =>
      Some (exists k, s R_RAX = p ⊕ k /\ nilfree m p k /\
            s V_MEM64 = m /\ s R_R8 = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134904 =>
      Some (exists k, s R_RAX = p ⊕ k /\ nilfree m p k /\
            s R_RDI = 0xfefefefefefefeff /\ s R_RSI = 0x8080808080808080 /\
            s V_MEM64 = m /\ s R_R8 = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13492c => Some (strlen_post s0 m p s)
  | _ => None
  end | _ => None end.

(* The RAX - p subtraction at the exit. *)
Lemma strlen_ret:
  forall m p k, p < 2^64 -> nilfree m p k -> m Ⓑ[p ⊕ k] = 0 -> msub 64 (p ⊕ k) p = k.
Proof.
  intros m p k P NF Z. pose proof (nilfree_bound m p k NF Z).
  unfold msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma byte_load_off: forall (m:memory) p k, m Ⓑ[p ⊕ k] = m Ⓑ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Ltac strlen_frame := split; [reflexivity || assumption|]; callee_saved_tac.

Theorem strlen_correct:
  forall prog s t s' x' m p
         (STRLEN: strlen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1348c0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p),
  satisfies_all prog (strlen_invs s m p) strlen_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p STRLEN ENTRY MDL MEM P.
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strlen_amd64); [exact STRLEN| |].
    intros a s1 t1 EXIT NOCODE. unfold strlen_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p MDL MEM P PB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; try assumption; apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strlen_welltyped. intro MDL1.
  clear - PRE MDL1 PB. rename t1 into t.
  destruct_inv 64 PRE.

  - (* entry *)
    destruct PRE as [MEM [P [RSP CS]]].
    repeat x64_step.
    exists 0. rewrite N.add_0_r, N.mod_small by assumption.
    split. reflexivity. split. intros i I. lia.
    conj_tac.

  - (* alignment loop *)
    destruct PRE as [k [RAX [NF [MEM [R8 [RSP CS]]]]]].
    repeat x64_step. all: bc_norm.
    + (* aligned: enter the word loop *)
      exists k. conj_tac.
    + (* zero byte: return k *)
      rewrite <- byte_load_off in BC0.
      split. exists k. split. apply N.mod_small, (nilfree_bound m p); assumption.
      split; assumption. conj_tac.
    + (* nonzero byte: advance *)
      rewrite <- byte_load_off in BC0.
      exists (k + 1). split. f_equal. lia. split. apply nilfree_succ; assumption. conj_tac.
  - (* word loop *)
    destruct PRE as [k [RAX [NF [RDI [RSI [MEM [R8 [RSP CS]]]]]]]].
    repeat x64_step. all: bc_norm.
    + (* no zero byte in this quadword: advance by 8 *)
      exists (k + 8). split. f_equal. lia. split. intros i I. apply (nilfree_add8 m p k NF BC i I). conj_tac.
    + (* maybe a zero byte: hand over to the byte loop *)
      exists k. conj_tac.
  - (* final byte loop *)
    destruct PRE as [k [RAX [NF [MEM [R8 [RSP CS]]]]]].
    repeat x64_step. all: bc_norm.
    + rewrite <- byte_load_off in BC.
      split. exists k. split. apply N.mod_small, (nilfree_bound m p); assumption.
      split; assumption. conj_tac.
    + rewrite <- byte_load_off in BC.
      exists (k + 1). split. f_equal. lia. split. apply nilfree_succ; assumption. conj_tac.
Qed.

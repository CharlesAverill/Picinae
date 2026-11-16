(* strcmp -- compare two strings (musl x86_64, C)

   SEMANTICS
   ---------
   musl's strcmp (src/string/strcmp.c) is

       for (; *l==*r && *l; l++, r++);
       return *(unsigned char * )l - *(unsigned char * )r;

   GCC keeps one index in RAX and compares l[i] with r[i] byte by byte; at the
   first difference (or common terminator) it returns the difference of the
   two bytes, as unsigned chars promoted to int.

   SPECIFICATION (man 3 strcmp, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            int strcmp(const char *s1, const char *s2);

     DESCRIPTION
            The strcmp() function compares the two strings s1 and s2.  The
            locale is not taken into account (for a locale-aware comparison,
            see strcoll(3)).  The comparison is done using unsigned
            characters.
            strcmp() returns an integer indicating the result of the
            comparison, as follows:
            •  0, if the s1 and s2 are equal;
            •  a negative value if s1 is less than s2;
            •  a positive value if s1 is greater than s2.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strcmp at 0x34880 (Ghidra image base 0x100000: 0x134880)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/strcmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s1, RSI = s2; m = memory on entry.  No precondition.
   Output:  At the RET (0x1348bd) there is an index K such that for every
            i < K the bytes s1[i] and s2[i] are equal and nonzero, and either
            s1[K] <> s2[K] or s1[K] = s2[K] = 0 (strcmp_stop); and
            EAX = s1[K] - s2[K] as a 32-bit two's-complement int (RAX is its
            zero extension), so the sign of the result is the sign of
            s1[K] - s2[K] as unsigned chars (strcmp_sign).  RSP and RBX, RBP,
            R12-R15 are unchanged; memory is unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strcmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem strcmp_nwc: forall s2 s1, strcmp_amd64 s1 = strcmp_amd64 s2.
Proof. reflexivity. Qed.

Theorem strcmp_welltyped: welltyped_prog x64typctx strcmp_amd64.
Proof. exact welltyped. Qed.

Theorem strcmp_preserves_memory:
  forall_endstates strcmp_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* the strings agree, without a terminator, on [0,k) *)
Definition same_prefix (m:memory) (l r k:N) :=
  forall i, i < k -> m Ⓑ[l ⊕ i] = m Ⓑ[r ⊕ i] /\ m Ⓑ[l ⊕ i] <> 0.

(* K is where strcmp stops *)
Definition strcmp_stop (m:memory) (l r K:N) :=
  same_prefix m l r K /\ (m Ⓑ[l ⊕ K] <> m Ⓑ[r ⊕ K] \/ m Ⓑ[l ⊕ K] = 0).

Definition strcmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1348bd => true
  | _ => false end | _ => false end.

Definition strcmp_post (s0:store) (m l r:N) (s:store) :=
  (exists K, strcmp_stop m l r K /\ s R_RAX = msub 32 (m Ⓑ[l ⊕ K]) (m Ⓑ[r ⊕ K])) /\
  s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strcmp_invs (s0:store) (m l r:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x134880 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1348a0 => Some (exists k, s R_RAX = k mod 2^64 /\ same_prefix m l r k /\
                      s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1348bd => Some (strcmp_post s0 m l r s)
  | _ => None
  end | _ => None end.

Lemma byte_load_off: forall (m:memory) p k, m Ⓑ[p ⊕ k] = m Ⓑ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Lemma byte_idx: forall (m:memory) p k, m Ⓑ[p + k mod 2^64] = m Ⓑ[p ⊕ k].
Proof.
  intros. rewrite <- (getmem_mod_l _ _ _ m (p + k mod 2^64)), N.add_mod_idemp_r by discriminate.
  reflexivity.
Qed.

Theorem strcmp_correct:
  forall prog s t s' x' m l r
         (STRCMP: strcmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x134880, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r),
  satisfies_all prog (strcmp_invs s m l r) strcmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r STRCMP ENTRY MDL MEM L R.
  eapply satisfies_all_pmono with (p1:=strcmp_amd64); [exact STRCMP| |].
    intros a s1 t1 EXIT NOCODE. unfold strcmp_invs.
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
  eapply models_at_invariant; try eassumption. apply strcmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  - (* entry *)
    destruct PRE as [MEM [L [R [RSP CS]]]].
    repeat x64_step.
    exists 0. split. reflexivity. split. intros i I. lia. conj_tac.

  - (* loop *)
    destruct PRE as [k [RAX [SP [MEM [L [R [RSP CS]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?byte_load_off in *.
    + (* common terminator *)
      split. exists k. split. split. assumption. right. rewrite BC. assumption.
      rewrite BC, BC0. reflexivity. conj_tac.
    + (* equal nonzero bytes: advance *)
      exists (k + 1). split. rewrite N.add_comm. reflexivity.
      split. intros i I. destruct (N.lt_ge_cases i k). apply SP. assumption.
        replace i with k by lia. split. assumption. rewrite BC. assumption.
      conj_tac.
    + (* first difference *)
      split. exists k. split. split. assumption. left. assumption. reflexivity. conj_tac.
Qed.

(* EAX read as a signed int is exactly s1[K] - s2[K]. *)
Theorem strcmp_sign:
  forall a b, a < 256 -> b < 256 -> toZ 32 (msub 32 a b) = (Z.of_N a - Z.of_N b)%Z.
Proof.
  intros a b A B. rewrite toZ_msub. unfold toZ, canonicalZ.
  change (Z.pred (Z.of_N 32)) with 31%Z. change (Z.of_N 32) with 32%Z.
  change (2^31)%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z.
  lia.
Qed.

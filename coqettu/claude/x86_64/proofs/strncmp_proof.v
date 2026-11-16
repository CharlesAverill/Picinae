(* strncmp -- compare at most n bytes of two strings (musl x86_64, C)

   SEMANTICS
   ---------
   musl's strncmp (src/string/strncmp.c) is

       const unsigned char *l=(void * )_l, *r=(void * )_r;
       if (!n--) return 0;
       for (; *l && *r && n && *l == *r ; l++, r++, n--);
       return *l - *r;

   GCC keeps one index RCX and the bound n-1 in RDX; the loop continues while
   l[i] <> 0, r[i] <> 0, l[i] = r[i] and i <> n-1.

   SPECIFICATION (man 3 strncmp, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <string.h>
            int strncmp(const char s1[.n], const char s2[.n], size_t n);

     DESCRIPTION
            The strncmp() function is similar, except it compares only the
            first (at most) n bytes of s1 and s2.

     RETURN VALUE
            The strcmp() and strncmp() functions return an integer less
            than, equal to, or greater than zero if s1 (or the first n bytes
            thereof) is found, respectively, to be less than, to match, or be
            greater than s2.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strncmp at 0x24480 (Ghidra image base 0x100000: 0x124480)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/strncmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s1, RSI = s2, RDX = n; m = memory.  No precondition.
   Output:  At the RET (0x1244f1): if n = 0 then RAX = 0.  Otherwise there is
            K < n with s1[i] = s2[i] <> 0 for i < K, and s1[K] = 0, or
            s1[K] <> s2[K], or K = n-1 (strncmp_stop); and EAX = s1[K] - s2[K]
            as a 32-bit int (RAX its zero extension).  Memory, RSP and RBX,
            RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strncmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem strncmp_nwc: forall s2 s1, strncmp_amd64 s1 = strncmp_amd64 s2.
Proof. reflexivity. Qed.

Theorem strncmp_welltyped: welltyped_prog x64typctx strncmp_amd64.
Proof. exact welltyped. Qed.

Definition nsame_prefix (m:memory) (l r k:N) :=
  forall i, i < k -> m Ⓑ[l ⊕ i] = m Ⓑ[r ⊕ i] /\ m Ⓑ[l ⊕ i] <> 0.

Definition strncmp_stop (m:memory) (l r n K:N) :=
  K < n /\ nsame_prefix m l r K /\
  (m Ⓑ[l ⊕ K] = 0 \/ m Ⓑ[l ⊕ K] <> m Ⓑ[r ⊕ K] \/ K = n - 1).

Definition strncmp_result (m:memory) (l r n v:N) :=
  (n = 0 /\ v = 0) \/
  (exists K, strncmp_stop m l r n K /\ v = msub 32 (m Ⓑ[l ⊕ K]) (m Ⓑ[r ⊕ K])).

Definition strncmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1244f1 => true
  | _ => false end | _ => false end.

Definition strncmp_post (s0:store) (m l r n:N) (s:store) :=
  strncmp_result m l r n (s R_RAX) /\
  s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strncmp_invs (s0:store) (m l r n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x124480 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1244c0 => Some (exists k, k < n /\ s R_RCX = k /\ s R_RDX = n - 1 /\ nsame_prefix m l r k /\
                      s R_R9 = l /\ s R_R10 = r /\
                      s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1244f1 => Some (strncmp_post s0 m l r n s)
  | _ => None
  end | _ => None end.

Lemma byte_load_off: forall (m:memory) p k, m Ⓑ[p ⊕ k] = m Ⓑ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Theorem strncmp_correct:
  forall prog s t s' x' m l r n
         (STRNCMP: strncmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x124480, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r) (Nn: s R_RDX = n),
  satisfies_all prog (strncmp_invs s m l r n) strncmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r n STRNCMP ENTRY MDL MEM L R Nn.
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strncmp_amd64); [exact STRNCMP| |].
    intros a s1 t1 EXIT NOCODE. unfold strncmp_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m l r n MDL MEM L R Nn NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncmp_welltyped. intro MDL1.
  clear - PRE MDL1 NB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [L [R [Nn [RSP CS]]]]].
    repeat x64_step. all: bc_norm.
    + split. left. split. assumption. reflexivity. conj_tac.
    + exists 0. split. lia. split. reflexivity.
      split. rewrite msub_nowrap; rewrite !N.mod_small; change (2^64) with 18446744073709551616 in *; lia.
      split. intros i I. lia. conj_tac.
  - destruct PRE as [k [KN [RCX [RDX [SP [R9 [R10 [MEM [RSP CS]]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?byte_load_off in *.
    all: lazymatch goal with
    | |- exists _, _ =>
        exists (k + 1); split; [lia|]; split; [rewrite N.add_comm; apply N.mod_small; lia|];
        split; [reflexivity|];
        split; [intros i I; destruct (N.lt_ge_cases i k); [apply SP; assumption|];
                replace i with k by lia; split; assumption|];
        conj_tac
    | _ =>
        split; [ right; exists k; split;
                 [ split; [lia|]; split; [assumption|];
                   first [ left; assumption | right; left; assumption | right; right; lia
                         | exfalso; congruence ]
                 | first [ reflexivity | rewrite BC; reflexivity | exfalso; congruence ] ] |];
        conj_tac
    end.
Qed.

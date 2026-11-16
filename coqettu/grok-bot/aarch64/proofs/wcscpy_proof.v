(* wcscpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/string/wcscpy.c:
       wchar_t *wcscpy(wchar_t *restrict d, const wchar_t *restrict s)
       {
           wchar_t *a = d;
           while ((d[0] = s[0])) d++, s++;
           return a;
       }
   (equivalent to musl's one-line loop that copies and post-increments; written so
   this comment stays well-formed.)  The binary keeps a byte offset
   x2 = 4k and copies the word at x1 + x2 to x0 + x2 until it copied a 0.

   SPECIFICATION (man 3 wcscpy, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t *wcscpy(wchar_t *restrict dest, const wchar_t *restrict src);

     DESCRIPTION
            The wcscpy() function is the wide-character equivalent of the
            strcpy(3) function.  It copies the wide-character string pointed
            to by src, including the terminating null wide character (L'\0'),
            to the array pointed to by dest.
            The strings may not overlap.
            The programmer must ensure that there is room for at least
            wcslen(src)+1 wide characters at dest.

     RETURN VALUE
            wcscpy() returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcscpy at 0x5fb2c (ELF vaddr); 0x15fb2c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wcscpy_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest = d, X1 = src = q; X30 = return address raddr; SP = sp;
            m = memory on entry.
   Output:  If execution reaches the RET (0x15fb40): X0 = d and there is k
            such that, with m_i = wcpy m d q i (the memory after copying the
            words q+4j to d+4j for j < i, in order, each read from the
            current memory):
              - m_i[q+4i] <> 0 for all i < k (wnz),
              - m_k[q+4k] = 0, and
              - final memory = m_(k+1)
            (32-bit little-endian words, addresses mod 2^64).  For
            non-overlapping strings this is "copy src up to and including its
            terminator".  SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wcscpy_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

Theorem wcscpy_welltyped: welltyped_prog arm8typctx wcscpy_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wcscpy_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wcscpy_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wcscpy_preserves_x30:
  forall_endstates wcscpy_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Lemma getmem_add_mod64: ∀ e len m a x, getmem 64 e len m (a + x mod 2^64) = getmem 64 e len m (a + x).
Proof. intros. rewrite <- getmem_mod_l, N.Div0.add_mod_idemp_r, getmem_mod_l. reflexivity. Qed.

Lemma setmem_add_mod64: ∀ e len m a x v, setmem 64 e len m (a + x mod 2^64) v = setmem 64 e len m (a + x) v.
Proof. intros. rewrite <- setmem_mod_l, N.Div0.add_mod_idemp_r, setmem_mod_l. reflexivity. Qed.

(* wcpy m d q k: memory after copying the 32-bit words at q+4i to d+4i for
   i = 0..k-1 in increasing order, each word read from the memory produced
   by the previous copies (addresses mod 2^64 via getmem/setmem). *)
Fixpoint wcpy (m:memory) (d q:N) (k:nat) : memory :=
  match k with
  | O => m
  | S k' => let m' := wcpy m d q k' in m' [Ⓓ d + 4 * N.of_nat k' := m' Ⓓ[q + 4 * N.of_nat k']]
  end.

(* The i-th source word, as read by the copy loop, is non-zero for all i < k. *)
Definition wnz (m:memory) (d q:N) (k:N) := ∀ i, i < k -> wcpy m d q (N.to_nat i) Ⓓ[q + 4*i] ≠ 0.

Lemma wnz_succ: ∀ m d q k, wnz m d q k -> wcpy m d q (N.to_nat k) Ⓓ[q + 4*k] ≠ 0 -> wnz m d q (k+1).
Proof.
  unfold wnz. intros m d q k NZ B i I.
  destruct (N.lt_ge_cases i k). apply NZ; assumption. replace i with k by lia. exact B.
Qed.

Lemma test32: ∀ x b, x < 2^32 -> negb ((x >> 0) mod 2^32 =? 0) = b -> (b = true /\ x ≠ 0) \/ (b = false /\ x = 0).
Proof.
  intros x b X B. rewrite N.shiftr_0_r, N.mod_small in B by exact X.
  destruct (N.eqb_spec x 0); subst b; simpl; [right|left]; split; auto.
Qed.

Section Invariants.
  Variables (sp mem raddr d q : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15fb2c => Inv 0 (s R_X0 = d /\ s R_X1 = q /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15fb30 => Inv 0 (∃ k, s R_X2 = (4*k) mod 2^64 /\ s R_X0 = d /\ s R_X1 = q /\ wnz mem d q k /\
                         s V_MEM64 = wcpy mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x15fb40 => Post 0 (∃ k, wnz mem d q k /\ wcpy mem d q (N.to_nat k) Ⓓ[q + 4*k] = 0 /\
                          s V_MEM64 = wcpy mem d q (N.to_nat (k+1)) /\
                          s R_X0 = d /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition wcscpy_exits := make_exits 0 wcscpy_armv8 invs.
  Definition wcscpy_invs := make_invs 0 wcscpy_armv8 invs.
End Invariants.

Theorem wcscpy_partial_correctness:
  ∀ prog s sp mem raddr d q t xs'
    (PROG: wcscpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fb2c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q),
  satisfies_all prog (wcscpy_invs sp mem raddr d q) (wcscpy_exits sp mem raddr d q) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wcscpy_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wcscpy_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscpy_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30).
    repeat arm8_step.
    exists 0. repeat split; try assumption. unfold wnz. intros. lia.
  - destruct PRE as (k & X2 & X0 & X1 & NZ & MEM & SP & X30).
    repeat arm8_step.
    all: pose proof (getmem_bound 64 LittleE 4 (wcpy mem d q (N.to_nat k)) (q + 4*k)) as B;
         change (2^(4*8)) with (2^32) in B;
         destruct (test32 _ _ B BC) as [[T NZK] | [T ZK]]; try discriminate T.
    + exists (k+1). repeat split.
      all: first
        [ assumption
        | apply wnz_succ; assumption
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wcpy]; rewrite ?N2Nat.id; reflexivity
        | f_equal; lia ].
    + exists k. repeat split.
      all: first
        [ assumption
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wcpy]; rewrite ?N2Nat.id; reflexivity ].
Qed.

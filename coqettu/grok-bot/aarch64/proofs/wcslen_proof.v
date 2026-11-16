(* wcslen -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/string/wcslen.c is

       size_t wcslen(const wchar_t *s)
       { const wchar_t *a; for (a=s; *s; s++); return s-a; }

   compiled to an 8-instruction loop: X1 walks the string four bytes (one
   wchar_t) at a time with LDR W2,[X1]; CBNZ W2 loops back; on the first zero
   word it returns (X1 - X0) >>arith 2 (the pointer difference divided by
   sizeof(wchar_t) = 4).  wchar_t is a 32-bit type on aarch64.

   SPECIFICATION (man 3 wcslen, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            size_t wcslen(const wchar_t *s);

     DESCRIPTION
            The  wcslen() function is the wide-character equivalent of the strlen(3)
            function.  It determines the length of the wide-character string pointed
            to by s, excluding the terminating null wide character (L'\0').

     RETURN VALUE
            The wcslen() function returns the number of wide characters in s.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcslen at 0x5fc18 (ELF vaddr); 0x15fc18 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py
            from picinae-llm/tools/ghidra-lifter (repo HEAD a4bae9c), options
            --globalAddressing --typeCheck; see ../lifted/wcslen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s; X30 = return address; m = memory on entry.  No assumption
            is made about the string (in particular, not its length).
   Output:  If execution reaches the RET (0x15fc34), then for some k < 2^62:
            the 32-bit words at s, s+4, ..., s+4(k-1) are all non-zero, the word
            at s+4k is zero (so k is the wide-string length), and
            X0 = (4k) >>arith 2 (sign-extending 64-bit shift).  Hence
            X0 = k whenever k < 2^61 (always true on real hardware, where a
            string cannot span 2^63 bytes); see wcslen_result_small.  Memory,
            SP, X30 and all AAPCS64 callee-saved registers are unchanged.
   Note:    For a (physically impossible) string of >= 2^61 wide characters
            the binary returns k with the top two bits set, because it computes
            the signed pointer difference; this matches the C source, where the
            ptrdiff_t subtraction would overflow.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wcslen_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* The first k wide characters starting at p are all non-zero. *)
Definition wcs_nilfree (m:memory) (p:addr) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] ≠ 0.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem wcslen_nwc: ∀ s2 s1, wcslen_armv8 s1 = wcslen_armv8 s2.
Proof. reflexivity. Qed.

Theorem wcslen_welltyped: welltyped_prog arm8typctx wcslen_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wcslen_preserves_memory:
  forall_endstates wcslen_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wcslen_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wcslen_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wcslen_preserves_x30:
  forall_endstates wcslen_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants                                                              *)

Section Invariants.
  Variables (sp mem raddr p : N).

  Definition wcslen_post (s:store) :=
    ∃ k, k < 2^62 /\ s R_X0 = ashiftr 64 (4*k) 2 /\
         wcs_nilfree mem p k /\ mem Ⓓ[p + 4*k] = 0 /\
         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr.

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* entry *)
    | 0x15fc18 => Inv 0 (s R_X0 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* loop head: ldr w2,[x1] *)
    | 0x15fc24 => Inv 0 (∃ k, k < 2^62 /\ s R_X0 = p /\ s R_X1 = p ⊕ 4*k /\
                         wcs_nilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* ret *)
    | 0x15fc34 => Post 0 (wcslen_post s)
    | _ => NoInv
    end.

  Definition wcslen_exits := make_exits 0 wcslen_armv8 invs.
  Definition wcslen_invs := make_invs 0 wcslen_armv8 invs.
End Invariants.

(* ---------------------------------------------------------------------- *)
(* Partial correctness                                                     *)

Theorem wcslen_partial_correctness:
  ∀ prog s sp mem raddr p t xs'
    (PROG: wcslen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fc18, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = p),
  satisfies_all prog (wcslen_invs sp mem raddr p) (wcslen_exits sp mem raddr p) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wcslen_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wcslen_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcslen_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  (* entry -> loop head with k = 0 *)
  - destruct PRE as (X0 & MEM & SP & X30).
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    arm8_step. arm8_step.
    exists 0. repeat split; try assumption.
    rewrite N.mul_0_r, N.add_0_r. symmetry. apply N.mod_small. exact P64.
    intros i H. destruct i; discriminate.

  (* loop head *)
  - destruct PRE as (k & KLT & X0 & X1 & NF & MEM & SP & X30).
    arm8_step. arm8_step.
    (* non-zero word: advance (wrapping k to 0 if the scan has covered the
       whole address space, where nothing new is learned) *)
    + arm8_step.
      apply cbnz32_true in BC; [|apply dword_lt32].
      destruct (N.lt_ge_cases (k+1) (2^62)) as [LT|GE].
      * exists (k+1). repeat split; try assumption.
        f_equal. lia.
        intros i Hi. destruct (N.lt_ge_cases i k). apply NF; assumption.
          replace i with k by lia. exact BC.
      * exists 0. repeat split; try assumption.
        assert (E: 4 + p + 4*k = p + 2^64) by lia. rewrite E, add_wrap_full. f_equal; lia.
        intros i Hi. destruct i; discriminate.
    (* zero word: return *)
    + arm8_step. arm8_step.
      apply cbnz32_false in BC; [|apply dword_lt32].
      exists k. repeat split; assumption.
Qed.

(* On any realistic string the returned value is exactly the length. *)
Theorem wcslen_result_small:
  ∀ k, k < 2^61 -> ashiftr 64 (4*k) 2 = k.
Proof.
  intros k LT. rewrite ashiftr64_small by lia.
  rewrite N.shiftr_div_pow2. change (2^2) with 4. rewrite N.mul_comm, N.div_mul by discriminate.
  reflexivity.
Qed.

(* The k in the post-condition is uniquely the wide-string length: it is the
   first index whose word is zero. *)
Theorem wcslen_post_unique:
  ∀ m p k1 k2,
    wcs_nilfree m p k1 -> m Ⓓ[p + 4*k1] = 0 ->
    wcs_nilfree m p k2 -> m Ⓓ[p + 4*k2] = 0 -> k1 = k2.
Proof.
  intros m p k1 k2 NF1 Z1 NF2 Z2.
  destruct (N.lt_trichotomy k1 k2) as [H|[H|H]].
    exfalso. exact (NF2 k1 H Z1).
    exact H.
    exfalso. exact (NF1 k2 H Z2).
Qed.

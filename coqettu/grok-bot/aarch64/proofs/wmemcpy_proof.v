(* wmemcpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/string/wmemcpy.c:
       wchar_t *wmemcpy(wchar_t *restrict d, const wchar_t *restrict s, size_t n)
       {
           wchar_t *a = d;
           while (n--) d[0] = s[0], d++, s++;
           return a;
       }
   (written with d[0]/s[0] so this comment stays well-formed.)  The binary
   keeps an index x3 = 0..n and copies the word at x1 + 4*x3 to x0 + 4*x3.

   SPECIFICATION (man 3 wmemcpy, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            wchar_t *wmemcpy(wchar_t dest[restrict .n],
                             const wchar_t src[restrict .n], size_t n);

     DESCRIPTION
            The wmemcpy() function is the wide-character equivalent of the
            memcpy(3) function.  It copies n wide characters from the array
            starting at src to the array starting at dest.
            The arrays may not overlap; use wmemmove(3) to copy between
            overlapping arrays.

     RETURN VALUE
            wmemcpy() returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wmemcpy at 0x6022c (ELF vaddr); 0x16022c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/wmemcpy_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest = d, X1 = src = q, X2 = n; X30 = return address raddr;
            SP = sp; m = memory on entry.
   Output:  If execution reaches the RET (0x160248): X0 = d and memory =
            wcpy m d q n: the result of copying the 32-bit words at q+4i to
            d+4i for i = 0..n-1 in increasing order, each word read from the
            memory produced by the previous copies (addresses mod 2^64).
            This is exactly the C loop's behaviour even for overlapping
            arrays (which the man page leaves undefined); for non-overlapping
            arrays it is the usual copy.  SP, X30 and the AAPCS64
            callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wmemcpy_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

Theorem wmemcpy_welltyped: welltyped_prog arm8typctx wmemcpy_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wmemcpy_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wmemcpy_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wmemcpy_preserves_x30:
  forall_endstates wmemcpy_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* wcpy m d q k: the memory after copying k 32-bit words from q to d one at a
   time in increasing order (word i is read from the memory produced by the
   first i copies, as the C loop does).  Addresses mod 2^64 (setmem/getmem). *)
Fixpoint wcpy (m:memory) (d q:N) (k:nat) : memory :=
  match k with
  | O => m
  | S k' => let m' := wcpy m d q k' in m' [Ⓓ d + (N.of_nat k' << 2) := m' Ⓓ[q + (N.of_nat k' << 2)]]
  end.

Section Invariants.
  Variables (sp mem raddr d q n : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x16022c => Inv 0 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160240 => Inv 0 (∃ k, k <= n /\ s R_X3 = k /\ s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\
                         s V_MEM64 = wcpy mem d q (N.to_nat k) /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160248 => Post 0 (s R_X0 = d /\ s V_MEM64 = wcpy mem d q (N.to_nat n) /\
                          s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition wmemcpy_exits := make_exits 0 wmemcpy_armv8 invs.
  Definition wmemcpy_invs := make_invs 0 wmemcpy_armv8 invs.
End Invariants.

Theorem wmemcpy_partial_correctness:
  ∀ prog s sp mem raddr d q n t xs'
    (PROG: wmemcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x16022c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X1: s R_X1 = q) (X2: s R_X2 = n),
  satisfies_all prog (wmemcpy_invs sp mem raddr d q n) (wmemcpy_exits sp mem raddr d q n) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wmemcpy_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wmemcpy_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemcpy_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
    repeat arm8_step.
    exists 0. repeat split; try assumption; try lia.
  - destruct PRE as (k & KLE & X3 & X0 & X1 & X2 & MEM & SP & X30).
    pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
    repeat arm8_step.
    all: destruct (n =? k) eqn:E; try discriminate.
    + apply N.eqb_eq in E. rewrite <- E in MEM. repeat split; assumption.
    + apply N.eqb_neq in E. exists (k+1). repeat split; try assumption; try lia.
      all: first
        [ rewrite N.add_comm; apply N.mod_small; lia
        | replace (N.to_nat (k+1)) with (S (N.to_nat k)) by lia; cbn [wcpy];
          rewrite N2Nat.id; first [ reflexivity | rewrite (N.add_comm d), (N.add_comm q); reflexivity | rewrite (N.add_comm d); reflexivity ] ].
Qed.

(* wcscmp -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/string/wcscmp.c is

       int wcscmp(const wchar_t *l, const wchar_t *r)
       { for (; *l==*r && *l && *r; l++, r++);
         return *l < *r ? -1 : *l > *r; }

   On aarch64 wchar_t is a 32-bit unsigned type.  The code keeps a byte
   offset X2 (step 4): W3 = l[X2], W4 = r[X2], X2 += 4, CMP W3,W4; B.NE to
   the exit; CBNZ W3 loops.  The exit does CMP W4,W3; CSET W0,CC;
   CSINV W0,W0,WZR,LS, which yields 1 if W3 > W4, 0 if equal and
   0xffffffff (-1) if W3 < W4 (unsigned).

   LIFTER NOTE: the upstream Picinae lifter translates p-code BOOL_NEGATE as
   bitwise NOT, which made CSET W0,CC produce 254/255; the lift used here
   comes from our patched lifter copy (../lifter/README_GROK.md), which uses
   XOR 1.  With the upstream lift this theorem is false (it would return 254
   for equal strings).

   SPECIFICATION (man 3 wcscmp, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <wchar.h>
            int wcscmp(const wchar_t *s1, const wchar_t *s2);

     DESCRIPTION
            The  wcscmp() function is the wide-character equivalent of the strcmp(3)
            function.  It compares the wide-character string pointed to  by  s1  and
            the wide-character string pointed to by s2.

     RETURN VALUE
            The  wcscmp()  function returns zero if the wide-character strings at s1
            and s2 are equal.  It returns an integer greater than  zero  if  at  the
            first  differing  position  i, the corresponding wide-character s1[i] is
            greater than s2[i].  It returns an integer less  than  zero  if  at  the
            first  differing  position  i, the corresponding wide-character s1[i] is
            less than s2[i].

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            wcscmp at 0x5fb00 (ELF vaddr); 0x15fb00 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix), options --globalAddressing --typeCheck;
            see ../lifted/wcscmp_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s1, X1 = s2; X30 = return address; m = memory on entry.
            Nothing is assumed about the strings.
   Output:  If execution reaches the RET (0x15fb28), there is a k such that
            the 32-bit words s1[i], s2[i] (at s+4i) agree and are non-zero for
            all i < k, and at index k they differ or are both 0; and
            X0 = ucmp32 s1[k] s2[k], i.e. 0xffffffff, 0 or 1 according to the
            unsigned comparison s1[k] <, =, > s2[k]; as a signed int this is
            -1, 0, 1 (wcscmp_result_sign).  Memory, SP, X30 and the AAPCS64
            callee-saved registers are unchanged.  Addresses wrap mod 2^64.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import wcscmp_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem wcscmp_nwc: ∀ s2 s1, wcscmp_armv8 s1 = wcscmp_armv8 s2.
Proof. reflexivity. Qed.

Theorem wcscmp_welltyped: welltyped_prog arm8typctx wcscmp_armv8.
Proof. Picinae_typecheck. Qed.

Theorem wcscmp_preserves_memory:
  forall_endstates wcscmp_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wcscmp_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates wcscmp_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem wcscmp_preserves_x30:
  forall_endstates wcscmp_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification helpers                                                   *)

(* The first k wide characters at p and q agree / are non-zero. *)
Definition wmem_eq (m:memory) (p q:addr) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] = m Ⓓ[q + 4*i].
Definition wnilfree (m:memory) (p:addr) (k:N) := ∀ i, i < k -> m Ⓓ[p + 4*i] ≠ 0.

(* Three-way unsigned comparison returned as a 32-bit int (-1 = 2^32-1). *)
Definition ucmp32 (a b : N) : N :=
  match N.compare a b with Lt => 2^32 - 1 | Eq => 0 | Gt => 1 end.

Lemma wcscmp_lt: ∀ a b,
  (if a <=? b then 0 else 1) .| (if b =? a then 1 else 0) = 0 -> 4294967295 = ucmp32 a b.
Proof.
  intros a b H. unfold ucmp32.
  destruct (a <=? b) eqn:H1, (b =? a) eqn:H2; try discriminate H.
  apply N.leb_le in H1. apply N.eqb_neq in H2.
  rewrite (proj2 (N.compare_lt_iff a b)) by lia. reflexivity.
Qed.

Lemma wcscmp_ge: ∀ a b n,
  (if a <=? b then 0 else 1) .| (if b =? a then 1 else 0) = N.pos n ->
  (if a <=? b then 0 else 1) = ucmp32 a b.
Proof.
  intros a b n H. unfold ucmp32.
  destruct (a <=? b) eqn:H1, (b =? a) eqn:H2; try discriminate H.
  - apply N.eqb_eq in H2. subst. rewrite N.compare_refl. reflexivity.
  - apply N.leb_gt in H1. rewrite (proj2 (N.compare_gt_iff a b)) by lia. reflexivity.
  - apply N.leb_gt in H1. rewrite (proj2 (N.compare_gt_iff a b)) by lia. reflexivity.
Qed.

Section Invariants.
  Variables (sp mem raddr p q : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* entry *)
    | 0x15fb00 => Inv 0 (s R_X0 = p /\ s R_X1 = q /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* loop head: ldr w3,[x0,x2] *)
    | 0x15fb04 => Inv 0 (∃ k, k < 2^62 /\ s R_X0 = p /\ s R_X1 = q /\ s R_X2 = 4*k /\
                         wmem_eq mem p q k /\ wnilfree mem p k /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* join before the three-way result computation: cmp w4,w3 *)
    | 0x15fb1c => Inv 0 (∃ k, wmem_eq mem p q k /\ wnilfree mem p k /\
                    (mem Ⓓ[p+4*k] ≠ mem Ⓓ[q+4*k] \/ mem Ⓓ[p+4*k] = 0 /\ mem Ⓓ[q+4*k] = 0) /\
                    s R_X3 = mem Ⓓ[p+4*k] /\ s R_X4 = mem Ⓓ[q+4*k] /\
                    s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* ret *)
    | 0x15fb28 => Post 0 (∃ k, wmem_eq mem p q k /\ wnilfree mem p k /\
                    (mem Ⓓ[p+4*k] ≠ mem Ⓓ[q+4*k] \/ mem Ⓓ[p+4*k] = 0 /\ mem Ⓓ[q+4*k] = 0) /\
                    s R_X0 = ucmp32 (mem Ⓓ[p+4*k]) (mem Ⓓ[q+4*k]) /\
                    s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition wcscmp_exits := make_exits 0 wcscmp_armv8 invs.
  Definition wcscmp_invs := make_invs 0 wcscmp_armv8 invs.
End Invariants.


Theorem wcscmp_partial_correctness:
  ∀ prog s sp mem raddr p q t xs'
    (PROG: wcscmp_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15fb00, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = q),
  satisfies_all prog (wcscmp_invs sp mem raddr p q) (wcscmp_exits sp mem raddr p q) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=wcscmp_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold wcscmp_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & SP & X30).
    repeat arm8_step.
    exists 0. repeat split; try assumption.
    all: first [ intros i Hi; destruct i; discriminate | reflexivity ].
  - destruct PRE as (k & KLT & X0 & X1 & X2 & EQ & NF & MEM & SP & X30).
    repeat arm8_step.
    + (* equal non-zero words: loop *)
      apply N.eqb_eq in BC. apply cbnz32_true in BC0; [|apply dword_lt32].
      assert (EQ': wmem_eq mem p q (k+1)).
        intros i Hi. destruct (N.lt_ge_cases i k). apply EQ; assumption.
        replace i with k by lia. exact BC.
      assert (NF': wnilfree mem p (k+1)).
        intros i Hi. destruct (N.lt_ge_cases i k). apply NF; assumption.
        replace i with k by lia. exact BC0.
      destruct (N.lt_ge_cases (k+1) (2^62)) as [LT|GE].
      * exists (k+1). repeat split; try assumption.
        rewrite N.mod_small by lia. lia.
      * exists 0. repeat split; try assumption.
        all: first [ intros i Hi; destruct i; discriminate | reflexivity
                   | replace (4 + 4*k) with (2^64) by lia; reflexivity ].
    + (* equal zero words *)
      apply N.eqb_eq in BC. apply cbnz32_false in BC0; [|apply dword_lt32].
      exists k. repeat split; try assumption. right. rewrite <- BC. split; assumption.
    + (* differing words *)
      apply N.eqb_neq in BC.
      exists k. repeat split; try assumption. left. assumption.
  - destruct PRE as (k & EQ & NF & HK & X3 & X4 & MEM & SP & X30).
    repeat arm8_step.
    + exists k. repeat split; try assumption. apply wcscmp_lt. exact BC.
    + exists k. repeat split; try assumption. eapply wcscmp_ge. exact BC.
Qed.

(* As a signed int the result is -1, 0 or 1 with the sign of the unsigned
   comparison of the first differing (or terminating) wide characters. *)
Theorem wcscmp_result_sign:
  ∀ a b, Z.compare (toZ 32 (ucmp32 a b)) 0%Z = N.compare a b.
Proof. intros. unfold ucmp32. destruct (N.compare a b); reflexivity. Qed.

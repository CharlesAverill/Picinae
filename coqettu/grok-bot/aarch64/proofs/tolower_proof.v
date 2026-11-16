(* tolower -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C

   SEMANTICS
   ---------
   musl's src/ctype/tolower.c:  if (isupper(c)) return c | 32; return c;
   with isupper(c) compiled to the unsigned test (unsigned)c - 'A' < 26:
       sub w2,w0,#0x41; orr w1,w0,#0x20; cmp w2,#0x1a; csel w0,w1,w0,cc
   musl's ctype is ASCII-only (the C/POSIX locale has no other letters).

   SPECIFICATION (man 3 tolower, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <ctype.h>
            int toupper(int c);
            int tolower(int c);

     DESCRIPTION
            These functions convert lowercase letters to uppercase, and vice
            versa.
            If c is a lowercase letter, toupper() returns its uppercase
            equivalent, if an uppercase representation exists in the current
            locale.  Otherwise, it returns c.
            If c is an uppercase letter, tolower() returns its lowercase
            equivalent, if a lowercase representation exists in the current
            locale.  Otherwise, it returns c.
            If c is neither an unsigned char value nor EOF, the behavior of
            these functions is undefined.

     RETURN VALUE
            The value returned is that of the converted letter, or c if the
            conversion was not possible.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            tolower at 0x1f2d0 (ELF vaddr); 0x11f2d0 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/tolower_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   W0 = c (int; the upper half of X0 is ignored); X30 = return address.
   Output:  At the RET (0x11f2e0), with c32 = c mod 2^32:
              X0 = c32 + 32   if 65 <= c32 <= 90  ('A'..'Z')
              X0 = c32        otherwise
            (tolower_spec).  This holds for every 32-bit input, not just
            unsigned char values and EOF.  Memory, SP, X30 and the AAPCS64
            callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import tolower_armv8.
From Grok.lib Require Import GrokCommon.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem tolower_nwc: ∀ s2 s1, tolower_armv8 s1 = tolower_armv8 s2.
Proof. reflexivity. Qed.

Theorem tolower_welltyped: welltyped_prog arm8typctx tolower_armv8.
Proof. Picinae_typecheck. Qed.

Theorem tolower_preserves_memory:
  forall_endstates tolower_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem tolower_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates tolower_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem tolower_preserves_x30:
  forall_endstates tolower_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)

(* C-locale tolower on the low 32 bits of the int argument. *)
Definition tolower_spec (c:N) : N :=
  let c32 := c mod 2^32 in if (65 <=? c32) && (c32 <=? 90) then c32 + 32 else c32.


(* x - lo (mod 2^32) is below len exactly when lo <= x mod 2^32 < lo + len. *)
Lemma msub32_range: ∀ c lo len, 0 < len -> lo + len <= 2^32 ->
  (msub 32 c lo < len <-> lo <= c mod 2^32 < lo + len).
Proof.
  intros c lo len L0 H. rewrite <- (msub_mod_l 32 32) by reflexivity.
  assert (X := N.mod_lt c (2^32) ltac:(discriminate)).
  set (x := c mod 2^32) in *. clearbody x. unfold msub.
  rewrite (N.mod_small lo) by lia.
  destruct (N.le_gt_cases lo x).
  - replace (x + (2^32 - lo)) with ((x - lo) + 1 * 2^32) by lia.
    rewrite N.Div0.mod_add, N.mod_small by lia. lia.
  - rewrite N.mod_small by lia. lia.
Qed.

Lemma or32_range: ∀ x, 65 <= x <= 90 -> x .| 32 = x + 32.
Proof.
  intros x H. assert (E: ∃ n:nat, x = 65 + N.of_nat n /\ (n < 26)%nat) by (exists (N.to_nat (x-65)); lia).
  destruct E as (n & -> & Hn). do 26 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma lor_mod32: ∀ x y, y < 2^32 -> (x .| y) mod 2^32 = (x mod 2^32) .| y.
Proof.
  intros x y Y. apply N.bits_inj. intro b. rewrite N.lor_spec.
  destruct (N.lt_ge_cases b 32).
  - rewrite !N.mod_pow2_bits_low by assumption. apply N.lor_spec.
  - rewrite !N.mod_pow2_bits_high by assumption. rewrite (bound_hibits_zero 32 y b Y H). reflexivity.
Qed.

Section Invariants.
  Variables (sp mem raddr c : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11f2d0 => Inv 0 (s R_X0 = c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11f2e0 => Post 0 (s R_X0 = tolower_spec c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition tolower_exits := make_exits 0 tolower_armv8 invs.
  Definition tolower_invs := make_invs 0 tolower_armv8 invs.
End Invariants.


Theorem tolower_partial_correctness:
  ∀ prog s sp mem raddr c t xs'
    (PROG: tolower_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11f2d0, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c),
  satisfies_all prog (tolower_invs sp mem raddr c) (tolower_exits sp mem raddr c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=tolower_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold tolower_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply tolower_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  repeat arm8_step; (split; [|repeat split; assumption]); unfold tolower_spec.
  - (* not in A..Z *)
    apply N.leb_le in BC. destruct (65 <=? c mod 2^32) eqn:L1, (c mod 2^32 <=? 90) eqn:L2; try reflexivity.
    apply N.leb_le in L1, L2. exfalso. assert (msub 32 c 65 < 26) by (apply msub32_range; cbn; lia). lia.
  - (* in A..Z *)
    apply N.leb_gt in BC. rewrite (msub32_range c 65 26) in BC by (cbn; lia).
    rewrite (proj2 (N.leb_le 65 _)), (proj2 (N.leb_le _ 90)) by lia. cbn [andb].
    rewrite lor_mod32 by reflexivity. apply or32_range. lia.
Qed.

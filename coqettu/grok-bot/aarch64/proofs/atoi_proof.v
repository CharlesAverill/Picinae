(* atoi -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/stdlib/atoi.c is

       int atoi(const char *s)
       {
           int n=0;
           int neg=0;
           while (isspace(s[0])) s++;
           switch (s[0]) {
           case '-': neg=1;
           case '+': s++;
           }
           while (isdigit(s[0]))
               n = 10*n - (s++[0] - '0');
           return neg ? n : -n;
       }

   (written with s[0] for the dereference so this comment stays well formed).
   It accumulates the NEGATED value, so the most negative int can be parsed.
   The compiled code (32-bit arithmetic) skips white space with
   "sub/cmp #0x20/ccmp #4/b.ls", records the sign in W3, accumulates with
   add+lsl (10*n) and sub, and returns with "cmp w3,#0; cneg".
   Ghidra splits the function: the symbol atoi (0x15cfa8) lifts only its first
   two instructions, so ../lifted/atoi_armv8.v is the lift of the Ghidra
   function FUN_0015cfb0, which contains all instructions of atoi.

   SPECIFICATION (man 3 atoi, Linux man-pages 6.9.1)
   -------------------------------------------------
     SYNOPSIS
            #include <stdlib.h>
            int atoi(const char *nptr);
            long atol(const char *nptr);
            long long atoll(const char *nptr);
     DESCRIPTION
            The atoi() function converts the initial portion of the string
            pointed to by nptr to int.  The behavior is the same as
                strtol(nptr, NULL, 10);
            except that atoi() does not detect errors.
            The atol() and atoll() functions behave the same as atoi(), except
            that they convert the initial portion of the string to their return
            type of long or long long.
     RETURN VALUE
            The converted value or 0 on error.
   (musl's isspace/isdigit are the C-locale classes: space and 0x09..0x0d;
   '0'..'9'.  Overflow is undefined behaviour in C; the binary wraps.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            atoi at 0x5cfa8 (ELF vaddr); 0x15cfa8 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, function FUN_0015cfb0 (re-lifted
            from the fresh headless project aarch64/ghidra2, Nov 16 2026);
            see ../lifted/atoi_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s; X30 = return address; m = memory on entry.  No assumption
            is made about the string.
   Output:  If execution reaches the RET (0x15d010), then for some i (white-space
            prefix length) and n (digit count):
              - bytes s[0..i) are white space (ws_run) and s[i] is not;
              - let q = s + i + sgn_len(s[i]) (skip one '+' or '-');
                bytes q[0..n) are decimal digits (dig_run) and q[n] is not;
              - X0 = atox_result 32 m s i n: with
                acc(0) = 0, acc(k+1) = (10*acc(k) - (q[k]-'0')) mod 2^32,
                X0 = acc(n) if s[i] = '-', else (0 - acc(n)) mod 2^32,
                i.e. the decimal value of the digits, signed, modulo 2^32
                (exactly the C source's arithmetic; X0 is zero-extended from W0, the 32-bit int).
            Memory, SP, X30 and the AAPCS64 callee-saved registers are
            unchanged (no stores, no stack use).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import atoi_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCtype GrokAtoi.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem atoi_nwc: ∀ s2 s1, atoi_armv8 s1 = atoi_armv8 s2.
Proof. reflexivity. Qed.

Theorem atoi_welltyped: welltyped_prog arm8typctx atoi_armv8.
Proof. Picinae_typecheck. Qed.

Theorem atoi_preserves_memory:
  forall_endstates atoi_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem atoi_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates atoi_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem atoi_preserves_x30:
  forall_endstates atoi_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants                                                              *)

Section Invariants.
  Variables (sp mem raddr p : N).

  Definition atoi_post (s:store) :=
    ∃ i n, ws_run mem p i /\ is_ws (mem Ⓑ[p + i]) = false /\
      dig_run mem (p + i + sgn_len (mem Ⓑ[p + i])) (N.of_nat n) /\
      is_dig (mem Ⓑ[p + i + sgn_len (mem Ⓑ[p + i]) + N.of_nat n]) = false /\
      s R_X0 = atox_result 32 mem p i n /\
      s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr.

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* entry: b to the white-space loop *)
    | 0x15cfa8 => Inv 0 (s R_X0 = p /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* white-space loop head: ldrb w1,[x0] *)
    | 0x15cfb0 => Inv 0 (∃ i, s R_X0 = p ⊕ i /\ ws_run mem p i /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* digit loop head: ldrb w2,[x0] *)
    | 0x15cff8 => Inv 0 (∃ i n, ws_run mem p i /\ is_ws (mem Ⓑ[p + i]) = false /\
                         s R_X0 = (p + i + sgn_len (mem Ⓑ[p + i])) ⊕ N.of_nat n /\
                         dig_run mem (p + i + sgn_len (mem Ⓑ[p + i])) (N.of_nat n) /\
                         s R_X1 = acc 32 mem (p + i + sgn_len (mem Ⓑ[p + i])) n /\
                         s R_X3 = (if mem Ⓑ[p + i] =? 45 then 1 else 0) /\
                         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    (* ret *)
    | 0x15d010 => Post 0 (atoi_post s)
    | _ => NoInv
    end.

  Definition atoi_exits := make_exits 0 atoi_armv8 invs.
  Definition atoi_invs := make_invs 0 atoi_armv8 invs.
End Invariants.

(* ---------------------------------------------------------------------- *)
(* Partial correctness                                                     *)

Theorem atoi_partial_correctness:
  ∀ prog s sp mem raddr p t xs'
    (PROG: atoi_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15cfa8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = p),
  satisfies_all prog (atoi_invs sp mem raddr p) (atoi_exits sp mem raddr p) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=atoi_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold atoi_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply atoi_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  (* entry -> white-space loop with i = 0 *)
  - destruct PRE as (X0 & MEM & SP & X30). repeat grok_step.
    pose proof (MDL1 R_X0 64 eq_refl) as P64. rewrite X0 in P64.
    exists 0. splits; try assumption. rewrite X0, N.add_0_r, N.mod_small; [reflexivity|exact P64].
    apply ws_run_0.

  (* white-space loop *)
  - destruct PRE as (i & X0 & WS & MEM & SP & X30).
    pose proof (byte_lt8 mem (p+i)) as B8.
    repeat grok_step.
    all: try rewrite ws_bc in * by exact B8.
    (* still white space: advance *)
    1,5: exists (i+1); splits; try reflexivity; try assumption;
         [ f_equal; lia
         | apply ws_run_succ; [exact WS | apply ws_from_bc;
             first [left; exact BC | right; rewrite BC0; discriminate]] ].
    (* '+', '-' or anything else: enter the digit loop with n = 0 *)
    all: exists i, 0%nat; splits; try reflexivity; try assumption;
         try (apply nws_from_bc; assumption); try apply dig_run_0.
    all: unfold sgn_len; rewrite ?BC1, ?BC2.
    all: repeat match goal with H: (_ =? _) = true |- _ => apply N.eqb_eq in H; rewrite H end.
    all: cbn [orb N.eqb Pos.eqb]; rewrite ?N.add_0_r; try reflexivity; try (f_equal; lia).

  (* digit loop *)
  - destruct PRE as (i & n & WS & NW & X0 & DR & X1 & X3 & MEM & SP & X30).
    pose proof (byte_lt8 mem (p + i + sgn_len (mem Ⓑ[p + i]) + N.of_nat n)) as B8.
    repeat grok_step.
    all: rewrite dig_bc in BC by exact B8.
    (* digit: accumulate *)
    3: { assert (D: is_dig (mem Ⓑ[p + i + sgn_len (mem Ⓑ[p + i]) + N.of_nat n]) = true)
           by (destruct is_dig; [reflexivity | discriminate]).
         exists i, (S n). splits; try assumption.
         f_equal; lia.
         replace (N.of_nat (S n)) with (N.of_nat n + 1) by lia. apply dig_run_succ; assumption.
         rewrite acc_step32 by (apply is_dig_bounds; exact D). all: reflexivity. }
    (* end of digits: return *)
    all: exists i, n; splits; try reflexivity; try assumption;
         [ destruct is_dig; [discriminate | reflexivity]
         | unfold atox_result; cbv zeta; rewrite BC0; try reflexivity;
           apply N.mod_small, acc_lt ].
Qed.

(* The white-space prefix and the digit count in the post-condition are
   unique (they are the first non-space / first non-digit positions). *)
Theorem atoi_post_unique_i: ∀ m p i1 i2,
  ws_run m p i1 -> is_ws (m Ⓑ[p + i1]) = false ->
  ws_run m p i2 -> is_ws (m Ⓑ[p + i2]) = false -> i1 = i2.
Proof.
  intros m p i1 i2 R1 N1 R2 N2. destruct (N.lt_trichotomy i1 i2) as [H|[H|H]].
  rewrite (R2 i1 H) in N1; discriminate. exact H. rewrite (R1 i2 H) in N2; discriminate.
Qed.

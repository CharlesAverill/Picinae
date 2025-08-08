(** * Abstractions and Practices *)

(* ################################################################# *)
(** * Introduction *)

(** This chapter surveys proof practices and Picinae-provided abstractions
    that are very useful for completing proofs and specifying readable
    properties.  This chapter can be skimmed once and used as a reference/extended
    documentation.  If you ever find yourself thinking "there's got to be an
    easy/easier way to do this!" or "surely someone else has solved this!" then
    refer to this chapter.  It is likely there is an abstraction, a lemma, or
    a standard practice for what you need.  And if there isn't, email
    the author with your proposed solution.

    Abstractions covered:

      * memory: [getmem], [setmem], [xbits]
      * memory safety: [overlap], [mem_region_unchanged],
      * strings: [nilfree], [strlen], [wnilfree], [wstrlen]

    Practices covered:

      * lia with ZifyN
      * psimpl
      * proofs by contradiction with N.lt_trichotomy and friends
      * equality over N by bitwise inspection 

    (* TODO: add a Picinae themed Search tutorial section and link to this tutorial
       there instead. *)
    Additionally, you'll find it very useful to understand how to use the
    Search command effectively.  The community has a great tutorial for this:
    https://rocq-prover.github.io/platform-docs/features/tutorial_search_for_lemma.html
    *)

(* ################################################################# *)
(** * Setting It Up *)

Require Import NArith.
Require Import Utf8.
Open Scope N.

(* ################################################################# *)
(** * Practices *)

(** We begin this chapter by covering common proving practices, which will
    immediately help with some of the abstraction exercises.

    First, and most importantly is [lia], Rocq's builtin linear integer
    arithmetic solver.  Lia solves arithmetic goals such as equality and
    comparison, and proves arbitrary goals by contradiction by finding
    arithmetic inconsistencies in the hypothesis space.  Here we import [lia]
    simply with [Require Import Lia.], but Picinae imports it through its
    architecture files.  I.e., [Require Import Picinae_pilbox32.] will import
    and configure [Lia] for you. *)

Require Import Lia.

(** Some basic examples of proving easy goals. *)
Goal 32 > 2. lia. Qed.

Goal forall x (LT: x < 2^30), x + 4 < 2^32. lia. Qed.

Goal forall w x y z
  (LTwx: w < x) (LTxy: x < y)
  (LTyz: y < z) (LTzw: z < w), False.
lia. Qed.

(** The lia decision procedure is powerful but has some important limitations.
    It performs propositional reasoning: it is able to destruct conjunctions,
    disjunctions, and reason about implications, negations, and formulaic
    rewrites.  However, it does not handle exponentiation by a variable,
    e.g., 2 ^ w, and does not natively handle some common functions,
    e.g., N.leb and N.mod.

    We can make Lia even more powerful by importing ZifyBool and ZifyNat.  Zify,
    read Z-e-fy, is Lia's preprocessing procedure which turns [N] and [nat]
    values into [Z] integers.  As a Picinae user you won't need to touch it
    directly unless you want to disable Picinae's custom preprocessing with
    [Ltac Zify.zify_pre_hook ::= idtac.] *)

Goal forall x (EQ: N.ltb x 3 = true), x < 3.
intros.
Fail lia. Abort.

Require Import ZifyBool.

Goal forall x (EQ: N.ltb x 3 = true), x < 3.
lia. Qed.

Goal forall x, x mod 2^32 < 2^32.
Fail lia. Abort.

Require Import ZifyN.

Goal forall x, x mod 2^32 < 2^32.
lia. Qed.

(** Lia cannot handle arbitrary moduli, just like it cannot handle
    arbitrary exponentiation. *)
Goal forall x w, x mod w < w.
Fail lia. Abort.

(** But it can figure it out if there is enough information. *)
Goal forall x w (LO: 3 < w) (HI: w < 13), x mod w < w.
lia. Qed.

Require Import Picinae_pilbox32.
Import PIL32Notations.

Goal forall len sublen (SUBLT : sublen < len),
      4 * sublen + 4 <= 4 + 4 * len.
lia. Qed.

Goal forall len sublen i (SUBLT : sublen < len) (LT : i < sublen),
      4 * i + 4 <= 4 + 4 * len.
lia. Qed.

Goal  forall r3 n
        (LE : r3 <= n)
        (BC : n < 1 + r3),
      r3 = n.
lia. Qed.


Goal  forall n r3
        (LE : r3 <= n)
        (BC : n < 1 ⊕ r3)
        (Ge : 2^32 - 1 <= r3),
      False.
lia. Qed.

Goal  forall len sublen i
        (SUBLT : sublen < len)
        (LENLT : len < 2 ^ 30)
        (LT : i < sublen),
      4 + (4 * sublen ⊕ (2 ^ 32 - (4 * i ⊕ 4))) + 4 <= 2 ^ 32.
intros.
lia. Qed.

Goal forall n r2 r3
  (LE : r3 <= n)
  (BC : 1 ⊕ r3 <= n)
  (IH : r2 = (r3 * (1 + r3) / 2) mod 2 ^ 32 ∧ n < 2 ^ 32 - 1 ∨ n = 2 ^ 32 - 1),
1 + r2 ⊕ r3 = ((1 ⊕ r3) * (1 + (1 ⊕ r3)) / 2) mod 2 ^ 32 ∧ n < 4294967295
∨ n = 4294967295.
intros.
lia. Qed.

(** Picinae can extend lia with a preprocessing step allowing it to understand
    Picinae's definitions (e.g., msub) and store abstraction.  At present this
    is a new feature and not incorporated in every architecture.  The file
    Picinae_auto.v defines and configures this automation. To enable it,
    instantiate the module defined therein in the Picinae arch specification
    and export it.  See Picinae_pilbox32.v for an example. *)

Goal forall s x (MDL: models pil32typctx s) (X: s R_R0 = x), x < 2^32.
lia. Qed.

(* ================================================================= *)

(** ** Psimpl *)

(** Psimpl, short for Picinae simplifier, simplifies expressions typically
    appearing in Picinae proofs including types such as N, Bool, and store,
    and functions such as (store) update and getmem/setmem. *)

(* TODO: why are we getting a `frontend verification needing optimization` message
   when using psimpl here? Coq 8.20.0 *)
Goal forall s n, (s[R_R2 := (n * (1 + n) / 2) mod 2 ^ 32][R_R1 := n][R_R3 :=
 1 ⊕ n][R_R0 := (n * (1 + n) / 2) mod 2 ^ 32]) R_R0 =
(n * (n + 1) / 2) mod 2 ^ 32.
intros. psimpl. lia. Qed.

Goal forall s n, (s[R_R2 := (n * (1 + n) / 2) mod 2 ^ 32][R_R1 := n][R_R3 :=
 1 ⊕ n][R_R0 := (n * (1 + n) / 2) mod 2 ^ 32]) R_R1 = n.
intros. psimpl. reflexivity. Qed.


(* ================================================================= *)

(** ** Proofs by contradiction *)

(** Many proofs are better solved by contradiction than by construction, and a
    common way to start these is by case analysis on the comparison of two
    constants.

    [[
   Search N "cases".

    N.le_ge_cases: ∀ n m : N, n <= m ∨ m <= n

    N.lt_ge_cases: ∀ n m : N, n < m ∨ m <= n

    N.le_gt_cases: ∀ n m : N, n <= m ∨ m < n

   ...

   Check N.lt_trichotomy.

    N.lt_trichotomy
        : ∀ n m : N, n < m ∨ n = m ∨ m < n

   Check N.eq_dec.

    N.eq_dec
        : ∀ n m : N, {n = m} + {n ≠ m}
   ]]

    The lemma, e.g., N.lt_ge_cases, is chosen and specialized so that in
    one case the goal is trivial (it is assumed), and in the other case the
    assumption allows the prover to construct a contradiction, i.e., prove [False].
*)

(** **** Exercise:1 star, standard, optional (nflen_lt)

  [nflen_lt] states that a nilfree region in some 64-bit memory [m] with
  a zero byte has a length less than 2^64.  Prove it by contradiction using
  psimpl and lia.  Can you prove this holds for any w-bit memory?

  [nilfree] is Picinae's abstraction for memory regions without zero-bytes,
  it is discussed in more depth below. *)
Lemma nflen_lt:
  forall m p len z
  (NF: nilfree 64 LittleE m p len)
  (Z:  getmem 64 LittleE 1 m z = 0),
  len < 2 ^ 64.
Proof.
Abort.

(* ================================================================= *)

(** ** Equality proofs by bitwise inspection *)

(** Think about it, if two binary numbers have the same digit in every position,
    then they must have the same value.  So you can prove that two integer-valued
    expressions are equal, such as [x mod 2^3] and [N.land x 7], are equal by
    proving that the bits in each position are equal.  The typical proof appeals
    to this fact, [N.bits_inj] or [N.bits_inj_0], and reasons about the value of each
    bit by repeated applications of "spec" bit-specifcation theorems.

    * *)

Example x_mod_8__x_land_7:
  forall x, x mod 2^3 = N.land x 7.
Proof.
  intros.
  apply N.bits_inj.
  (* The goal now asks us to prove the two expressions are functionally equivalent. *)
  unfold N.eqf. intro i.

  (* We reason that the 3rd index ([i]=3) and greater are 0 and indices 0-2 are
     equal to what they are in [x].  Thus we proceed by case analysis on which
     index, splitting into the cases \[0,2\] and \[3,inf). *)
  destruct (N.lt_ge_cases i 3) as [LO | HI].
{
  (* Appeal to the digit being the same as x because the index is less than
     the power of the power-of-2 modulus. *)
  rewrite N.mod_pow2_bits_low; try assumption.
  (* Appeal to the bit-spec of logical and--N.testbit of a digit returns true iff
     it returns true for both sides of the N.land expression. *)
  rewrite N.land_spec.
  (* Replace 7 with 0b111, expressed as [N.ones 3], to capture the significance
     of the number--specifcally, that it is a sequence of 1-bits... *)
  replace 7 with (N.ones 3); try reflexivity.
  (* ... and use this to show the rhs of the logical-and always evaluates
     to true... *)
  rewrite N.ones_spec_low; try assumption.
  (* ... so the expression is equal only to the lhs. *)
  rewrite Bool.andb_true_r.
  reflexivity.
}
{
  (* Appeal to the digit being zero because the index is greater than
     the power of the power-of-2 modulus. *)
  rewrite N.mod_pow2_bits_high; try assumption.
  (* Break apart the logical-and on the rhs of the goal. *)
  rewrite N.land_spec.
  (* Again replace 7 with its [N.ones] representation. *)
  replace 7 with (N.ones 3); try reflexivity.
  (* This time appeal to the index being higher than the number of ones in
     [N.ones], so the testbit evaluates to false. *)
  rewrite N.ones_spec_high; try assumption.
  (* And the boolean-and evaluates to false. *)
  rewrite Bool.andb_false_r.
  reflexivity.
}
Qed.

(** **** Exercise:1 star, standard, optional (land_ones_proof)

    Prove the generalization of the above theorem.  Try not to look at its proof,
    instead use [Search] to find the needed helper lemmas.  You may not use the
    N.land_ones theorem from the standard library. *)

Theorem land_ones:
  forall x w, x mod 2^w = N.land x (N.ones w).
Proof.
Abort.

(** **** Exercise:1 star, standard, optional (Nshiftr_land_ones_high)

   Prove the following using [N.bits_inj_0], the specialization of [N.bits_inj]
   when the right-hand-side is zero. *)
Lemma Nshiftr_land_ones_high:
  forall a n m, m <= n -> (a << n) .& (N.ones m) = 0.
Proof.
Abort.

(** **** Exercise:1 star, standard, optional (Nshiftr_land_high_nop)

    Prove the following using N.bits_inj. *)
Lemma Nshiftr_land_high_nop:
  forall a b n m, n > m -> (a .| b << n) .& (N.ones m) = a .& (N.ones m).
Proof.
Abort.

(** **** Exercise:1 star, standard, optional (xbits_lshift_0)

    Prove the following. *)
Lemma xbits_lshift_0:
  forall n shift i j, i <= j -> j <= shift -> xbits (n << shift) i j = 0.
Proof.
Abort.

(* ################################################################# *)
(** * Abstractions *)

(** ** Memory *)
(** So far we've only considered arithmetic examples dealing exclusively with
    the contents of registers.  When we start reasoning about data structures,
    non-numeric data, and memory we need to introduce abstractions.  At the
    most fundamental level we have Picinae's builtin abstraction for memory-access:
    [getmem] and [setmem].  These abstract the notion of memory as an 8*2^w-bit
    bitstring and allow us to handle byte-aligned big- and little-endian reads
    and writes.

    [[
        Definition getmem w (e:endianness) len mem p : N := _.

        Definition setmem w (e:endianness) len mem p v : memory := _.
    ]]

   Picinae treats memory as a bit-string that wraps around on itself.  A 2kb
   read starting at the last kilobyte of 32-bit memory,
   [getmem 32 _ 2048 mem (2^32-1024)], returns a value comprised of the first
   and last kilobytes of [mem].  A write at an address beyond the w-bit addressable
   memory is mapped to an in-bound address by taking the appropriate remainder modulo bytewidth
   Writing four bytes starting twenty bytes beyond the memory address is the
   equivalent to writing the same four bytes at address 20.  That is,
   [setmem 32 _ 4 (2^32+20) v] is equivalent to [setmem 32 _ 4 20 v].

   Memory writes return the updated memory.  This non-destructive approach
   allows reasoning about memory in several different states, which is
   absolutely necessary when programs interleave reads and writes.
*)

(** **** Exercise:1 star, standard, optional (setmem_4_w20_20)

    Prove the assertion we made above about writing to memory beyond the
    address space.  We start you off with a useful search.  Oh, and feel free
    to import Lia at any time.
 *)
Theorem setmem_4_w20_20:
  forall e mem v, setmem 32 e 4 mem (2^32+20) v = setmem 32 e 4 mem 20 v.
Proof.
  Search setmem -nilfree -"frame" -overlap.
Abort.

(** [getmem] and [setmem] are opaque at the typical user level, meaning you
    cannot unfold or see their definitions.  Working with them requires you to
    use the many getmem and setmem functions available in Picinae_theory.

    [[
      Search getmem in Picinae_theory.
    ]]

    If you need a property of [getmem] or [setmem] that does not exist, you can
    prove it inside of Picinae_theory where you can unfold the definition.  This
    should not be necessary.  For instance, proving a property by recursing over
    the length of the read/write does not require unfolding the definition and
    is facilitated by the [getmem_succ] and [setmem_succ] theorems.  To read
    more about proofs by induction refer to the MemTheory section in
    Picinae_theory.v. *)

(** ** Strings *)

(** Ascii nil-terminated strings are a simple datastructure.  Each byte is
    treated as an ASCII character and the end of the string is marked by
    the null character 0x00 (we use nil and null interchangably).  Technically,
    we can reason about string functions and programs that operate on strings
    without ever considering their semantics.  They are all encoded as bits
    after all.  However developing a library of abstractions is very helpful
    for reading the specifications and writing the proofs.

    The [nilfree] proposition encodes what it means for a string starting at
    [p] to have at least [len] non-nil characters.  Specifically, it states
    that all indices [i] less than [len] into the string starting at [p] are
    non-nil.  Remember that indices start at 0, so there are [len] unique
    indices between 0 and [len-1] inclusive, and thus [len] characters.

    FYI: most unix system will have a man page you can reference for the
    Ascii characters and their encodings as numeric values.  Try running
    [man ascii] in your terminal.
 *)
Module string_defs.

Definition nilfree mem p len :=
  forall w e i, i < len -> getmem w e 1 mem p <> 0.

(** **** Exercise:1 star, standard, required (strlen_def)

   Fill in a definition for the length of a nil-terminated string in memory
   [mem] starting at location [p] using the definition for nilfree. *)

Definition strlen (mem p len:N) : Prop := (* _FILL_IN_HERE_ *) True.

(** **** Exercise:1 star, standard, optional (nilfree_lr_len)

    Prove this lemma saying that there are no null characters before any index
    inside of a string. *)
Lemma nilfree_le_len :
  forall mem p len k
    (LEN : strlen mem p len)
    (LE  : k <= len),
    nilfree mem p k.
Proof.
Abort.

(** **** Exercise:1 star, standard, optional (strlen_incr)

    Prove this strlen lemma used in reasoning about the length of a string as
    we discover new information about its characters.  It states that if we know
    a character, possibly the nil-terminator, is not the nil-terminator then the
    length of the string is greater than the index of this character. *)
Lemma strlen_incr :
  forall mem p len k
    (LEN : strlen mem p len)
    (LE : k <= len)
    (NNULL : mem Ⓑ[ p + k ] <> 0),
     k < len.
Proof.
Abort.

(** **** Exercise:2 stars, standard, optional (wnilfree_sublen_eq_len)

    Prove this lemma used in the wcscpy proof below without peeking at
    Picinae_theory.  It states that the length, [sublen], of a nil-free substring
    is the length of the entire string if there is a nil terminator at its
    corresponding index. *)
Lemma wnilfree_sublen_eq_len:
  forall w e mem p len sublen
    (NF: wnilfree w e mem p sublen)
    (LEN: wstrlen w e mem p len)
    (BC: getmem w e 4 mem (p+4*sublen) = 0),
  sublen = len.
Proof.
Abort.

End string_defs.

(** ** Memory Safety *)

(** Once we start reasoning about programs that modify code, e.g., the [wcscpy]
    exercise in BasicLoops, it becomes necessary to reason about the memory safety
    of programs.  In other words, we need a way to say that values read from two
    different memories are the same, that the expected value was not overwritten
    during an execution, or that it was correctly copied by a write or sequence
    of writes.

    The [overlap] and [mem_region_unchanged] abstractions are used for this purpose.
    [Overlap] defines what it means for two memory regions specified by their initial
    addresses and their lengths to overlap in a w-bit system, useful e.g., to define
    that a destination buffer does not overlap with the source buffer.
    [Mem_region_unchanged] is a shorthand for stating that the bytes in a specification
    region of two different memories are the same, useful e.g., when we want to
    describe a data structure as static.

    In particular, the [getmem_noverlap] and [getmem_index_unchanged] theorems help
    by rewriting memory accesses from modified memories to memory accesses from
    unmodified memory, providing some non-overlapping conditions hold.  Often times
    [getmem_noverla] is followed by a [noverlap_sum; lia] invocation to prove the
    [~ overlap] condition.  When lia is not strong enough for this the intensive overlap
    theory library is well equipped for reasoning about overlaps and non-overlaps at
    a high level.

    [[
      Search overlap.
    ]] *)

(** **** Exercise:1 star, standard, optional (getmem_setmem_eq)

   Prove the following lemma featuring [overlap]. *)

Lemma getmem_setmem_eq:
  forall mem e (a wraddr wrlen v min max : N)
    (HEAD : min <= a <= max)
    (NOV : ~ overlap 32 wraddr wrlen min (max + 8 - min)),
  mem Ⓓ[ 4 + a ] = setmem 32 e wrlen mem wraddr v Ⓓ[ 4 + a ].
Proof.
  (* FILL IN HERE *)
Abort.

(** **** Exercise:1 star, standard, optional (wstrlen_same)

   Prove the following lemma featuring [overlap]. *)

Lemma wstreln_same:
  forall psrc pdest len mem sublen
    (LEN : wstrlen 32 LittleE mem psrc len)
    (NOV : ¬ overlap 32 psrc (4 + 4 * len) pdest (4 + 4 * len))
    (SUBLT : sublen < len),
  wstrlen 32 LittleE
    (mem [Ⓓ pdest + 4 * sublen := mem Ⓓ[ psrc + 4 * sublen ] ]) psrc len.
Proof.
  (* FILL IN HERE *)
Abort.

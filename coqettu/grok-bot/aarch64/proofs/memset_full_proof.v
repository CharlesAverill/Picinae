(* memset (full: small and large paths) -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64,
   hand-written assembly (src/string/aarch64/memset.S)

   SEMANTICS
   ---------
   void *memset(void *dest, int c, size_t n): fills n bytes at dest with
   the byte c mod 256 and returns dest.  dup v0.16b, w1 splats the byte into
   q0.  n <= 96: overlapping stores from both ends (see memset_proof.v).
   n > 96 (0x18480): str q0,[dest]; x3 = (dest & ~15) - 16; if n >= 160 and
   c mod 256 = 0 the DC ZVA path (mrs dczid_el0, dc zva) is taken, otherwise
   the loop at 0x184e8 stores 64 bytes per iteration (stp q0,q0,[x3,#32];
   stp q0,q0,[x3,#64]!) while x2 = dest+n-x3-96 > 64, then stores the last
   64 bytes from the end (stp q0,q0,[x4,#-64]; stp q0,q0,[x4,#-32]).

   SPECIFICATION (man 3 memset, Linux man-pages 6.9.1)
   ----------------------------------------------------
     The memset() function fills the first n bytes of the memory area
     pointed to by s with the constant byte c.  memset() returns a
     pointer to the memory area s.

   RESTRICTION AND WHY IT IS SOUND
   -------------------------------
   Preconditions: mf_side c n := n <= 96 \/ c mod 256 <> 0 \/ n < 160,
   4096 <= dest, dest + n < 2^64.
   - mf_side excludes exactly the c mod 256 = 0 /\ n >= 160 inputs.  Those
     reach 0x18498 (mrs x5, dczid_el0) and the dc zva loop, which the lifter
     models as Nop (unmodelled system register / CALLOTHER), so no sound
     statement about them is possible from this lift.  The theorem proves the
     invariant at 0x118498 is False under mf_side, so no Nop-lifted
     instruction is executed.  This lifts the old n <= 96 limit for every
     nonzero fill byte and for zero fills of fewer than 160 bytes.
   - 4096 <= dest and dest + n < 2^64: as in memset_proof.v (page 0 is never
     mapped; an object cannot end at the top of the address space).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            memset at 0x18400 (ELF vaddr); 0x118400 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/memset_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest = d, X1 = c, X2 = n; X30 = return address raddr;
            SP = sp; mem = memory on entry; precondition mf_side c n,
            4096 <= d, d + n < 2^64.
   Output:  If execution reaches any of the RETs (0x118428, 0x11843c,
            0x118450, 0x11846c, 0x11847c, 0x118500; 0x1184d8 is unreachable):
            X0 = d, SP = sp, X30 = raddr, every byte d+i for i < n equals
            c mod 2^8, and every byte outside [d, d+n) is unchanged (memset_post,
            the same postcondition as memset_partial_correctness).  The callee-saved
            registers are unchanged by memset_proof.memset_preserves_callee_saved
            (same program memset_armv8).  Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
From Grok.proofs Require Import memset_proof memset_full_defs.
Import ARM8Notations.
Open Scope N.

Lemma land_m16: ∀ d, d < 2^64 -> N.land d 18446744073709551600 = d - d mod 16.
Proof.
  intros d D.
  replace (d - d mod 16) with (N.shiftl (N.shiftr d 4) 4).
  - rewrite <- N.ldiff_ones_r. apply N.bits_inj. intro k.
    rewrite N.land_spec, N.ldiff_spec.
    replace 18446744073709551600 with (N.ldiff (N.ones 64) (N.ones 4)) by reflexivity.
    rewrite N.ldiff_spec.
    destruct (N.lt_ge_cases k 64) as [K|K].
    + rewrite (N.ones_spec_low 64 k K). destruct (N.testbit d k), (N.testbit (N.ones 4) k); reflexivity.
    + rewrite (N.ones_spec_high 64 k) by lia.
      replace (N.testbit d k) with false; [reflexivity|].
      symmetry. apply (N.bits_above_log2 d k). destruct (N.eq_dec d 0) as [->|NZ]; [simpl; lia|].
      apply N.log2_lt_pow2; [lia | apply N.lt_le_trans with (2^64); [exact D | apply N.pow_le_mono_r; lia]].
  - rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. pose proof (N.div_mod d 16 ltac:(discriminate)).
    change (2^4) with 16. lia.
Qed.

Lemma rng_dec: ∀ a b len, (b <= a /\ a < b + len) \/ (a < b \/ b + len <= a).
Proof. intros. lia. Qed.

(* single-byte read through a store, one in-branch and one out-branch *)
Ltac rd2 :=
  match goal with |- context [getmem 64 LittleE 1 (setmem 64 LittleE ?len ?m ?b ?v) ?a] =>
    let H := fresh "RG" in destruct (rng_dec a b len) as [H|H];
    [ rewrite (read_in len m b v a) by (change (2^64) with 18446744073709551616 in *; lia)
    | rewrite (read_out len m b v a) by (change (2^64) with 18446744073709551616 in *; lia) ]
  end.

Ltac mf_byte := match goal with ZS: splat_bytes _ _ _ |- _ => memset_byte ZS end.
Ltac mf_ih := match goal with H: ∀ i:N, _ <= i -> i < _ -> _ = _ |- _ => apply H; lia end.
Ltac mf_out := match goal with H: ∀ a:N, a < _ -> _ \/ _ -> _ = _ |- _ => apply H; lia end.

Theorem memset_full_partial_correctness:
  ∀ prog s mem d c n sp raddr t xs'
    (PROG: memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118400, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = d) (X1: s R_X1 = c) (X2: s R_X2 = n) (MEM: s V_MEM64 = mem) (SP: s R_SP = sp) (X30: s R_X30 = raddr)
    (SIDE: mf_side c n) (LOW: 4096 <= d) (NW: d + n < 2^64),
  satisfies_all prog (mf_invs0 mem d c n sp raddr) (mf_exits mem d c n sp raddr) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memset_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold mf_invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL X0 X1 X2 MEM SP X30 SIDE LOW NW START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold mfb, fbase, mf_loop in *; repeat match goal with H: _ /\ _ |- _ => destruct H end.
  all: try match goal with H: False |- _ => destruct H end.
  1: (arm8_step; splits; try reflexivity; try assumption; match goal with |- context[?s R_Z0] => solve_splat c (s R_Z0) end).
  (* 0x118404 *)
  (* old small-path cases 0x118404 .. 0x118470 *)
  2-6: (repeat grok_step; memset_prep;
    try (unfold memset_post); unfold mfb, fbase; splits; try reflexivity; try assumption; try lia;
    try (intros i I; memset_addr; repeat rd1; first [match goal with ZS: splat_bytes _ _ _ |- _ => memset_byte ZS end | lia | reflexivity]);
    try (intros x A O; memset_addr; repeat rd1; first [reflexivity | lia]);
    try (intros; match goal with H: _ V_MEM64 = _ |- _ => rewrite H end; reflexivity)).
  (* 0x118404 *)
  1: (repeat grok_step; memset_prep; unfold mfb, fbase; splits; try reflexivity; try assumption; memset_addr; try lia).
  (* 0x118480 *)
  1: { repeat grok_step. all: memset_prep.
       all: try (exfalso; unfold mf_side in *; lia).
       all: rewrite !land_m16 by lia.
       all: assert (DM: d mod 16 < 16) by (apply N.mod_lt; discriminate).
       all: assert (DL: d mod 16 <= d) by (apply N.Div0.mod_le).
       all: unfold fbase; splits; try reflexivity; try assumption; memset_addr; try lia.
       all: first
         [ intros i I1 I2; rd1; [ mf_byte | exfalso; lia | exfalso; lia ]
         | intros x A O; rd1; [ exfalso; lia | reflexivity | reflexivity ] ]. }
  (* 0x1184e8 *)
  1: { repeat grok_step. all: memset_prep.
       all: repeat match goal with H: MemAcc _ _ _ _ _ |- _ => clear H end.
       all: unfold fbase; splits; try reflexivity; try assumption; memset_addr; try lia.
       all: match goal with
         | |- ∀ i, i < _ -> _ => intros i I; repeat rd2; first [ mf_byte | mf_ih ]
         | |- ∀ i, _ <= i -> _ => intros i I1 I2; repeat rd2; first [ mf_byte | mf_ih ]
         | |- ∀ a, a < _ -> _ => intros x A O; repeat rd2; first [ exfalso; lia | mf_out ]
         end. }
Qed.

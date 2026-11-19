(* mempcpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C
   (src/string/mempcpy.c), restricted to n <= 128

   SEMANTICS
   ---------
   void *mempcpy(void *dest, const void *src, size_t n): copies n bytes from
   src to dest like memcpy and returns dest + n.  musl: returns memcpy(dest, src, n)
   plus n (as a char pointer).  The code saves x29/x30 at sp-32,
   sp-24 and n at sp-8, calls memcpy (bl 0x118270), reloads n, restores
   x29/x30 and returns x0 + n.

   SPECIFICATION (man 3 mempcpy, Linux man-pages 6.9.1)
   -----------------------------------------------------
     The mempcpy() function is nearly identical to the memcpy(3) function.
     It copies n bytes from the object beginning at src into the object
     pointed to by dest.  But instead of returning the value of dest it
     returns a pointer to the byte following the last written byte.

   RESTRICTION AND WHY IT IS SOUND
   -------------------------------
   Preconditions: n <= 128, dest + n < 2^64, src + n < 2^64, 32 <= sp,
   and [dest, dest+n) does not overlap mempcpy's 32-byte frame
   [sp-32, sp) (true for any object the caller owns, since the frame is
   below the caller's stack pointer).
   - n <= 128: memcpy is verified here on its small-size paths
     (memcpy_proof.v); the large path has its own theorem
     (memcpy_large_proof.v) but is not yet wired into this caller.
   The copy is relative to the memory at the call (mp_fm: entry memory plus
   the three frame slots), so a src overlapping the frame reads the saved
   values, exactly as the machine does.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            mempcpy at 0x5e81c (ELF vaddr); 0x15e81c in Ghidra (image base 0x100000);
            callee memcpy at 0x18270 / 0x118270
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/mempcpy_armv8.v and
            ../lifted/memcpy_armv8.v (combined as mp_prog with updateall2).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest = d, X1 = src, X2 = n, X29 = x29, X30 = raddr, SP = sp,
            mem = memory on entry (mp_pre).
   Output:  At the RET 0x15e838: X0 = d + n, SP = sp, X30 = raddr, X29 = x29,
            byte d+i = mp_fm byte src+i for i < n, and every byte outside
            [d, d+n) equals mp_fm (mp_post).  X19..X28 and Z8..Z15 are
            unchanged (mempcpy_preserves_other_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require mempcpy_armv8 memcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCopy GrokCov.
From Grok.proofs Require Import memcpy_defs memcpy_mem memcpy_proof.
From Grok.proofs Require Import mempcpy_defs mempcpy_callee.
Import ARM8Notations.
Open Scope N.

Lemma copied_out_read: ∀ FM M src d n a len, copied FM M src d n ->
  (a + len <= d \/ d + n <= a) -> a + len <= 2^64 ->
  getmem 64 LittleE len M a = getmem 64 LittleE len FM a.
Proof.
  intros FM M src d n a len [_ H] O B. apply getmem_ext. intros i I. apply H; lia.
Qed.

Theorem mempcpy_partial_correctness:
  ∀ prog s sp mem raddr d src n x29 t xs'
    (P1: mempcpy_armv8.mempcpy_armv8 ⊆2 prog) (P0: memcpy_armv8.memcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e81c, s))
    (MDL: models arm8typctx s) (HPRE: mp_pre sp mem raddr d src n x29 s),
  satisfies_all prog (mp_invs1 sp mem raddr d src n x29) (mp_exits1 sp mem raddr d src n x29) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=mp_prog).
    unfold mp_prog. rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
    intros a s1 t1 EXIT NOCODE. unfold mp_invs1, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL HPRE START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. exact HPRE.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply mp_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & X29 & SMALL & ND & NS & SPL & SPH & FR).
  pose proof (MDL1 R_X30 64 eq_refl) as R64. rewrite X30 in R64. simpl in R64.
  pose proof (MDL1 R_X29 64 eq_refl) as X2964. rewrite X29 in X2964. simpl in X2964.
  pose proof (MDL1 R_X2 64 eq_refl) as N64. rewrite X2 in N64. simpl in N64.
  do 4 arm8_step.
  match goal with |- nextinv _ _ _ _ ((_, ?st) :: _) => set (s2 := st) end.
  eapply models_after_steps. eassumption. apply mp_prog_welltyped. intro MDL2.
  eapply (perform_call 0). reflexivity.
  intros. eapply memcpy_correct_in_mempcpy.
  1: exact mp_prog_contains. 1: apply subset_updateall2. 1: exact ENTRY. 1: exact MDL2.
  2: reflexivity.
  1: (unfold memcpy_pre, s2; upd_simpl; splits; try reflexivity; try assumption).
  intros.
  assert (MDL': models arm8typctx s').
    eapply preservation_exec_prog; try eassumption. apply mp_prog_welltyped.
  set (t' := t2++t0++_::t) in *. clearbody s2 t'.
  clear - PRE MDL' R64 X2964 N64 SMALL ND NS SPL SPH FR.
  rename MDL' into MDL. rename t' into t. rename s' into s.
  destruct_inv 64 PRE.
  all: unfold memcpy_post in PRE; destruct PRE as (RX0 & RSP & RX30 & CP).
  all: repeat arm8_step.
  all: rewrite !msub64_small' by (change (2^64) with 18446744073709551616 in *; lia).
  all: unfold mp_post; splits; [ | reflexivity | | | exact CP ].
  all: rewrite (copied_out_read _ _ _ _ _ _ _ CP) by (change (2^64) with 18446744073709551616 in *; lia).
  all: unfold mp_fm; rewrite !msub64_small' by (change (2^64) with 18446744073709551616 in *; lia).
  all: repeat first [ rewrite getmem_setmem by (change (2^64) with 18446744073709551616 in *; lia)
                    | rewrite getmem_setmem_above by (change (2^64) with 18446744073709551616 in *; lia) ].
  all: first [ rewrite (N.mod_small n (2^(8*8))) by exact N64; apply N.mod_small; exact ND
              | apply N.mod_small; exact R64
              | apply N.mod_small; exact X2964 ].
Qed.

Theorem mempcpy_preserves_other_callee_saved:
  ∀ r, In r (R_X19 :: R_X20 :: R_X21 :: R_X22 :: R_X23 :: R_X24 :: R_X25 :: R_X26 :: R_X27 :: R_X28 ::
             R_Z8 :: R_Z9 :: R_Z10 :: R_Z11 :: R_Z12 :: R_Z13 :: R_Z14 :: R_Z15 :: nil) ->
  forall_endstates mp_prog (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

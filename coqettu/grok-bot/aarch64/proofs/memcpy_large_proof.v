(* memcpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, hand-written assembly
   (src/string/aarch64/memcpy.S, Arm optimized-routines style), large sizes n > 128

   SEMANTICS
   ---------
   void *memcpy(void *restrict dest, const void *restrict src, size_t n):
   copies n bytes from src to dest and returns dest.  The aarch64 code
   computes srcend = src + n, dstend = dest + n and, for n <= 128, uses
   straight-line code that issues every load before any store:
   n = 0: nothing; 1..3: bytes at 0, n/2, n-1 (lsr); 4..7: words at 0 and
   n-4; 8..15: dwords at 0 and n-8 (tbz on bits 3 and 2 of n); 16..32:
   ldp/stp pairs at 0 and n-16; 33..64: pairs at 0, 16, n-32, n-16;
   65..96: pairs at 0..48 and n-32, n-16; 97..128: additionally n-64, n-48.
   n > 128 branches to an aligned 64-byte ldp/stp loop at 0x118370.

   SPECIFICATION (man 3 memcpy, Linux man-pages 6.9.1)
   ----------------------------------------------------
     The memcpy() function copies n bytes from memory area src to memory
     area dest.  The memory areas must not overlap.  Use memmove(3) if the
     memory areas do overlap.  The memcpy() function returns a pointer to
     dest.

   RESTRICTION AND WHY IT IS SOUND
   -------------------------------
   This theorem covers n > 128 (memcpy_proof.v covers n <= 128).
   Preconditions: 128 < n, dest + n < 2^64, src + n < 2^64, and the buffers
   do not overlap (src + n <= dest or dest + n <= src) -- exactly the
   memcpy contract ("The memory areas must not overlap").  Disjointness is
   needed: the loop interleaves loads and stores.
   - dest + n < 2^64, src + n < 2^64: an object cannot end at the very top
     of the address space (the upper half is kernel space on aarch64 Linux).
   Loop: the first 16 bytes are stored at dest, then x3 = dest & ~15 and the
   64-byte loop at 0x1183a0 stores 16-byte-aligned blocks; invariant: the
   first L bytes are copied, x6..x13 hold the next 64 source bytes,
   x1 = src+L+48, x2 = n-L-128.  The tail 0x1183c8 stores the last 64 bytes
   of the current block and the final 64 bytes (dstend-64 .. dstend).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            memcpy at 0x18270 (ELF vaddr); 0x118270 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/memcpy_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = dest = d, X1 = src, X2 = n; X30 = return address raddr;
            SP = sp; mem = memory on entry (mcl_pre).
   Output:  If execution reaches the RET at 0x1183f8 (the small-size RETs
            are unreachable for n > 128): X0 = d, SP = sp, X30 = raddr,
            byte d+i equals the entry byte mem[src+i] for every i < n, and
            every byte outside [d, d+n) is unchanged (memcpy_post / copied).
            The AAPCS64 callee-saved registers are unchanged
            (memcpy_preserves_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill GrokMem GrokCopy GrokCov.
From Grok.proofs Require Import memcpy_defs memcpy_mem memcpy_proof.
From Grok.proofs Require Import memcpy_large_defs memcpy_large_chain.
Import ARM8Notations.
Open Scope N.
Ltac bools_to_props_ml := repeat match goal with
 | H: (?a =? ?b) = true |- _ => apply N.eqb_eq in H
 | H: (?a =? ?b) = false |- _ => apply N.eqb_neq in H
 | H: (?a <=? ?b) = true |- _ => apply N.leb_le in H
 | H: (?a <=? ?b) = false |- _ => apply N.leb_gt in H
 | H: (?a <? ?b) = true |- _ => apply N.ltb_lt in H
 | H: (?a <? ?b) = false |- _ => apply N.ltb_ge in H
 | H: context[if ?c then _ else _] |- _ =>
     match type of H with _ V_MEM64 = _ => fail 1 | _ => destruct c eqn:? end
 end.
Theorem memcpy_large_partial_correctness:
  ∀ prog s mem d src n sp raddr t xs'
    (PROG: memcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118270, s))
    (MDL: models arm8typctx s) (HPRE: mcl_pre mem d src n sp raddr s),
  satisfies_all prog (mcl_invs mem d src n sp raddr) (mcl_exits mem d src n sp raddr) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memcpy_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold mcl_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL HPRE START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. exact HPRE.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold mcl_pre, mcl_regs in *; repeat match goal with H: _ /\ _ |- _ => destruct H | H: ∃ _, _ |- _ => destruct H end.
  all: (repeat grok_step).
  all: try match goal with H: models _ _ |- _ => clear H end.
  all: repeat match goal with H: MemAcc _ _ _ _ _ |- _ => clear H end.
  all: bools_to_props_ml; rewrite ?N.shiftr_div_pow2 in *.
  all: try (exfalso; lia).
  all: try lor_absurd.
  all: match goal with H: _ + _ <= _ \/ _ + _ <= _ |- _ => destruct H as [DJ|DJ] end.
  all: pose proof (N.mod_lt d 16 ltac:(discriminate)); pose proof (N.Div0.mod_le d 16).
  all: try match goal with C: cov _ _ _ _ _ (fun i => i < ?L) |- ∃ _, _ => exists (L + 64) end.
  all: try match goal with |- ∃ _, _ => exists (16 - d mod 16) end.
  all: unfold mcl_regs, memcpy_post; splits.
  all: (upd_simpl).
  all: rewrite ?land15; rewrite ?land_m16' by (change (2^64) with 18446744073709551616 in *; lia).
  all: (pow_lits; pow_lits_g; addr_norm; num_norm).
  all: (try lia).
  all: (try sassumption).
  all: try (match goal with C: cov _ _ _ _ _ _ |- _ => src_read C end; src_read0;
            apply (f_equal (getmem 64 LittleE 8 mem)); lia).
  all: try (src_read0; apply (f_equal (getmem 64 LittleE 8 mem)); lia).
  all: try ((try match goal with C: cov _ _ _ _ _ _ |- _ => src_read C end); src_read0; cov_close).
Qed.

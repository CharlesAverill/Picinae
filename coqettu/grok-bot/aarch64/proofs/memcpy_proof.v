(* memcpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, hand-written assembly
   (src/string/aarch64/memcpy.S, Arm optimized-routines style), restricted to n <= 128

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
   Preconditions: n <= 128, dest + n < 2^64, src + n < 2^64.
   - n <= 128: the theorem covers only the small-size code; the invariant
     at the large-size loop entry 0x118370 is False and is proved
     unreachable under the precondition.
   - dest + n < 2^64, src + n < 2^64: an object cannot end at the very top
     of the address space (the upper half is kernel space on aarch64 Linux).
   No disjointness is assumed: on these paths all loads precede all stores,
   so the result is the copy of the ORIGINAL src bytes even when the areas
   overlap (i.e. for n <= 128 this code also meets the memmove contract).

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
            SP = sp; mem = memory on entry (memcpy_pre).
   Output:  If execution reaches any RET (0x1182a0, 0x1182b8, 0x1182d4,
            0x1182f8, 0x118328, 0x118368): X0 = d, SP = sp, X30 = raddr,
            byte d+i equals the entry byte mem[src+i] for every i < n, and
            every byte outside [d, d+n) is unchanged (memcpy_post / copied).
            The AAPCS64 callee-saved registers are unchanged
            (memcpy_preserves_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill GrokCopy.
From Grok.proofs Require Import memcpy_defs memcpy_mem.
Import ARM8Notations.
Open Scope N.

Theorem memcpy_welltyped: welltyped_prog arm8typctx memcpy_armv8.
Proof. Picinae_typecheck. Qed.

Theorem memcpy_nwc: ∀ s2 s1, memcpy_armv8 s1 = memcpy_armv8 s2.
Proof. reflexivity. Qed.

Theorem memcpy_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates memcpy_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem memcpy_preserves_x30:
  forall_endstates memcpy_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Ltac bools_to_props_mc := repeat match goal with
 | H: (?a =? ?b) = true |- _ => apply N.eqb_eq in H
 | H: (?a =? ?b) = false |- _ => apply N.eqb_neq in H
 | H: (?a <=? ?b) = true |- _ => apply N.leb_le in H
 | H: (?a <=? ?b) = false |- _ => apply N.leb_gt in H
 | H: (?a <? ?b) = true |- _ => apply N.ltb_lt in H
 | H: (?a <? ?b) = false |- _ => apply N.ltb_ge in H
 | H: context[if ?c then _ else _] |- _ =>
     match type of H with _ V_MEM64 = _ => fail 1 | _ => destruct c eqn:? end
 end.
Theorem memcpy_partial_correctness:
  ∀ prog s mem d src n sp raddr t xs'
    (PROG: memcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118270, s))
    (MDL: models arm8typctx s) (HPRE: memcpy_pre mem d src n sp raddr s),
  satisfies_all prog (memcpy_invs mem d src n sp raddr) (memcpy_exits mem d src n sp raddr) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memcpy_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold memcpy_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL HPRE START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. exact HPRE.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold memcpy_pre in *; repeat match goal with H: _ /\ _ |- _ => destruct H end.
  all: try match goal with H: False |- _ => destruct H end.
  all: repeat grok_step.
  all: try match goal with H: models _ _ |- _ => clear H end.
  all: bools_to_props_mc; rewrite ?N.shiftr_div_pow2 in *.
  all: try (exfalso; lia).
  all: try (match goal with H: ?st V_MEM64 = _ |- context [?st V_MEM64] => rewrite H end).
  all: unfold memcpy_post; splits; try reflexivity; try assumption.
  all: try (exfalso; match goal with H: N.lor _ _ = _ |- _ => vm_compute in H; discriminate H end).
  all: apply_cp; pow_lits; lia.
Qed.

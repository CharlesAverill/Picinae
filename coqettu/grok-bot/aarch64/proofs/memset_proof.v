(* memset -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, hand-written assembly
   (src/string/aarch64/memset.S), restricted to n <= 96

   SEMANTICS
   ---------
   void *memset(void *dest, int c, size_t n): fills n bytes at dest with
   the byte c mod 256 and returns dest.  The aarch64 code splats the byte
   into q0 with dup v0.16b, w1, then for n <= 96 uses overlapping stores:
   n < 16: 8/4/2/1-byte stores of the splat from both ends (tbz on bits
   3, 2, 1 of n); 16 <= n <= 96: q0 stores at dest, dest+16, dest+32..63
   and the last 16/32 bytes, chosen by bits 6 and 5 of n.

   SPECIFICATION (man 3 memset, Linux man-pages 6.9.1)
   ----------------------------------------------------
     The memset() function fills the first n bytes of the memory area
     pointed to by s with the constant byte c.  memset() returns a
     pointer to the memory area s.

   RESTRICTION AND WHY IT IS SOUND
   -------------------------------
   Preconditions: n <= 96, 4096 <= dest, dest + n < 2^64.
   - n <= 96: the lifter models mrs x5, dczid_el0 and dc zva as Nop
     (unmodelled system register / CALLOTHER).  Both occur only after the
     cmp x2, #0x60 / b.hi at 0x18408 (Ghidra 0x118408) has branched to
     0x18480 for n > 96.  Under n <= 96 that branch is never taken (the
     theorem proves the 0x118480 invariant is False there), so no Nop-lifted
     instruction is executed and the theorem says nothing about them.
   - 4096 <= dest: Linux never maps page 0 (vm.mmap_min_addr >= 4096), so
     no valid object starts there; this lets dest+n-k be computed without
     64-bit wraparound.
   - dest + n < 2^64: an object cannot end at the very top of the address
     space (on aarch64 Linux the upper half is kernel space).

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
            SP = sp; mem = memory on entry.
   Output:  If execution reaches any of the RETs (0x118428, 0x11843c,
            0x118450, 0x11846c, 0x11847c): X0 = d, SP = sp, X30 = raddr,
            every byte d+i for i < n equals c mod 2^8, and every byte
            outside [d, d+n) is unchanged (memset_post).  The AAPCS64
            callee-saved registers are unchanged (memset_preserves_callee_saved).
 *)

From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
Import ARM8Notations.
Open Scope N.

Theorem memset_welltyped: welltyped_prog arm8typctx memset_armv8.
Proof. Picinae_typecheck. Qed.

Theorem memset_nwc: ∀ s2 s1, memset_armv8 s1 = memset_armv8 s2.
Proof. reflexivity. Qed.

Theorem memset_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates memset_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem memset_preserves_x30:
  forall_endstates memset_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition memset_post (mem d c n sp raddr : N) (s:store) :=
  s R_X0 = d /\ s R_SP = sp /\ s R_X30 = raddr /\
  (∀ i, i < n -> s V_MEM64 Ⓑ[d + i] = c mod 2^8) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]).


Lemma msub64_small: ∀ x k, k <= x -> x < 2^64 -> msub 64 x k = x - k.
Proof.
  intros x k H1 H2. unfold msub. rewrite (N.mod_small k) by lia.
  replace (x + (2^64 - k)) with ((x - k) + 1 * 2^64) by lia.
  rewrite N.mod_add by discriminate. apply N.mod_small. lia.
Qed.

Ltac bools_to_props := repeat match goal with
 | H: (?a =? ?b) = true |- _ => apply N.eqb_eq in H
 | H: (?a =? ?b) = false |- _ => apply N.eqb_neq in H
 | H: (?a <=? ?b) = true |- _ => apply N.leb_le in H
 | H: (?a <=? ?b) = false |- _ => apply N.leb_gt in H
 | H: (?a <? ?b) = true |- _ => apply N.ltb_lt in H
 | H: (?a <? ?b) = false |- _ => apply N.ltb_ge in H end.

Ltac memset_prep :=
  try match goal with H: models _ _ |- _ => clear H end;
  repeat match goal with H: context[if ?c then _ else _] |- _ =>
    match type of H with _ V_MEM64 = _ => fail 1 | _ => destruct c eqn:? end end;
  try solve [match goal with H: _ = _ |- _ => discriminate H end];
  bools_to_props;
  rewrite ?N.shiftr_div_pow2 in *.

Ltac memset_addr :=
  change (2^64) with 18446744073709551616 in *;
  repeat match goal with |- context[msub 64 ?x ?k] => rewrite (msub64_small x k) by lia end;
  repeat match goal with |- context[(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x + y)) by lia end.

Ltac memset_byte ZS :=
  repeat rewrite byte_mod by lia; apply ZS; lia.

Section Invariants.
  Variables (mem d c n sp raddr : N).
  Definition mbase (s:store) := s R_X0 = d /\ s R_X2 = n /\ s R_SP = sp /\ s R_X30 = raddr /\
                         n <= 96 /\ 4096 <= d /\ d + n < 2^64 /\ splat_bytes (s R_Z0) c 16.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x118400 => Inv 0 (s R_X0 = d /\ s R_X1 = c /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         n <= 96 /\ 4096 <= d /\ d + n < 2^64)
    | 0x118404 => Inv 0 (s R_X0 = d /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         n <= 96 /\ 4096 <= d /\ d + n < 2^64 /\ splat_bytes (s R_Z0) c 16)
    | 0x118418 => Inv 0 (mbase s /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ n < 16)
    | 0x118430 => Inv 0 (mbase s /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ n < 8 /\ s R_X1 = s R_Z0 mod 2^64)
    | 0x118440 => Inv 0 (mbase s /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ n < 4 /\ s R_X1 = s R_Z0 mod 2^64)
    | 0x118454 => Inv 0 (mbase s /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ 16 <= n)
    | 0x118470 => Inv 0 (mbase s /\ s R_X4 = d + n /\ s V_MEM64 = setmem 64 LittleE 16 mem d (s R_Z0) /\ 64 <= n)
    | 0x118480 => Inv 0 False
    | 0x118428 | 0x11843c | 0x118450 | 0x11846c | 0x11847c => Post 0 (memset_post mem d c n sp raddr s)
    | _ => NoInv
    end.
  Definition memset_exits := make_exits 0 memset_armv8 invs.
  Definition memset_invs := make_invs 0 memset_armv8 invs.
End Invariants.

Theorem memset_partial_correctness:
  ∀ prog s mem d c n sp raddr t xs'
    (PROG: memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118400, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = d) (X1: s R_X1 = c) (X2: s R_X2 = n) (MEM: s V_MEM64 = mem) (SP: s R_SP = sp) (X30: s R_X30 = raddr)
    (SMALL: n <= 96) (LOW: 4096 <= d) (NW: d + n < 2^64),
  satisfies_all prog (memset_invs mem d c n sp raddr) (memset_exits mem d c n sp raddr) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memset_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold memset_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL X0 X1 X2 MEM SP X30 SMALL LOW NW START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold mbase in *; repeat match goal with H: _ /\ _ |- _ => destruct H end.
  all: try match goal with H: False |- _ => destruct H end.
  1: (arm8_step; splits; try assumption; match goal with |- context[?s R_Z0] => solve_splat c (s R_Z0) end).
  all: repeat grok_step.
  all: memset_prep.
  all: try (unfold memset_post); unfold mbase; splits; try reflexivity; try assumption; try lia.
  all: try (intros i I; memset_addr; repeat rd1; first [match goal with ZS: splat_bytes _ _ _ |- _ => memset_byte ZS end | lia | reflexivity]).
  all: try (intros x A O; memset_addr; repeat rd1; first [reflexivity | lia]).
  all: intros; match goal with H: _ V_MEM64 = _ |- _ => rewrite H end; reflexivity.
Qed.

(* mtx_init -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl's C source is (essentially)

       int mtx_init(mtx_t *m, int type) { *m = (mtx_t){ ._m_type = ((type&mtx_recursive) ? PTHREAD_MUTEX_RECURSIVE : PTHREAD_MUTEX_NORMAL) }; return thrd_success; }

   compiled to straight-line code without calls or stack use.

   SPECIFICATION
   -------------
   POSIX / Linux man-pages: mtx_init zeroes the 40-byte mutex, sets _m_type (offset 0, 32-bit) to type AND 1, and returns thrd_success (0) (musl representation; field offsets
   are those of musl's aarch64 structure layout, as used by the binary).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            mtx_init at 0x60d88 (ELF vaddr); 0x160d88 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/mtx_init_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = a, X1 = b, X2 = c (the pointer/integer arguments in order;
            unused ones are unconstrained); X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x160da0): s R_X0 = (0) /\ s V_MEM64 = (mem [Ⓠ a := 0] [Ⓠ a + 8 := 0] [Ⓓ a := N.land b 1] [Ⓠ a + 16 := 0] [Ⓠ a + 24 := 0] [Ⓠ a + 32 := 0])
            (Ⓑ/Ⓦ/Ⓓ/Ⓠ = little-endian 8/16/32/64-bit access).
            Memory changes exactly as stated (no other byte changes); SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import mtx_init_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf GrokLeaf2.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem mtx_init_nwc: ∀ s2 s1, mtx_init_armv8 s1 = mtx_init_armv8 s2.
Proof. reflexivity. Qed.

Theorem mtx_init_welltyped: welltyped_prog arm8typctx mtx_init_armv8.
Proof. Picinae_typecheck. Qed.


Theorem mtx_init_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates mtx_init_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem mtx_init_preserves_x30:
  forall_endstates mtx_init_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c : N).
  Definition mtx_init_post (s:store) :=
    s R_X0 = (0) /\ s V_MEM64 = (mem [Ⓠ a := 0] [Ⓠ a + 8 := 0] [Ⓓ a := N.land b 1] [Ⓠ a + 16 := 0] [Ⓠ a + 24 := 0] [Ⓠ a + 32 := 0]) /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x160d88 => Inv 0 (s R_X0 = a /\ s R_X1 = b /\ s R_X2 = c /\
                       s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160da0 => Post 0 (mtx_init_post s)
    | _ => NoInv
    end.
  Definition mtx_init_exits := make_exits 0 mtx_init_armv8 invs.
  Definition mtx_init_invs := make_invs 0 mtx_init_armv8 invs.
End Invariants.

Theorem mtx_init_partial_correctness:
  ∀ prog s sp mem raddr a b c t xs'
    (PROG: mtx_init_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x160d88, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_X1 = b) (X2: s R_X2 = c),
  satisfies_all prog (mtx_init_invs sp mem raddr a b c) (mtx_init_exits sp mem raddr a b c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=mtx_init_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold mtx_init_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply mtx_init_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
  repeat grok_step.
  all: unfold mtx_init_post; splits; try reflexivity; try assumption.

  all: try grok_leaf_close.
all: try grok_leaf_close2.
Qed.

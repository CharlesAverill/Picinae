(* cfmakeraw -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl's C source is (essentially)

       void cfmakeraw(struct termios *t) { t->c_iflag &= ~(IGNBRK|BRKINT|PARMRK|ISTRIP|INLCR|IGNCR|ICRNL|IXON); t->c_oflag &= ~OPOST; t->c_lflag &= ~(ECHO|ECHONL|ICANON|ISIG|IEXTEN); t->c_cflag &= ~(CSIZE|PARENB); t->c_cflag |= CS8; t->c_cc[VMIN] = 1; t->c_cc[VTIME] = 0; }

   compiled to straight-line code without calls or stack use.

   SPECIFICATION
   -------------
   POSIX / Linux man-pages: cfmakeraw clears the iflag/oflag bits (one 64-bit AND over offsets 0-7), clears CSIZE|PARENB and sets CS8 in c_cflag (offset 8), clears the lflag bits (offset 12), and writes VTIME=0, VMIN=1 (bytes 22-23 as the halfword 256) (musl representation; field offsets
   are those of musl's aarch64 structure layout, as used by the binary).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            cfmakeraw at 0x605c8 (ELF vaddr); 0x1605c8 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/cfmakeraw_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = a, X1 = b, X2 = c (the pointer/integer arguments in order;
            unused ones are unconstrained); X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x160600): s V_MEM64 = (mem [Ⓠ a := mem Ⓠ[a] .& 0xfffffffefffffa14] [Ⓓ a + 8 := (mem Ⓓ[a + 8] .& 0xfffffecf) .| 0x30] [Ⓓ a + 12 := mem Ⓓ[a + 12] .& 0xffff7fb4] [Ⓦ a + 22 := 256])
            (Ⓑ/Ⓦ/Ⓓ/Ⓠ = little-endian 8/16/32/64-bit access).
            Memory changes exactly as stated (no other byte changes); SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import cfmakeraw_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf GrokLeaf2.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem cfmakeraw_nwc: ∀ s2 s1, cfmakeraw_armv8 s1 = cfmakeraw_armv8 s2.
Proof. reflexivity. Qed.

Theorem cfmakeraw_welltyped: welltyped_prog arm8typctx cfmakeraw_armv8.
Proof. Picinae_typecheck. Qed.


Theorem cfmakeraw_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates cfmakeraw_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem cfmakeraw_preserves_x30:
  forall_endstates cfmakeraw_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c : N).
  Definition cfmakeraw_post (s:store) :=
    s V_MEM64 = (mem [Ⓠ a := mem Ⓠ[a] .& 0xfffffffefffffa14] [Ⓓ a + 8 := (mem Ⓓ[a + 8] .& 0xfffffecf) .| 0x30] [Ⓓ a + 12 := mem Ⓓ[a + 12] .& 0xffff7fb4] [Ⓦ a + 22 := 256]) /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x1605c8 => Inv 0 (s R_X0 = a /\ s R_X1 = b /\ s R_X2 = c /\
                       s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x160600 => Post 0 (cfmakeraw_post s)
    | _ => NoInv
    end.
  Definition cfmakeraw_exits := make_exits 0 cfmakeraw_armv8 invs.
  Definition cfmakeraw_invs := make_invs 0 cfmakeraw_armv8 invs.
End Invariants.

Theorem cfmakeraw_partial_correctness:
  ∀ prog s sp mem raddr a b c t xs'
    (PROG: cfmakeraw_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x1605c8, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_X1 = b) (X2: s R_X2 = c),
  satisfies_all prog (cfmakeraw_invs sp mem raddr a b c) (cfmakeraw_exits sp mem raddr a b c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=cfmakeraw_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold cfmakeraw_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply cfmakeraw_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
  repeat grok_step.
  all: unfold cfmakeraw_post; splits; try reflexivity; try assumption.

  all: try grok_leaf_close.
all: try grok_leaf_close2.
all: try grok_leaf_close3.
Qed.

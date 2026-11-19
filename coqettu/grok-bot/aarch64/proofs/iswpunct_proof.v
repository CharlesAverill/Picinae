(* iswpunct -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, straight-line)

   SEMANTICS
   ---------
   musl's C source is (essentially)

       int iswpunct(wint_t wc) { if (wc < 0x20000U) return (table[table[wc>>8]*32+((wc&255)>>3)]>>(wc&7))&1; return 0; }  (static const unsigned char table[] at ELF 0x73140, Ghidra 0x173140)

   compiled to straight-line code without calls or stack use.

   SPECIFICATION
   -------------
   POSIX / Linux man-pages: iswpunct for wc below 0x20000 returns bit (wc AND 7) of the bitmap byte table[table[wc>>8]*32 + ((wc AND 255)>>3)], both bytes read from memory at the table (ELF 0x73140; in the loaded binary that read-only data is musl two-level bitmap); for wc >= 0x20000 returns 0 (musl representation; field offsets
   are those of musl's aarch64 structure layout, as used by the binary).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            iswpunct at 0x1f1cc (ELF vaddr); 0x11f1cc in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/iswpunct_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = a, X1 = b, X2 = c (the pointer/integer arguments in order;
            unused ones are unconstrained); X30 = return address; m = memory.
   Output:  If execution reaches the RET (0x11f1dc): s R_X0 = (if a mod 2^32 <=? 131071 then (mem Ⓑ[0x173140 + (mem Ⓑ[0x173140 + (a mod 2^32 >> 8)] * 32 + (a >> 3) mod 32)] >> a mod 8) .& 1 else 0) /\ s V_MEM64 = (mem)
            (Ⓑ/Ⓦ/Ⓓ/Ⓠ = little-endian 8/16/32/64-bit access).
            Memory is unchanged; SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import iswpunct_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokLeaf GrokLeaf2 GrokRange.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem iswpunct_nwc: ∀ s2 s1, iswpunct_armv8 s1 = iswpunct_armv8 s2.
Proof. reflexivity. Qed.

Theorem iswpunct_welltyped: welltyped_prog arm8typctx iswpunct_armv8.
Proof. Picinae_typecheck. Qed.

Theorem iswpunct_preserves_memory:
  forall_endstates iswpunct_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem iswpunct_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates iswpunct_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem iswpunct_preserves_x30:
  forall_endstates iswpunct_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Invariants and partial correctness                                      *)

Section Invariants.
  Variables (sp mem raddr a b c : N).
  Definition iswpunct_post (s:store) :=
    s R_X0 = (if a mod 2^32 <=? 131071 then (mem Ⓑ[0x173140 + (mem Ⓑ[0x173140 + (a mod 2^32 >> 8)] * 32 + (a >> 3) mod 32)] >> a mod 8) .& 1 else 0) /\ s V_MEM64 = (mem) /\ s R_SP = sp /\ s R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    | 0x11f1cc => Inv 0 (s R_X0 = a /\ s R_X1 = b /\ s R_X2 = c /\
                       s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x11f1dc => Post 0 (iswpunct_post s)
    | _ => NoInv
    end.
  Definition iswpunct_exits := make_exits 0 iswpunct_armv8 invs.
  Definition iswpunct_invs := make_invs 0 iswpunct_armv8 invs.
End Invariants.

Theorem iswpunct_partial_correctness:
  ∀ prog s sp mem raddr a b c t xs'
    (PROG: iswpunct_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11f1cc, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = a) (X1: s R_X1 = b) (X2: s R_X2 = c),
  satisfies_all prog (iswpunct_invs sp mem raddr a b c) (iswpunct_exits sp mem raddr a b c) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=iswpunct_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold iswpunct_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 X2 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply iswpunct_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & X2 & MEM & SP & X30).
  repeat grok_step.
  all: unfold iswpunct_post; splits; try reflexivity; try assumption.

  all: try grok_leaf_close.
  all: try clear MDL1.
  all: grok_tab_close.
Qed.

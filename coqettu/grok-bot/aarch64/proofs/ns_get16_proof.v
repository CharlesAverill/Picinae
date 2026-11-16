(* ns_get16 -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/network/ns_parse.c: ns_get16 return cp[0]<<8 | cp[1];
   compiled to  ldrh w0,[x0]; rev16 w0,w0; and w0,w0,#0xffff; ret.

   SPECIFICATION
   -------------
   There is no Linux man-pages entry for the ns_* helpers.  They come from
   BIND's libresolv (ns_parse.c / arpa/nameser.h), where they read or
   write integers in network byte order (big-endian):
     unsigned      ns_get16(const unsigned char *src);   16-bit value at src
     unsigned long ns_get32(const unsigned char *src);   32-bit value at src
     void          ns_put16(unsigned int src, unsigned char *dst);
     void          ns_put32(unsigned long src, unsigned char *dst);
   ns_put16/ns_put32 store the low 16/32 bits of src at dst, most
   significant byte first.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            ns_get16 at 0x43f4c (ELF vaddr); 0x143f4c in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/ns_get16_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = src (any address); X30 = return address.
   Output:  If execution reaches the RET (0x143f58): X0 = getmem 64 BigE 2 mem src,
            the big-endian 16-bit value at src.  Memory, SP, X30 and the
            AAPCS64 callee-saved registers are unchanged.
   Proof: the rev/rev16 bit network is matched against Picinae's revbytes by
   reflection (lib/GrokBytes.v, lib/GrokBitRefl.v); BigE = revbytes of LittleE.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import ns_get16_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl GrokBytes.
Import ARM8Notations.
Open Scope N.

Theorem ns_get16_welltyped: welltyped_prog arm8typctx ns_get16_armv8.
Proof. Picinae_typecheck. Qed.

Theorem ns_get16_preserves_memory:
  forall_endstates ns_get16_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ns_get16_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates ns_get16_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem ns_get16_preserves_x30:
  forall_endstates ns_get16_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x143f4c => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x143f58 => Post 0 (s R_X0 = getmem 64 BigE 2 mem c /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ns_get16_exits := make_exits 0 ns_get16_armv8 invs.
  Definition ns_get16_invs := make_invs 0 ns_get16_armv8 invs.
End Invariants.

Theorem ns_get16_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: ns_get16_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x143f4c, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (ns_get16_invs sp mem raddr c d) (ns_get16_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ns_get16_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ns_get16_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ns_get16_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: rewrite (getmem_revbytes 64 BigE LittleE) by discriminate.
  replace (getmem 64 LittleE 1 mem c) with (getmem 64 LittleE 2 mem c mod 2^(1*8)) by (rewrite getmem_mod; reflexivity).
  pose proof (getmem_bound 64 LittleE 2 mem c) as YB.
  apply N.bits_inj; intro i. destruct (N.lt_ge_cases i (2*8)) as [LT|GE].
  - rev_low (getmem 64 LittleE 2 mem c) 2.
  - rewrite revbytes_high by assumption.
    match goal with |- N.testbit ?t i = _ =>
      let e := reify_bx (getmem 64 LittleE 2 mem c) t in change t with (bden (getmem 64 LittleE 2 mem c) e);
      apply bbnd_ok; [cbn in YB; lia | let v := eval vm_compute in (bbnd e) in change (bbnd e) with v; cbn in GE; lia]
    end.
Qed.

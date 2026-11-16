(* ntohs -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/network/ntohs.c:
       uint16_t ntohs(uint16_t n) {
           union { int i; char c; } u = { 1 };
           return u.c ? bswap_16(n) : n;
       }
   compiled (little-endian) to "rev16 w0,w0; ret".

   SPECIFICATION (man 3 byteorder, Linux man-pages 6.9.1)
   ------------------------------------------------------
     SYNOPSIS
            #include <arpa/inet.h>
            uint16_t ntohs(uint16_t netshort);
     DESCRIPTION
            The ntohs() function converts the unsigned short integer netshort
            from network byte order to host byte order.
            On the i386 the host byte order is Least Significant Byte first,
            whereas the network byte order, as used on the Internet, is Most
            Significant Byte first.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            ntohs at 0x443c4 (ELF vaddr); 0x1443c4 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/ntohs_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = x; X30 = return address.
   Output:  If execution reaches the RET (0x1443c8):
            X0 mod 2^16 = revbytes (x mod 2^16) 2 (the uint16_t result:
            the two low bytes swapped) and X0 < 2^32.  rev16 also swaps the
            bytes of bits 16..31 of W0, which AAPCS64 leaves unspecified for
            a uint16_t argument, so those result bits are not specified.
            Memory, SP, X30 and all AAPCS64 callee-saved registers are
            unchanged.  aarch64 is little-endian, so the host-to-network
            conversion is the byte swap.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import ntohs_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl GrokBytes.
Import ARM8Notations.
Open Scope N.
Theorem ntohs_welltyped: welltyped_prog arm8typctx ntohs_armv8.
Proof. Picinae_typecheck. Qed.

Theorem ntohs_preserves_memory:
  forall_endstates ntohs_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ntohs_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates ntohs_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.
Section Invariants.
  Variables (sp mem raddr x : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x1443c4 => Inv 0 (s R_X0 = x /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x1443c8 => Post 0 (s R_X0 mod 2^16 = revbytes (x mod 2^16) 2 /\ s R_X0 < 2^32 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ntohs_exits := make_exits 0 ntohs_armv8 invs.
  Definition ntohs_invs := make_invs 0 ntohs_armv8 invs.
End Invariants.
Theorem ntohs_partial_correctness:
  ∀ prog s sp mem raddr x t xs'
    (PROG: ntohs_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x1443c4, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = x),
  satisfies_all prog (ntohs_invs sp mem raddr x) (ntohs_exits sp mem raddr x) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ntohs_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold ntohs_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ntohs_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  pose proof (MDL1 R_X0 64 eq_refl) as YB. rewrite X0 in YB.
  repeat arm8_step.
  splits; try reflexivity; try assumption.
  - apply N.bits_inj; intro i. destruct (N.lt_ge_cases i (2*8)) as [LT|GE].
    + transitivity (N.testbit (revbytes x 2) i).
      * rev_low x 2.
      * rewrite !revbytes_spec, (proj2 (N.ltb_lt _ _) LT).
        rewrite N.mod_pow2_bits_low. reflexivity. unfold rbf.
        assert (i/8 < 2) by (apply N.Div0.div_lt_upper_bound; lia).
        pose proof (N.mod_lt i 8 ltac:(discriminate)). lia.
    + rewrite revbytes_high by (try apply N.mod_lt; try discriminate; assumption).
      match goal with |- N.testbit ?t i = _ =>
        let e := reify_bx x t in change t with (bden x e);
        apply bbnd_ok; [cbn in YB; lia | let v := eval vm_compute in (bbnd e) in change (bbnd e) with v; cbn in GE; lia]
      end.
  - match goal with |- ?t < _ =>
      enough (E: t mod 2^32 = t) by (rewrite <- E; apply N.mod_lt; discriminate) end.
    apply N.bits_inj; intro i. destruct (N.lt_ge_cases i 32) as [LT|GE].
    + apply N.mod_pow2_bits_low. exact LT.
    + rewrite N.mod_pow2_bits_high by exact GE.
      match goal with |- false = N.testbit ?t i =>
        let e := reify_bx x t in change t with (bden x e); symmetry;
        apply bbnd_ok; [cbn in YB; lia | let v := eval vm_compute in (bbnd e) in change (bbnd e) with v; lia]
      end.
Qed.

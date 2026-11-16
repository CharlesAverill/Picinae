(* sigismember -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/signal/sigismember.c (64-bit long, _NSIG = 65 on aarch64):
       int sigismember(const sigset_t *set, int sig)
       {
           unsigned s = sig-1;
           if (s >= _NSIG-1) return 0;
           return !!(set->__bits[s/64] & 1UL<<(s%64));   (paraphrased)
       }
   compiled to  sub w1,w1,#1; cmp w1,#63; b.hi L; ldr x0,[x0]; lsr x0,x0,x1;
   and w0,w0,#1; ret; L: mov w0,#0; b ret.

   SPECIFICATION (man 3 sigsetops, Linux man-pages 6.9.1)
   ------------------------------------------------------
     SYNOPSIS
            #include <signal.h>
            int sigismember(const sigset_t *set, int signum);
     DESCRIPTION
            sigismember() tests whether signum is a member of set.
     RETURN VALUE
            sigismember() returns 1 if signum is a member of set, 0 if signum
            is not a member, and -1 on error.
     ERRORS
            EINVAL signum is not a valid signal.
   (musl does not report EINVAL here: an out-of-range signum gives 0.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            sigismember at 0x52330 (ELF vaddr); 0x152330 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/sigismember_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = set, X1 = signum (only signum mod 2^32 is used); X30 = return
            address.
   Output:  If execution reaches the RET (0x152348), with s = (signum - 1) mod 2^32:
            X0 = bit s of the 64-bit little-endian word at set when s < 64
            (i.e. 1 <= signum <= 64), and X0 = 0 otherwise
            (sigismember_spec).  Only the 8 bytes at set are read, and only
            when s < 64.  Memory, SP, X30 and the AAPCS64 callee-saved
            registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import sigismember_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokSig.
Import ARM8Notations.
Open Scope N.

Theorem sigismember_welltyped: welltyped_prog arm8typctx sigismember_armv8.
Proof. Picinae_typecheck. Qed.

Theorem sigismember_preserves_memory:
  forall_endstates sigismember_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem sigismember_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates sigismember_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem sigismember_preserves_x30:
  forall_endstates sigismember_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition sigismember_spec (mem p sig : N) : N :=
  let s := msub 32 sig 1 in if s <? 64 then N.land (N.shiftr (getmem 64 LittleE 8 mem p) s) 1 else 0.

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition sinvs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x152330 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x152348 => Post 0 (s R_X0 = sigismember_spec mem c d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition sim_exits := make_exits 0 sigismember_armv8 sinvs.
  Definition sim_invs := make_invs 0 sigismember_armv8 sinvs.
End Invariants.

Theorem sigismember_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: sigismember_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x152330, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (sim_invs sp mem raddr c d) (sim_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=sigismember_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold sim_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigismember_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: unfold sigismember_spec; pose proof (msub32_1 d) as M.
  - assert (S: msub 32 d 1 < 64).
    { destruct (N.eqb_spec (d mod 2^32) 64) as [E|E].
      - rewrite M, E. cbn. lia.
      - destruct (N.leb_spec 63 (msub 32 d 1)) as [L|L]; [discriminate BC | lia]. }
    rewrite (proj2 (N.ltb_lt _ _) S), msub6_32, (N.mod_small _ (2^6)) by exact S.
    change (N.land (N.shiftr ?x ?y) 1) with (N.land (N.shiftr x y) (N.ones 1)).
    rewrite N.land_ones. reflexivity.
  - destruct (N.eqb_spec (d mod 2^32) 64) as [E|E]; [discriminate BC|].
    destruct (N.leb_spec 63 (msub 32 d 1)) as [L|L]; [|discriminate BC].
    assert (S: 64 <= msub 32 d 1).
    { destruct (N.eqb_spec (d mod 2^32) 0) as [Z|Z]; rewrite M in *; lia. }
    rewrite (proj2 (N.ltb_ge _ _) S). reflexivity.
Qed.

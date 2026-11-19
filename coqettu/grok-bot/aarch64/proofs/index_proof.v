(* index -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (tail call to strchr)

   SEMANTICS
   ---------
   musl's src/legacy/index.c:
       char *index(const char *s, int c) { return strchr(s, c); }
   compiled to a single instruction at 0x15e124: b 0x15ebcc (strchr).  The
   proof reuses strchr_partial_correctness (proofs/strchr_proof.v, which
   covers strchr, strchrnul and strlen) through the generic tail-call lemma
   tailcall_satisfies_all of lib/GrokTail.v: any trace starting at index's
   entry is one Jmp step followed by a trace starting at strchr's entry with
   the same register file and memory, and the make_invs/make_exits
   invariant sets only inspect the newest trace element.

   SPECIFICATION (man 3 index, Linux man-pages 6.9.1)
   --------------------------------------------------
     SYNOPSIS
            #include <strings.h>
            char *index(const char *s, int c);
     DESCRIPTION
            index() is identical to strchr(3).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            index at 0x5e124 (ELF vaddr); 0x15e124 in Ghidra (image base 0x100000);
            target strchr at 0x5ebcc / 0x15ebcc
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/index_armv8.v,
            ../lifted/strchr_armv8.v, ../lifted/strchrnul_armv8.v and
            ../lifted/strlen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s (p), X1 = c, SP = sp, X30 = raddr, X29 = x29, memory mem;
            the program contains index, strchr, strchrnul and strlen.
            No precondition beyond strchr's (none).
   Output:  Exactly strchr's invariant set and postcondition, invs2/exits2 of
            strchr_callees.v, instantiated with the entry values: if execution
            reaches strchr's RET (0x15ebf0), SP = sp, X30 = raddr, X29 = x29,
            memory is mem plus strchr's/strchrnul's saved frame, and
            X0 = r if the byte at r equals c mod 2^8, else 0, where r is the
            strchrnul_spec result (first occurrence of c mod 2^8 or the
            terminator).  Partial correctness only.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require index_armv8 strchr_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokTail.
From Grok.proofs Require Import strchr_callees strchr_proof.
Import ARM8Notations.
Open Scope N.

Theorem index_partial_correctness:
  ∀ prog s sp mem raddr p c x29 t xs'
    (P3: index_armv8.index_armv8 ⊆2 prog)
    (P2: strchr_armv8.strchr_armv8 ⊆2 prog) (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e124, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = p) (X1: s R_X1 = c) (X29: s R_X29 = x29),
  satisfies_all prog (invs2 sp mem raddr p c x29) (exits2 sp mem raddr p c x29) (xs'::t).
Proof.
  intros.
  apply (tailcall_satisfies_all prog (invs2 sp mem raddr p c x29) (exits2 sp mem raddr p c x29))
    with (a0 := 0x15e124) (a1 := 0x15ebcc)
         (P := fun s => models arm8typctx s /\ s R_SP = sp /\ s V_MEM64 = mem /\ s R_X30 = raddr /\
                        s R_X0 = p /\ s R_X1 = c /\ s R_X29 = x29) (s := s).
  - intros [[a|i] s1] t1 t2; reflexivity.
  - intros [[a|i] s1] t1 t2; reflexivity.
  - reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intro s1. apply P3. reflexivity.
  - intros s1 s2 E (M & H1 & H2 & H3 & H4 & H5 & H6). rewrite <- !E.
    split; [|repeat split; assumption]. intros v w CV. rewrite <- E. exact (M v w CV).
  - intros s1 t1 xs1 START (M & H1 & H2 & H3 & H4 & H5 & H6).
    eapply strchr_partial_correctness; eassumption.
  - exact ENTRY.
  - repeat split; assumption.
Qed.

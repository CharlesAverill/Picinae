(* bzero -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C, restricted to n <= 96

   SEMANTICS
   ---------
   musl src/string/bzero.c:
       void bzero(void *s, size_t n) { memset(s, 0, n); }
   compiled to mov x2, x1; mov w1, #0; b memset (a tail call).

   SPECIFICATION (man 3 bzero, Linux man-pages 6.9.1)
   ----------------------------------------------------
     The bzero() function erases the data in the n bytes of the memory
     starting at the location pointed to by s, by writing zeros (bytes
     containing 0) to that area.

   RESTRICTION
   -----------
   Same preconditions as proofs/memset_proof.v (n <= 96, 4096 <= s,
   s + n < 2^64), for the same reasons (see that header): the n > 96 path
   of memset reaches instructions lifted as Nop and is never entered.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            bzero at 0x5e0fc (ELF vaddr); 0x15e0fc in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/bzero_armv8.v and ../lifted/memset_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s = d, X1 = n; X30 = return address raddr; SP = sp;
            mem = memory on entry.  The program contains bzero and memset.
   Output:  If execution reaches any RET of memset (the tail-called code):
            X0 = d, SP = sp, X30 = raddr, every byte d+i for i < n is 0 and
            every byte outside [d, d+n) is unchanged (memset_post with c = 0).
            The three bzero instructions write only X1 and X2 (see bzero_preserves_memory and the other frame theorems).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import bzero_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokTail GrokFill.
From Grok.proofs Require Import memset_proof.
Import ARM8Notations.
Open Scope N.

Theorem bzero_nwc: ∀ s2 s1, bzero_armv8 s1 = bzero_armv8 s2.
Proof. reflexivity. Qed.

Theorem bzero_welltyped: welltyped_prog arm8typctx bzero_armv8.
Proof. Picinae_typecheck. Qed.

Theorem bzero_preserves_memory:
  forall_endstates bzero_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem bzero_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates bzero_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem bzero_preserves_x30:
  forall_endstates bzero_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition bz_pre (mem d n sp raddr : N) (s:store) :=
  models arm8typctx s /\ s R_SP = sp /\ s V_MEM64 = mem /\ s R_X30 = raddr /\ s R_X0 = d /\
  n <= 96 /\ 4096 <= d /\ d + n < 2^64.

Ltac bz_move v u :=
  repeat rewrite (reset_move _ v u 64) by reflexivity;
  repeat first [ rewrite update_updated | rewrite update_frame by discriminate ].

Theorem bzero_partial_correctness:
  ∀ prog s mem d n sp raddr t xs'
    (P1: bzero_armv8 ⊆2 prog) (P0: memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x15e0fc, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = d) (X1: s R_X1 = n) (MEM: s V_MEM64 = mem) (SP: s R_SP = sp) (X30: s R_X30 = raddr)
    (SMALL: n <= 96) (LOW: 4096 <= d) (NW: d + n < 2^64),
  satisfies_all prog (memset_invs mem d 0 n sp raddr) (memset_exits mem d 0 n sp raddr) (xs'::t).
Proof.
  intros.
  apply (step_satisfies_all prog (memset_invs mem d 0 n sp raddr) (memset_exits mem d 0 n sp raddr))
    with (a0 := 0x15e0fc) (a1 := 0x15e100) (sz := 4) (q := Move R_X2 (Var R_X1))
         (P := fun s => bz_pre mem d n sp raddr s /\ s R_X1 = n)
         (Q := fun s => bz_pre mem d n sp raddr s /\ s R_X2 = n) (s := s).
  - intros [[a|i] s1] t1 t2; reflexivity.
  - intros [[a|i] s1] t1 t2; reflexivity.
  - reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intro s1. apply P1. reflexivity.
  - intros s1 c1 s2 x1 ((M & H1 & H2 & H3 & H4 & H5 & H6 & H7) & H8) XS.
    inversion XS; subst. inversion E; subst. split. reflexivity.
    assert (MU: models arm8typctx (s1[R_X2 := s1 R_X1])).
    { apply models_update; [ cbn; exact (M R_X1 64 eq_refl) | exact M ]. }
    unfold bz_pre. bz_move R_X2 (s1 R_X1).
    repeat split; try assumption.
    intros vv ww CV. rewrite (reset_move _ R_X2 (s1 R_X1) 64) by reflexivity. exact (MU vv ww CV).
  - intros s1 t1 xs1 START1 PQ.
    apply (step_satisfies_all prog (memset_invs mem d 0 n sp raddr) (memset_exits mem d 0 n sp raddr))
      with (a0 := 0x15e100) (a1 := 0x15e104) (sz := 4) (q := Move R_X1 (Word 0 64))
           (P := fun s => bz_pre mem d n sp raddr s /\ s R_X2 = n)
           (Q := fun s => bz_pre mem d n sp raddr s /\ s R_X2 = n /\ s R_X1 = 0) (s := s1).
    + intros [[a|i] s2] t2 t3; reflexivity.
    + intros [[a|i] s2] t2 t3; reflexivity.
    + reflexivity.
    + intros; reflexivity.
    + intros; reflexivity.
    + intro s2. apply P1. reflexivity.
    + intros s2 c1 s3 x1 ((M & H1 & H2 & H3 & H4 & H5 & H6 & H7) & H8) XS.
      inversion XS; subst. inversion E; subst. split. reflexivity.
      assert (MU: models arm8typctx (s2[R_X1 := 0])).
      { apply models_update; [ cbn; reflexivity | exact M ]. }
      unfold bz_pre. bz_move R_X1 0.
      repeat split; try assumption; try reflexivity.
      intros vv ww CV. rewrite (reset_move _ R_X1 0 64) by reflexivity. exact (MU vv ww CV).
    + intros s2 t2 xs2 START2 PQ2.
      apply (tailcall_satisfies_all prog (memset_invs mem d 0 n sp raddr) (memset_exits mem d 0 n sp raddr))
        with (a0 := 0x15e104) (a1 := 0x118400)
             (P := fun s => bz_pre mem d n sp raddr s /\ s R_X2 = n /\ s R_X1 = 0) (s := s2).
      * intros [[a|i] s3] t3 t4; reflexivity.
      * intros [[a|i] s3] t3 t4; reflexivity.
      * reflexivity.
      * intros; reflexivity.
      * intros; reflexivity.
      * intro s3. apply P1. reflexivity.
      * intros s3 s4 EQ ((M & H1 & H2 & H3 & H4 & H5 & H6 & H7) & H8 & H9). unfold bz_pre. rewrite <- !EQ.
        repeat split; try assumption. intros v w CV. rewrite <- EQ. exact (M v w CV).
      * intros s3 t3 xs3 START3 ((M & H1 & H2 & H3 & H4 & H5 & H6 & H7) & H8 & H9).
        eapply memset_partial_correctness; eassumption.
      * exact START2.
      * exact PQ2.
    + exact START1.
    + exact PQ.
  - exact ENTRY.
  - unfold bz_pre. repeat split; assumption.
Qed.

(* memccpy -- copy memory area up to a given byte

   SEMANTICS
   ---------
   memccpy(dest, src, c, n) copies bytes from src to dest, stopping after the
   first occurrence of (unsigned char) c is copied, or after n bytes.  It
   returns a pointer to the byte after c in dest, or NULL if c was not found.
   glibc's memccpy is a NON-LEAF function: it calls memchr(src, c, n)
   (CALL 0x128420).  If memchr finds c at offset k it TAIL-CALLS
   mempcpy(dest, src, k+1) (JMP 0x1283e0), which returns dest+k+1.  Otherwise
   it calls memcpy(dest, src, n) (CALL 0x128620) and returns NULL.  As in
   amd64_strdup_proof.v, the callees are arbitrary code cp with assumed
   contracts, and the theorem ends at the jump into mempcpy, stating its
   arguments exactly.

   SPECIFICATION (man 3 memccpy, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------
            void *memccpy(void *restrict dest, const void *restrict src,
                          int c, size_t n);

            The memccpy() function copies no more than n bytes from memory area
            src to memory area dest, stopping when the character c is found.

            If the memory areas overlap, the results are undefined.

            The memccpy() function returns a pointer to the next character in
            dest after c, or NULL if c was not found in the first n characters
            of src.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol memccpy at 0x1a9bb0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh (global addressing); see memccpy_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dest, RSI = src, EDX = c, RCX = n, RSP = sp, memory m.  The
            frame is the 32 bytes below sp.
   Preconditions:  src[0..n) lies outside the frame; dest[0..n) lies outside
            the frame and the return address (the 40 bytes from sp-32); cp
            meets the memchr and memcpy contracts.
   Output:  Let u = c mod 2^8.  Exactly one of two exits is reached:
              JMP mempcpy:  some k < n has src[k] = u and src[i] <> u for
                    i < k; RDI = dest, RSI = src, RDX = k+1, RSP = sp, and
                    memory equals m outside the frame;
              RET:  src[i] <> u for all i < n; RAX = 0; dest[0..n) holds
                    src[0..n) (as in m), and every byte outside dest[0..n)
                    and the frame equals its value in m.
            At either exit RBX, RBP and R12-R15 have their entry values.
            (Partial correctness.)
   Callee model:  memchr must leave memory unchanged; memcpy must produce
            `copied` (amd64_memcpy_sets.v) relative to the memory at the call.
 *)

Require Import Picinae_amd64.
Require Import memccpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring amd64_memcpy_sets.
Import ListNotations.
Open Scope N.

Theorem memccpy_nwc: forall s2 s1, memccpy_amd64 s1 = memccpy_amd64 s2.
Proof. reflexivity. Qed.

Theorem memccpy_welltyped: welltyped_prog x64typctx memccpy_amd64.
Proof. Picinae_typecheck. Qed.

Definition P_MEMCHR := 0x128420.
Definition P_MEMCPY := 0x128620.
Definition P_MEMPCPY := 0x1283e0.
Definition RET_MEMCHR := 0x1a9bcf.
Definition RET_MEMCPY := 0x1a9bfe.

Definition memccpy_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match memccpy_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma memccpy_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (memccpy_with cp).
Proof.
  intros cp WT s a. unfold memccpy_with.
  pose proof (memccpy_welltyped s a) as H.
  destruct (memccpy_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

Definition fr (sp:N) := sp ⊖ 32.

(* r = memchr(p, c, n) in memory m. *)
Definition mchr (m:memory) p c n r :=
  (r = 0 /\ forall i, i < n -> m Ⓑ[p ⊕ i] <> c) \/
  (exists k, k < n /\ r = p ⊕ k /\ m Ⓑ[p ⊕ k] = c /\ forall i, i < k -> m Ⓑ[p ⊕ i] <> c).

Section Invariants.
  Variable sp : N.
  Variable mem : memory.
  (* callee or memccpy arguments *)
  Variables a1 a2 a3 a4 : N.
  Variable rbx rbp r12 r13 r14 r15 : N.

  Definition saved (s:store) :=
    s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
    s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* memchr (subroutine 0): memchr(a1, a2, a3) *)
    | 0x128420 => Inv 0 (s R_RDI = a1 /\ s R_RSI = a2 /\ s R_RDX = a3 /\ s R_RSP = sp /\
                         s V_MEM64 = mem /\ mem Ⓠ[sp] = RET_MEMCHR /\ saved s)
    | 0x1a9bcf => Post 0 (mchr mem a1 (a2 mod 2^8) a3 (s R_RAX) /\ s R_RSP = sp ⊕ 8 /\
                          s V_MEM64 = mem /\ saved s)
    (* memcpy (subroutine 1): memcpy(a1, a2, a3) *)
    | 0x128620 => Inv 1 (s R_RDI = a1 /\ s R_RSI = a2 /\ s R_RDX = a3 /\ s R_RSP = sp /\
                         s V_MEM64 = mem /\ mem Ⓠ[sp] = RET_MEMCPY /\ saved s)
    | 0x1a9bfe => Post 1 (copied mem (s V_MEM64) a1 a2 a3 /\ s R_RSP = sp ⊕ 8 /\ saved s)
    (* memccpy (subroutine 2): memccpy(a1, a2, a3, a4) *)
    | 0x1a9bb0 => Inv 2 (s R_RDI = a1 /\ s R_RSI = a2 /\ s R_RDX = a3 /\ s R_RCX = a4 /\
                         s R_RSP = sp /\ s V_MEM64 = mem /\ saved s)
    | 0x1a9bf6 => Inv 2 ((forall i, i < a4 -> mem Ⓑ[a2 ⊕ i] <> a3 mod 2^8) /\
                         s R_RSI = a2 /\ s R_RDX = a4 /\ s R_RSP = sp ⊖ 24 /\
                         s R_R13 = a1 /\ s R_R12 = a4 /\ s R_RBP = a2 /\
                         s R_RBX = rbx /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                         s V_MEM64 Ⓠ[sp ⊖ 8] = r13 /\ s V_MEM64 Ⓠ[sp ⊖ 16] = r12 /\
                         s V_MEM64 Ⓠ[sp ⊖ 24] = rbp /\ agree (fr sp) 32 (s V_MEM64) mem)
    | 0x1a9c05 => Post 2 ((forall i, i < a4 -> mem Ⓑ[a2 ⊕ i] <> a3 mod 2^8) /\
                          s R_RAX = 0 /\ s R_RSP = sp /\ saved s /\
                          (forall i, i < a4 -> s V_MEM64 Ⓑ[a1 ⊕ i] = mem Ⓑ[a2 ⊕ i]) /\
                          (forall b, ~ msub 64 b a1 < a4 -> ~ inwin (fr sp) 32 b ->
                                     s V_MEM64 Ⓑ[b] = mem Ⓑ[b]))
    | 0x1283e0 => Post 2 (exists k, k < a4 /\ mem Ⓑ[a2 ⊕ k] = a3 mod 2^8 /\
                          (forall i, i < k -> mem Ⓑ[a2 ⊕ i] <> a3 mod 2^8) /\
                          s R_RDI = a1 /\ s R_RSI = a2 /\ s R_RDX = k ⊕ 1 /\ s R_RSP = sp /\
                          saved s /\ agree (fr sp) 32 (s V_MEM64) mem)
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (memccpy_with cp) invs.
  Definition invs0 cp := make_invs 0 (memccpy_with cp) invs.
  Definition exits1 cp := make_exits 1 (memccpy_with cp) invs.
  Definition invs1 cp := make_invs 1 (memccpy_with cp) invs.
  Definition exits2 cp := make_exits 2 (memccpy_with cp) invs.
  Definition invs2 cp := make_invs 2 (memccpy_with cp) invs.
End Invariants.

Definition memchr_contract (cp: store -> addr -> N * stmt) :=
  forall s t xs' sp mem p c n rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_MEMCHR, s) -> models x64typctx s ->
  s R_RDI = p -> s R_RSI = c -> s R_RDX = n -> s R_RSP = sp -> s V_MEM64 = mem ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_MEMCHR ->
  satisfies_all (memccpy_with cp)
    (invs0 sp mem p c n 0 rbx rbp r12 r13 r14 r15 cp)
    (exits0 sp mem p c n 0 rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Definition memcpy_contract (cp: store -> addr -> N * stmt) :=
  forall s t xs' sp mem d p n rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_MEMCPY, s) -> models x64typctx s ->
  s R_RDI = d -> s R_RSI = p -> s R_RDX = n -> s R_RSP = sp -> s V_MEM64 = mem ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_MEMCPY ->
  satisfies_all (memccpy_with cp)
    (invs1 sp mem d p n 0 rbx rbp r12 r13 r14 r15 cp)
    (exits1 sp mem d p n 0 rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Lemma frame_nov:
  forall a sp x, 8 <= x <= 32 -> ~ overlap 64 a 8 (fr sp) 32 -> ~ overlap 64 a 8 (sp ⊖ x) 8.
Proof.
  intros a sp x X NO [i [j [I [J E]]]]. apply NO. exists i, (32 - x + j).
  split; [exact I|]. split; [lia|]. rewrite E. clear - X. unfold fr, msub.
  rewrite !N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small x), (N.mod_small 32) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma agree_frame8:
  forall sp x M m v, 8 <= x <= 32 -> agree (fr sp) 32 M m ->
  agree (fr sp) 32 (M [Ⓠ sp ⊖ x := v]) m.
Proof.
  intros. apply agree_setwin; try assumption; try (change (2^64) with 18446744073709551616; lia).
  clear - H. unfold fr, msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma getmem8_agree:
  forall (M1 M2:memory) a, (forall a', msub 64 a' a < 8 -> M1 Ⓑ[a'] = M2 Ⓑ[a']) -> M1 Ⓠ[a] = M2 Ⓠ[a].
Proof.
  intros M1 M2 a H. apply getmem_frame_mem. intros a' A. rewrite <- !(getmem_1 64 LittleE). apply H, A.
Qed.

(* A slot of the frame lies in the 40 bytes from sp-32. *)
Lemma slot_in40:
  forall sp x a, 8 <= x <= 32 -> msub 64 a (sp ⊖ x) < 8 -> msub 64 a (fr sp) < 40.
Proof.
  intros sp x a X A. unfold fr. clear - X A. unfold msub in *.
  change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma rsp_back: forall sp, sp ⊖ 32 ⊕ 8 = sp ⊖ 24.
Proof.
  intro sp. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small 32), (N.mod_small 24) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Ltac slot_nov :=
  intros [i [j [I [J E]]]]; clear - I J E; unfold msub in E; change (2^64) with 18446744073709551616 in *; lia.

Lemma mchr_agree:
  forall lo len M m p c n r, agree lo len M m -> (forall i, i < n -> ~ inwin lo len (p ⊕ i)) ->
  mchr M p c n r -> mchr m p c n r.
Proof.
  intros lo len M m p c n r A F [[R0 NO]|[k [K [R [E NO]]]]].
  - left. split. exact R0. intros i I. rewrite <- (A _ (F i I)). apply NO, I.
  - right. exists k. split. exact K. split. exact R. split.
    rewrite <- (A _ (F k K)). exact E.
    intros i I. rewrite <- (A _ (F i ltac:(lia))). apply NO, I.
Qed.

(* A frame slot is not in dest, so memcpy leaves it alone. *)
Lemma slot_not_dst:
  forall sp dst n a', (forall i, i < n -> 40 <= msub 64 (dst ⊕ i) (fr sp)) ->
  msub 64 a' (fr sp) < 40 -> ~ msub 64 a' dst < n.
Proof.
  intros sp dst n a' DF A I. specialize (DF _ I).
  rewrite add_msub, msub_mod_l in DF by reflexivity. lia.
Qed.

Lemma getmem8_copied:
  forall M1 M2 dst src n sp a x, copied M1 M2 dst src n ->
  (forall i, i < n -> 40 <= msub 64 (dst ⊕ i) (fr sp)) ->
  8 <= x <= 32 -> a = sp ⊖ x -> M2 Ⓠ[a] = M1 Ⓠ[a].
Proof.
  intros M1 M2 dst src n sp a x [_ OUT] DF X ->. apply getmem8_agree. intros a' A.
  apply OUT, (slot_not_dst sp dst n a' DF). eapply slot_in40; eassumption.
Qed.

Theorem memccpy_correct:
  forall cp s t xs' sp mem dst src c n
         (WT: welltyped_code cp) (MEMCHR: memchr_contract cp) (MEMCPY: memcpy_contract cp)
         (ENTRY: startof t xs' = (Addr 0x1a9bb0, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem)
         (RDI: s R_RDI = dst) (RSI: s R_RSI = src) (RDX: s R_RDX = c) (RCX: s R_RCX = n)
         (SPB: sp < 2^64) (SRC0: 0 < src) (SRCW: src + n <= 2^64)
         (SRCF: forall i, i < n -> ~ inwin (fr sp) 32 (src ⊕ i))
         (DSTF: forall i, i < n -> 40 <= msub 64 (dst ⊕ i) (fr sp)),
  satisfies_all (memccpy_with cp)
    (invs2 sp mem dst src c n (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits2 sp mem dst src c n (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memccpy_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT MEMCHR MEMCPY SPB SRC0 SRCW SRCF DSTF. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  - (* entry: call memchr *)
    destruct PRE as (RDI & RSI & RDX & RCX & RSP & MEM & RBX & RBP & R12 & R13 & R14 & R15).
    assert (B1 := MDL R_R12 64 eq_refl). assert (B2 := MDL R_RBP 64 eq_refl). assert (B3 := MDL R_R13 64 eq_refl).
    assert (NB := MDL R_RCX 64 eq_refl). assert (SB := MDL R_RSI 64 eq_refl).
    rewrite R12 in B1. rewrite RBP in B2. rewrite R13 in B3. rewrite RCX in NB. rewrite RSI in SB.
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply memccpy_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply MEMCHR; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (MC & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply memccpy_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M := mem [Ⓠ sp ⊖ 8 := r130] [Ⓠ sp ⊖ 16 := r120] [Ⓠ sp ⊖ 24 := rbp0] [Ⓠ sp ⊖ 32 := 1743823]) in *.
    assert (AGc: agree (fr sp) 32 M mem).
      repeat apply agree_frame8; try (clear; lia). apply agree_refl.
    assert (MCm: mchr mem src (c mod 2^8) n (s' R_RAX)).
    { eapply mchr_agree; [exact AGc | exact SRCF |].
      replace (c mod 2^8) with ((c mod 2^32) mod 2^8). exact MC.
      rewrite mp2_mod_mod_min. reflexivity. }
    assert (G1: M Ⓠ[sp ⊖ 8] = r130).
      unfold M. do 3 (rewrite getmem_noverlap by slot_nov).
      rewrite getmem_setmem by discriminate. apply N.mod_small. exact B3.
    assert (G2: M Ⓠ[sp ⊖ 16] = r120).
      unfold M. do 2 (rewrite getmem_noverlap by slot_nov).
      rewrite getmem_setmem by discriminate. apply N.mod_small. exact B1.
    assert (G3: M Ⓠ[sp ⊖ 24] = rbp0).
      unfold M. rewrite getmem_noverlap by slot_nov.
      rewrite getmem_setmem by discriminate. apply N.mod_small. exact B2.
    remember (s' R_RAX) as r eqn:RAXr. symmetry in RAXr.
    clearbody M.
    try rewrite RBX in RBXc. try rewrite R13 in R13c. try rewrite R14 in R14c. try rewrite R15 in R15c.
    try rewrite RBP in RBPc. try rewrite R12 in R12c.
    clear - RAXr RSPc MEMc RBXc RBPc R12c R13c R14c R15c MDL' AGc MCm G1 G2 G3 SPB SRC0 SRCW NB.
    repeat x64_step.
    + (* not found: on to the memcpy call *)
      apply N.eqb_eq in BC. subst r.
      assert (NO: forall i, i < n -> mem Ⓑ[src ⊕ i] <> c mod 2^8).
      { destruct MCm as [[_ NO]|[k [K [R _]]]]. exact NO.
        exfalso. symmetry in R. rewrite N.mod_small in R by lia. lia. }
      split. exact NO. split. reflexivity. split. reflexivity.
      split. rewrite RSPc, rsp_back. reflexivity.
      do 6 (split; [first [assumption | reflexivity]|]).
      rewrite MEMc. split. exact G1. split. exact G2. split. exact G3. exact AGc.
    + (* found at offset k: tail call mempcpy(dst, src, k+1) *)
      apply N.eqb_neq in BC.
      destruct MCm as [[R0 _]|[k [K [R [E NO]]]]]; [contradiction|].
      exists k. split. exact K. split. exact E. split. exact NO.
      split. reflexivity. split. reflexivity.
      split. subst r. apply msub_add_l. change (2^64) with 18446744073709551616. apply N.mod_lt. discriminate.
        rewrite !N.add_mod_idemp_r by discriminate. f_equal. lia.
      split. first [reflexivity | apply N.mod_small, SPB].
      split.
      * unfold saved. cbn [update iseq vareq]. try rewrite MEMc. rewrite G1, G2, G3.
        repeat split; assumption.
      * try rewrite MEMc. exact AGc.
  - (* not found: memcpy(dst, src, n), then return NULL *)
    destruct PRE as (NO & RSI & RDX & RSP & R13 & R12 & RBP & RBX & R14 & R15 & F1 & F2 & F3 & AG).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply memccpy_with_welltyped, WT. intro MDL1.
    eapply (perform_call 1). reflexivity.
    intros. eapply MEMCPY; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (CP & RSPc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply memccpy_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M1 := s V_MEM64 [Ⓠ sp ⊖ 32 := 1743870]) in *.
    assert (AG1: agree (fr sp) 32 M1 mem) by (apply agree_frame8; [clear; lia | exact AG]).
    assert (G1: s' V_MEM64 Ⓠ[sp ⊖ 8] = r130).
      rewrite (getmem8_copied M1 _ dst src n sp _ 8 CP DSTF) by (lia || reflexivity).
      unfold M1. rewrite getmem_noverlap by slot_nov. exact F1.
    assert (G2: s' V_MEM64 Ⓠ[sp ⊖ 16] = r120).
      rewrite (getmem8_copied M1 _ dst src n sp _ 16 CP DSTF) by (lia || reflexivity).
      unfold M1. rewrite getmem_noverlap by slot_nov. exact F2.
    assert (G3: s' V_MEM64 Ⓠ[sp ⊖ 24] = rbp0).
      rewrite (getmem8_copied M1 _ dst src n sp _ 24 CP DSTF) by (lia || reflexivity).
      unfold M1. rewrite getmem_noverlap by slot_nov. exact F3.
    assert (CPY: forall i, i < n -> s' V_MEM64 Ⓑ[dst ⊕ i] = mem Ⓑ[src ⊕ i]).
      intros i I. destruct CP as [CPin _]. rewrite (CPin i I). apply AG1, SRCF, I.
    assert (OUT: forall b, ~ msub 64 b dst < n -> ~ inwin (fr sp) 32 b -> s' V_MEM64 Ⓑ[b] = mem Ⓑ[b]).
      intros b B W. destruct CP as [_ CPout]. rewrite (CPout b B). apply AG1, W.
    clearbody M1.
    try rewrite RBX in RBXc. try rewrite R14 in R14c. try rewrite R15 in R15c.
    try rewrite R13 in R13c. try rewrite R12 in R12c. try rewrite RBP in RBPc.
    clear - RSPc RBXc RBPc R12c R13c R14c R15c MDL' G1 G2 G3 CPY OUT NO SPB.
    repeat x64_step.
    split. exact NO. split. reflexivity. split. first [reflexivity | apply N.mod_small, SPB].
    split.
    + unfold saved. cbn [update iseq vareq]. rewrite G1, G2, G3. repeat split; assumption.
    + split. exact CPY. exact OUT.
Time Qed.

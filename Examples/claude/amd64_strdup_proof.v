(* strdup -- duplicate a string

   SEMANTICS
   ---------
   strdup(s) computes n = strlen(s) and calls malloc(n+1).  If malloc returns
   NULL, strdup returns NULL.  Otherwise strdup TAIL-CALLS memcpy(d, s, n+1)
   (JMP to the memcpy PLT stub), so memcpy returns d directly to strdup's
   caller.  glibc's __strdup is a NON-LEAF function with three callees, all
   reached through the PLT:
     strlen (CALL 0x128490), malloc (CALL 0x128380), memcpy (JMP 0x128620).
   Their targets are not part of this program, so the proof places arbitrary
   code cp at every address outside strdup and assumes contracts for strlen
   and malloc.  The theorem ends at the jump into memcpy and states memcpy's
   arguments exactly: the destination block came from malloc(n+1), the source
   is s, and the length is n+1.  Any memcpy specification (for example
   amd64_memcpy_proof.v for small n) then gives the duplicated string.

   malloc changes heap memory.  The theorem is parameterized by an abstract
   heap region `heap`.  The malloc contract lets malloc change only heap
   bytes and requires it to return NULL or a block of the requested size
   inside the heap.  strdup's frame, its return address and the string s are
   assumed to lie outside the heap.

   SPECIFICATION (man 3 strdup, Linux man-pages, Ubuntu 22.04)
   ------------------------------------------------------------
     SYNOPSIS
            #include <string.h>

            char *strdup(const char *s);

     DESCRIPTION
            The  strdup() function returns a pointer to a new string which is a du-
            plicate of the string s.  Memory for the new string  is  obtained  with
            malloc(3), and can be freed with free(3).

     RETURN VALUE
            On  success,  the strdup() function returns a pointer to the duplicated
            string.  It returns NULL if insufficient memory was available, with er-
            rno set to indicate the cause of the error.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol strdup (__strdup) at 0x1a8570 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh (global addressing); see strdup_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSP = sp, memory m.  The frame is the 32 bytes below sp.
   Preconditions:  the string s (up to and including its NUL) lies outside the
            frame; the frame and the return address (the 40 bytes from sp-32)
            lie outside the heap; and cp meets the strlen and malloc contracts.
   Output:  For n = strlen(s), exactly one of two exits is reached:
              RET:  RAX = 0 (malloc returned NULL);
              JMP memcpy:  RDI = d <> 0 with [d, d+n+1) inside the heap,
                    RSI = s, RDX = n+1 (mod 2^64), RSP = sp (so memcpy returns
                    to strdup's caller).
            At either exit, RBX, RBP and R12-R15 have their entry values, and
            every byte outside the heap and the frame equals its value in m.
            (Partial correctness.)
   Callee model:  the strlen contract requires the callee to leave memory
            unchanged, and the malloc contract allows changes only inside the
            heap.  Real callees may also write below their own stack pointer,
            a region that is dead to strdup.
 *)

Require Import Picinae_amd64.
Require Import strdup_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring.
Import ListNotations.
Open Scope N.

Theorem strdup_nwc: forall s2 s1, strdup_amd64 s1 = strdup_amd64 s2.
Proof. reflexivity. Qed.

Theorem strdup_welltyped: welltyped_prog x64typctx strdup_amd64.
Proof. Picinae_typecheck. Qed.

Definition P_STRLEN := 0x128490.
Definition P_MALLOC := 0x128380.
Definition P_MEMCPY := 0x128620.
Definition RET_STRLEN := 0x1a8583.
Definition RET_MALLOC := 0x1a858f.

Definition strdup_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match strdup_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma strdup_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (strdup_with cp).
Proof.
  intros cp WT s a. unfold strdup_with.
  pose proof (strdup_welltyped s a) as H.
  destruct (strdup_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

Definition fr (sp:N) := sp ⊖ 32.

Section Invariants.
  Variable heap : N -> Prop.
  Variable sp : N.
  Variable mem : memory.
  Variable p : N.
  Variable rbx rbp r12 r13 r14 r15 : N.

  Definition saved (s:store) :=
    s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
    s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.

  (* Every byte outside the heap and the frame is unchanged. *)
  Definition unchanged_outside (M:memory) :=
    forall a, ~ heap a -> ~ inwin (fr sp) 32 a -> M Ⓑ[a] = mem Ⓑ[a].

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strlen (subroutine 0) *)
    | 0x128490 => Inv 0 (s R_RDI = p /\ s R_RSP = sp /\ s V_MEM64 = mem /\
                         mem Ⓠ[sp] = RET_STRLEN /\ saved s)
    | 0x1a8583 => Post 0 (slen mem p (s R_RAX) /\ s R_RSP = sp ⊕ 8 /\ s V_MEM64 = mem /\ saved s)
    (* malloc (subroutine 1); p is the requested size *)
    | 0x128380 => Inv 1 (s R_RDI = p /\ s R_RSP = sp /\ s V_MEM64 = mem /\
                         mem Ⓠ[sp] = RET_MALLOC /\ saved s)
    | 0x1a858f => Post 1 (s R_RSP = sp ⊕ 8 /\ saved s /\
                          (forall a, ~ heap a -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]) /\
                          (s R_RAX = 0 \/ forall i, i < p -> heap (s R_RAX ⊕ i)))
    (* strdup (subroutine 2) *)
    | 0x1a8570 => Inv 2 (s R_RSP = sp /\ s V_MEM64 = mem /\ s R_RDI = p /\ saved s)
    | 0x1a8587 => Inv 2 (exists n, slen mem p n /\
                         s R_RSP = sp ⊖ 24 /\ s R_R12 = n ⊕ 1 /\ s R_RBP = p /\
                         s R_RBX = rbx /\ s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                         s V_MEM64 Ⓠ[sp ⊖ 8] = r12 /\ s V_MEM64 Ⓠ[sp ⊖ 16] = rbp /\
                         agree (fr sp) 32 (s V_MEM64) mem)
    | 0x1a85af => Post 2 (s R_RSP = sp /\ s R_RAX = 0 /\ saved s /\ unchanged_outside (s V_MEM64))
    | 0x128620 => Post 2 (exists n, slen mem p n /\
                          s R_RDI <> 0 /\ (forall i, i < n ⊕ 1 -> heap (s R_RDI ⊕ i)) /\
                          s R_RSI = p /\ s R_RDX = n ⊕ 1 /\ s R_RSP = sp /\
                          saved s /\ unchanged_outside (s V_MEM64))
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (strdup_with cp) invs.
  Definition invs0 cp := make_invs 0 (strdup_with cp) invs.
  Definition exits1 cp := make_exits 1 (strdup_with cp) invs.
  Definition invs1 cp := make_invs 1 (strdup_with cp) invs.
  Definition exits2 cp := make_exits 2 (strdup_with cp) invs.
  Definition invs2 cp := make_invs 2 (strdup_with cp) invs.
End Invariants.

(* Callee contracts.  Every conjunct of each entry invariant is a
   hypothesis, so the contracts do not force the entry check to fail. *)
Definition strlen_contract (cp: store -> addr -> N * stmt) (heap: N -> Prop) :=
  forall s t xs' sp mem str rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_STRLEN, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = str ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_STRLEN ->
  satisfies_all (strdup_with cp)
    (invs0 heap sp mem str rbx rbp r12 r13 r14 r15 cp)
    (exits0 heap sp mem str rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Definition malloc_contract (cp: store -> addr -> N * stmt) (heap: N -> Prop) :=
  forall s t xs' sp mem size rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_MALLOC, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = size ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_MALLOC ->
  satisfies_all (strdup_with cp)
    (invs1 heap sp mem size rbx rbp r12 r13 r14 r15 cp)
    (exits1 heap sp mem size rbx rbp r12 r13 r14 r15 cp) (xs'::t).

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

Theorem strdup_correct:
  forall cp heap s t xs' sp mem str
         (WT: welltyped_code cp) (STRLEN: strlen_contract cp heap) (MALLOC: malloc_contract cp heap)
         (ENTRY: startof t xs' = (Addr 0x1a8570, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem) (RDI: s R_RDI = str)
         (SPB: sp < 2^64)
         (SFS: strfree (fr sp) 32 mem str)
         (HF: forall a, msub 64 a (fr sp) < 40 -> ~ heap a),
  satisfies_all (strdup_with cp)
    (invs2 heap sp mem str (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits2 heap sp mem str (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strdup_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT STRLEN MALLOC SPB SFS HF. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  - (* entry: call strlen *)
    destruct PRE as (RSP & MEM & RDI & RBX & RBP & R12 & R13 & R14 & R15).
    assert (B1 := MDL R_R12 64 eq_refl). assert (B2 := MDL R_RBP 64 eq_refl).
    rewrite R12 in B1. rewrite RBP in B2.
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply strdup_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply STRLEN; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (SL & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply strdup_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M := mem [Ⓠ sp ⊖ 8 := r120] [Ⓠ sp ⊖ 16 := rbp0] [Ⓠ sp ⊖ 32 := 1738115]) in *.
    assert (AGc: agree (fr sp) 32 M mem).
      repeat apply agree_frame8; try (clear; lia). apply agree_refl.
    assert (SLm: slen mem str (s' R_RAX)) by (eapply slen_agree; eassumption).
    assert (G1: M Ⓠ[sp ⊖ 8] = r120).
      unfold M. rewrite getmem_noverlap by slot_nov. rewrite getmem_noverlap by slot_nov.
      rewrite getmem_setmem by discriminate. apply N.mod_small. exact B1.
    assert (G2: M Ⓠ[sp ⊖ 16] = rbp0).
      unfold M. rewrite getmem_noverlap by slot_nov. rewrite getmem_setmem by discriminate.
      apply N.mod_small. exact B2.
    remember (s' R_RAX) as n eqn:RAXn. symmetry in RAXn.
    clearbody M.
    try rewrite RBX in RBXc. try rewrite R13 in R13c. try rewrite R14 in R14c. try rewrite R15 in R15c.
    clear - RAXn RSPc MEMc RBXc RBPc R12c R13c R14c R15c MDL' AGc SLm G1 G2.
    repeat x64_step.
    exists n. split. exact SLm. split. rewrite RSPc, rsp_back. reflexivity.
    split. f_equal. apply N.add_comm.
    do 5 (split; [assumption|]).
    rewrite MEMc. split. exact G1. split. exact G2. exact AGc.
  - (* 0x1a8587: call malloc *)
    destruct PRE as (n & SL & RSP & R12 & RBP & RBX & R13 & R14 & R15 & F1 & F2 & AG).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply strdup_with_welltyped, WT. intro MDL1.
    eapply (perform_call 1). reflexivity.
    intros. eapply MALLOC; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (RSPc & (RBXc & RBPc & R12c & R13c & R14c & R15c) & HM & RES).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply strdup_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M := s V_MEM64 [Ⓠ sp ⊖ 32 := 1738127]) in *.
    assert (AGc: agree (fr sp) 32 M mem) by (apply agree_frame8; [clear; lia | exact AG]).
    assert (G1: s' V_MEM64 Ⓠ[sp ⊖ 8] = r120).
      rewrite (getmem8_agree _ M).
        unfold M. rewrite getmem_noverlap by slot_nov. exact F1.
      intros a' A. apply HM, HF. eapply slot_in40; [|exact A]. clear; lia.
    assert (G2: s' V_MEM64 Ⓠ[sp ⊖ 16] = rbp0).
      rewrite (getmem8_agree _ M).
        unfold M. rewrite getmem_noverlap by slot_nov. exact F2.
      intros a' A. apply HM, HF. eapply slot_in40; [|exact A]. clear; lia.
    assert (OUT: unchanged_outside heap sp mem (s' V_MEM64)).
      intros a NH NW. rewrite (HM a NH). apply AGc, NW.
    clearbody M.
    try rewrite RBX in RBXc. try rewrite R13 in R13c. try rewrite R14 in R14c. try rewrite R15 in R15c.
    try rewrite RBP in RBPc. try rewrite R12 in R12c.
    clear - RSPc RBXc RBPc R12c R13c R14c R15c RES MDL' G1 G2 OUT SL SPB.
    repeat x64_step.
    + (* malloc returned NULL *)
      split. first [reflexivity | apply N.mod_small, SPB]. split. reflexivity.
      split; [|exact OUT].
      unfold saved. cbn [update iseq vareq]. rewrite G1, G2.
      repeat split; assumption.
    + (* tail call memcpy(d, s, n+1) *)
      apply N.eqb_neq in BC. destruct RES as [R0|HB]; [contradiction|].
      rewrite (N.add_comm 1 n) in HB.
      exists n. split. exact SL. split. exact BC. split. exact HB.
      split. reflexivity. split. f_equal. apply N.add_comm.
      split. first [reflexivity | apply N.mod_small, SPB].
      split; [|exact OUT].
      unfold saved. cbn [update iseq vareq]. rewrite G1, G2.
      repeat split; assumption.
Time Qed.

(* Non-vacuity: the two callee contracts are not contradictory, even
   together and for any heap.  The witness's malloc returns NULL at once
   (RAX := 0; RET), which meets the malloc contract outright.  Its strlen
   spins forever, which is weaker evidence but rules out a contract that is
   false for every cp. *)
Definition ret0 : stmt :=
  Move R_RAX (Word 0 64) $;
  Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
  Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
  Jmp (Var R_RIP).
Definition cp0 (_:store) (a:addr) : N * stmt :=
  if a =? P_MALLOC then (1, ret0) else (1, Jmp (Word P_STRLEN 64)).

Lemma cp0_welltyped: welltyped_code cp0.
Proof.
  intros s a. unfold cp0. destruct (a =? P_MALLOC); apply typchk_stmt_compute; vm_compute; exact I.
Qed.

Theorem strdup_contracts_satisfiable:
  forall heap, exists cp, welltyped_code cp /\ strlen_contract cp heap /\ malloc_contract cp heap.
Proof.
  intro heap. exists cp0. split. exact cp0_welltyped. split.
  all: intros s t xs' sp mem a0 rbx rbp r12 r13 r14 r15 ENTRY MDL RSP MEM RDI [RBX [RBP [R12 [R13 [R14 R15]]]]] RET; apply prove_invs;
       [ simpl; rewrite ENTRY; x64_step; repeat split; assumption |].
  all: intros; erewrite startof_prefix in ENTRY; try eassumption;
       eapply models_at_invariant; try eassumption;
       [ apply strdup_with_welltyped, cp0_welltyped |].
  all: intro MDL1; clear - PRE MDL1; rename t1 into t; destruct_inv 64 PRE.
  all: destruct PRE as (RDI & RSP & MEM & RET & RBX & RBP & R12 & R13 & R14 & R15).
  - x64_step. repeat split; assumption.
  - x64_step. rewrite RET. unfold RET_MALLOC. x64_step.
    split. reflexivity. split. repeat split; assumption.
    split. intros a _. reflexivity. left. reflexivity.
Qed.

(* strsep -- extract a token from a string

   SEMANTICS
   ---------
   strsep(stringp, delim) reads s = *stringp.  If s is NULL it returns NULL.
   Otherwise it finds n = strcspn(s, delim), the length of the first token.
   If s[n] is a delimiter, strsep overwrites it with NUL and sets *stringp to
   s+n+1.  If s[n] is the terminator, it sets *stringp to NULL.  Either way it
   returns s.  glibc's strsep (__strsep_g) is a NON-LEAF function: it calls
   strcspn through the PLT (CALL 0x128570), whose IFUNC-selected target is not
   part of this program.  The proof therefore places arbitrary code cp at every
   address outside strsep and assumes only a contract for the code entered at
   the PLT stub P: it returns strcspn(s, delim) in RAX, as perform_call
   consumes it (see strsep_cspn_contract).

   SPECIFICATION (man 3 strsep, Linux man-pages, Ubuntu 22.04)
   ------------------------------------------------------------
     SYNOPSIS
            #include <string.h>

            char *strsep(char **stringp, const char *delim);

     DESCRIPTION
            If  *stringp is NULL, the strsep() function returns NULL and does noth-
            ing else.  Otherwise, this function finds the first token in the string
            *stringp,  that  is  delimited by one of the bytes in the string delim.
            This token is terminated by overwriting the delimiter with a null  byte
            ('\0'),  and  *stringp  is updated to point past the token.  In case no
            delimiter was found, the  token  is  taken  to  be  the  entire  string
            *stringp, and *stringp is made NULL.

     RETURN VALUE
            The  strsep()  function returns a pointer to the token, that is, it re-
            turns the original value of *stringp.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol strsep (__strsep_g) at 0x1a9d40 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh (global addressing); see strsep_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = stringp, RSI = delim, RSP = sp, memory m; s = m[stringp] (8 bytes).
            The frame is the 32 bytes below sp (two saved registers, padding,
            and the return address of the strcspn call).
   Preconditions:  *stringp (8 bytes) lies outside the frame; if s <> NULL, the
            strings s and delim (up to and including their NULs) lie outside
            the frame; and cp meets strsep_cspn_contract.
   Output:  On return, RSP = sp, RBX, RBP and R12-R15 have their entry values,
            and, writing M' for the final memory and "=f" for "equal at every
            byte outside the frame":
              s = NULL:  RAX = 0 and M' =f m;
              s <> NULL: RAX = s, and for n = strcspn(s, delim) (as computed
                         on m):
                           s[n] = NUL:  M' =f m with *stringp := NULL;
                           s[n] <> NUL: M' =f m with s[n] := NUL and then
                                        *stringp := s+n+1.
            (Partial correctness.)
   Callee model:  the strcspn contract also requires the callee to leave
            memory unchanged.  Real code may scribble below its own stack
            pointer; that region is dead to strsep.
 *)

Require Import Picinae_amd64.
Require Import strsep_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring.
Import ListNotations.
Open Scope N.

Theorem strsep_nwc: forall s2 s1, strsep_amd64 s1 = strsep_amd64 s2.
Proof. reflexivity. Qed.

Theorem strsep_welltyped: welltyped_prog x64typctx strsep_amd64.
Proof. Picinae_typecheck. Qed.

Definition P := 0x128570.         (* PLT stub for strcspn *)
Definition RET_SITE := 0x1a9d5e.  (* return address of the CALL *)

Definition strsep_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match strsep_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma strsep_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (strsep_with cp).
Proof.
  intros cp WT s a. unfold strsep_with.
  pose proof (strsep_welltyped s a) as H.
  destruct (strsep_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

(* The frame window: the 32 bytes below the entry sp. *)
Definition fr (sp:N) := sp ⊖ 32.

Definition strsep_ok (sp:N) (m:memory) (stringp delim r:N) (M:memory) :=
  let s := m Ⓠ[stringp] in
  (s = 0 /\ r = 0 /\ agree (fr sp) 32 M m) \/
  (s <> 0 /\ r = s /\ exists n, cspn m s delim n /\
     ((m Ⓑ[s ⊕ n] = 0 /\ agree (fr sp) 32 M (m [Ⓠ stringp := 0])) \/
      (m Ⓑ[s ⊕ n] <> 0 /\ agree (fr sp) 32 M (m [Ⓑ s ⊕ n := 0] [Ⓠ stringp := s ⊕ n ⊕ 1])))).

Section Invariants.
  Variable sp : N.
  Variable mem : memory.
  Variable p d : N.
  Variable rbx rbp r12 r13 r14 r15 : N.

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* strcspn (subroutine 0): entry at P, returns to RET_SITE *)
    | 0x128570 => Inv 0 (s R_RDI = p /\ s R_RSI = d /\ s R_RSP = sp /\
                         s V_MEM64 = mem /\ mem Ⓠ[sp] = RET_SITE /\
                         s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                         s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    | 0x1a9d5e => Post 0 (cspn mem p d (s R_RAX) /\ s R_RSP = sp ⊕ 8 /\ s V_MEM64 = mem /\
                          s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                          s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    (* strsep (subroutine 1) *)
    | 0x1a9d40 => Inv 1 (s R_RSP = sp /\ s V_MEM64 = mem /\ s R_RDI = p /\ s R_RSI = d /\
                         s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                         s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15)
    | 0x1a9d53 => Inv 1 (s R_RSP = sp ⊖ 24 /\ s R_RDI = p /\ s R_RSI = d /\
                         s R_R12 = mem Ⓠ[p] /\ mem Ⓠ[p] <> 0 /\
                         s R_RBX = rbx /\ s R_RBP = rbp /\
                         s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                         s V_MEM64 Ⓠ[sp ⊖ 16] = rbx /\ s V_MEM64 Ⓠ[sp ⊖ 8] = r12 /\
                         agree (fr sp) 32 (s V_MEM64) mem)
    | 0x1a9d7a | 0x1a9d91 =>
        Post 1 (s R_RSP = sp /\
                s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
                s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15 /\
                strsep_ok sp mem p d (s R_RAX) (s V_MEM64))
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (strsep_with cp) invs.
  Definition invs0 cp := make_invs 0 (strsep_with cp) invs.
  Definition exits1 cp := make_exits 1 (strsep_with cp) invs.
  Definition invs1 cp := make_invs 1 (strsep_with cp) invs.
End Invariants.

(* What the code at P must do: compute strcspn without touching memory or the
   callee-saved registers.  Every conjunct of the entry invariant (Inv 0) is a
   hypothesis here, so the contract does not force the entry check to fail. *)
Definition strsep_cspn_contract (cp: store -> addr -> N * stmt) :=
  forall s t xs' sp mem str d rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P, s) -> models x64typctx s ->
  s R_RSP = sp -> s V_MEM64 = mem -> s R_RDI = str -> s R_RSI = d ->
  s R_RBX = rbx -> s R_RBP = rbp -> s R_R12 = r12 -> s R_R13 = r13 ->
  s R_R14 = r14 -> s R_R15 = r15 -> mem Ⓠ[sp] = RET_SITE ->
  satisfies_all (strsep_with cp)
    (invs0 sp mem str d rbx rbp r12 r13 r14 r15 cp)
    (exits0 sp mem str d rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Lemma frame_nov:
  forall a sp x, sp < 2^64 -> 8 <= x <= 32 -> ~ overlap 64 a 8 (fr sp) 32 -> ~ overlap 64 a 8 (sp ⊖ x) 8.
Proof.
  intros a sp x SPB X NO [i [j [I [J E]]]]. apply NO. exists i, (32 - x + j).
  split; [exact I|]. split; [lia|]. rewrite E. unfold fr, msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma byte_frame_nov:
  forall a sp x, sp < 2^64 -> 8 <= x <= 32 -> ~ inwin (fr sp) 32 a -> ~ overlap 64 a 1 (sp ⊖ x) 8.
Proof.
  intros a sp x SPB X NI [i [j [I [J E]]]]. apply NI. unfold inwin, fr, msub in *.
  change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma agree_frame8:
  forall sp x M m v, sp < 2^64 -> 8 <= x <= 32 -> agree (fr sp) 32 M m ->
  agree (fr sp) 32 (M [Ⓠ sp ⊖ x := v]) m.
Proof.
  intros. apply agree_setwin; try assumption; try (change (2^64) with 18446744073709551616; lia).
  unfold fr, msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Ltac slot_nov :=
  intros [i [j [I [J E]]]]; unfold msub in E; change (2^64) with 18446744073709551616 in *; lia.

Theorem strsep_correct:
  forall cp s t xs' sp mem stringp delim
         (WT: welltyped_code cp) (CSPN: strsep_cspn_contract cp)
         (ENTRY: startof t xs' = (Addr 0x1a9d40, s))
         (MDL: models x64typctx s)
         (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem)
         (RDI: s R_RDI = stringp) (RSI: s R_RSI = delim)
         (SPB: sp < 2^64)
         (NOV: ~ overlap 64 stringp 8 (fr sp) 32)
         (SFS: mem Ⓠ[stringp] <> 0 -> strfree (fr sp) 32 mem (mem Ⓠ[stringp]))
         (SFD: mem Ⓠ[stringp] <> 0 -> strfree (fr sp) 32 mem delim),
  satisfies_all (strsep_with cp)
    (invs1 sp mem stringp delim (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits1 sp mem stringp delim (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strsep_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT CSPN SPB NOV SFS SFD. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  - destruct PRE as (RSP & MEM & RDI & RSI & RBX & RBP & R12 & R13 & R14 & R15).
    assert (RD: (mem [Ⓠ sp ⊖ 8 := r120] [Ⓠ sp ⊖ 16 := rbx0]) Ⓠ[stringp] = mem Ⓠ[stringp]).
      rewrite !getmem_noverlap by (apply frame_nov; (assumption || lia)). reflexivity.
    assert (AG: agree (fr sp) 32 (mem [Ⓠ sp ⊖ 8 := r120] [Ⓠ sp ⊖ 16 := rbx0]) mem).
      repeat apply agree_frame8; try (assumption || lia). apply agree_refl.
    repeat x64_step; rewrite RD in *.
    + (* *stringp = NULL *)
      apply N.eqb_eq in BC.
      do 7 (split; [(reflexivity || assumption)|]).
      left. split. exact BC. split. exact BC. exact AG.
    + apply N.eqb_neq in BC.
      do 10 (split; [(reflexivity || assumption)|]).
      split. reflexivity. split. reflexivity. exact AG.
  - destruct PRE as (RSP & RDI & RSI & R12 & NZ & RBX & RBP & R13 & R14 & R15 & F1 & F2 & AG).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply strsep_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply CSPN; try (eassumption || reflexivity).
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (CS & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply strsep_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M := s V_MEM64 [Ⓠ sp ⊖ 32 := 1744222]) in *.
    assert (AGc: agree (fr sp) 32 M mem) by (apply agree_frame8; (assumption || lia)).
    pose proof (SFS NZ) as SS. pose proof (SFD NZ) as SD.
    assert (CSm: cspn mem (mem Ⓠ[stringp]) delim (s' R_RAX)) by (eapply cspn_agree; eassumption).
    assert (NIW := cspn_end_free _ _ _ _ _ _ SS CSm).
    assert (BYTE: M Ⓑ[mem Ⓠ[stringp] ⊕ s' R_RAX] = mem Ⓑ[mem Ⓠ[stringp] ⊕ s' R_RAX]) by (apply AGc, NIW).
    assert (G1: M Ⓠ[sp ⊖ 16] = rbx0).
      unfold M. rewrite getmem_noverlap by slot_nov. exact F1.
    assert (G2: M Ⓠ[sp ⊖ 8] = r120).
      unfold M. rewrite getmem_noverlap by slot_nov. exact F2.
    remember (s' R_RAX) as n eqn:RAXn. symmetry in RAXn.
    remember (mem Ⓠ[stringp]) as s0 eqn:S0. 
    clearbody M.
    clear - RAXn RSPc MEMc RBXc RBPc R12c R13c R14c R15c MDL' AGc CSm NIW BYTE G1 G2 NZ SPB NOV S0.
    rename s' into s. rename MDL' into MDL. rename t' into t.
    repeat x64_step.
    all: unfold strsep_ok; cbv zeta; rewrite <- S0.
    all: rewrite (N.add_comm n s0), <- (getmem_mod_l _ _ _ M (s0+n)), BYTE in BC.
    all: split; [reflexivity|].
    + (* s[n] is the terminator: *stringp := NULL *)
      apply N.eqb_eq in BC.
      split. rewrite getmem_noverlap by (apply noverlap_sym, frame_nov; (assumption || lia)). exact G1.
      split. assumption.
      split. rewrite getmem_noverlap by (apply noverlap_sym, frame_nov; (assumption || lia)). exact G2.
      do 3 (split; [assumption|]).
      right. split. exact NZ. split. reflexivity. exists n. split. exact CSm.
      left. split. exact BC.
      apply agree_set; try (change (2^64) with 18446744073709551616; lia). exact AGc.
    + (* s[n] is a delimiter: s[n] := NUL, *stringp := s+n+1 *)
      apply N.eqb_neq in BC.
      assert (A: forall X v, X [Ⓑ n + s0 := v] = X [Ⓑ s0 ⊕ n := v])
        by (intros; rewrite setmem_mod_l, N.add_comm; reflexivity).
      assert (W: forall X, X [Ⓠ stringp := 1 + n + s0] = X [Ⓠ stringp := s0 ⊕ n ⊕ 1]).
        intro X. rewrite <- (setmem_mod_r _ _ _ X _ (1 + n + s0)), <- (setmem_mod_r _ _ _ X _ (s0 ⊕ n ⊕ 1)).
        f_equal. change (8*8) with 64. rewrite N.mod_mod, N.add_mod_idemp_l by discriminate.
        f_equal. lia.
      rewrite A, W.
      split. rewrite !getmem_noverlap
               by (apply noverlap_sym; first [apply frame_nov | apply byte_frame_nov]; (assumption || lia)).
             exact G1.
      split. assumption.
      split. rewrite !getmem_noverlap
               by (apply noverlap_sym; first [apply frame_nov | apply byte_frame_nov]; (assumption || lia)).
             exact G2.
      do 3 (split; [assumption|]).
      right. split. exact NZ. split. reflexivity. exists n. split. exact CSm.
      right. split. exact BC.
      apply agree_set; try (change (2^64) with 18446744073709551616; lia).
      apply agree_set; try (change (2^64) with 18446744073709551616; lia). exact AGc.
Time Qed.

(* Non-vacuity: the strcspn contract is not contradictory.  The witness is
   a callee that spins at P forever (Jmp P).  This is weaker evidence than a
   terminating strcspn implementation, but it rules out the failure mode where
   the contract is false for every cp, which would make strsep_correct hold
   trivially. *)
Definition cp_spin (_:store) (_:addr) : N * stmt := (1, Jmp (Word P 64)).

Theorem strsep_cspn_contract_satisfiable:
  exists cp, welltyped_code cp /\ strsep_cspn_contract cp.
Proof.
  exists cp_spin. split.
    intros s a. apply typchk_stmt_compute; vm_compute; exact I.
  intros s t xs' sp mem str d rbx rbp r12 r13 r14 r15
    ENTRY MDL RSP MEM RDI RSI RBX RBP R12 R13 R14 R15 RET. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption.
    apply strsep_with_welltyped. intros s0 a0. apply typchk_stmt_compute; vm_compute; exact I.
  intro MDL1. clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (RDI & RSI & RSP & MEM & RET & RBX & RBP & R12 & R13 & R14 & R15).
  x64_step. repeat split; assumption.
Qed.

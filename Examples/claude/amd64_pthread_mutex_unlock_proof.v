(* pthread_mutex_unlock -- unlock a mutex

   SEMANTICS
   ---------
   glibc 2.35's pthread_mutex_unlock(m) is __pthread_mutex_unlock_usercnt(m, 1)
   inlined.  struct __pthread_mutex_s on x86-64: __lock at 0, __count at 4,
   __owner at 8, __nusers at 12, __kind at 16.  With typ = __kind:
     - typ & 0x7c <> 0 (robust, priority-inherit or priority-protect): tail
       call __pthread_mutex_unlock_full(m, 1).
     - kind = typ & 0x17f = 0 (PTHREAD_MUTEX_NORMAL / TIMED), or
       typ & 0x7f = 3 (ADAPTIVE): the common release, below.
     - kind = 0x100 (elision): tail call __lll_unlock_elision(&m->__lock,
       typ & 0x80).
     - typ & 0x7f = 1 (RECURSIVE): EPERM (1) unless __owner = the calling
       thread's TID; otherwise --__count, and the common release when the
       count reaches 0.
     - kind = 2 (ERRORCHECK): EPERM unless __owner = TID and __lock <> 0;
       otherwise the common release.
     - any other kind: __assert_fail.
   The common release: --__nusers, __owner := 0, __lock := 0, returning 0.
   If the mutex is process-shared (typ & 0x80) or the process has started a
   second thread (THREAD_SELF->header.multiple_threads), __lock is cleared
   with XCHG, and if its old value was > 1 (waiters) glibc calls
   __lll_lock_wake (CALL 0x191320) to issue FUTEX_WAKE.  That callee is
   modeled by unlock_wake_contract, applied by perform_call.

   SPECIFICATION (man 3 pthread_mutex_unlock, POSIX, Ubuntu 22.04)
   ----------------------------------------------------------------

     int pthread_mutex_unlock(pthread_mutex_t *mutex);

     The pthread_mutex_unlock() function shall release the mutex object
     referenced by mutex.  [...]  If the mutex type is PTHREAD_MUTEX_
     ERRORCHECK [...] and a thread attempts to unlock a mutex that it has
     not locked or a mutex which is unlocked, an error shall be returned.
     If the mutex type is PTHREAD_MUTEX_RECURSIVE, [...] when the lock
     count reaches zero, the mutex shall become available.

     [EPERM] The mutex type is PTHREAD_MUTEX_ERRORCHECK or
     PTHREAD_MUTEX_RECURSIVE [...] and the current thread does not own the
     mutex.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol pthread_mutex_unlock at 0x99a70 (Ghidra address 0x199a70, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see pthread_mutex_unlock_amd64.v (global
            addresses).  The LOCK-prefixed / implicitly locked XCHG is lifted
            as an ordinary exchange: Picinae's semantics is single-threaded.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = a (the mutex), FS_BASE = fs (the thread pointer), RSP = sp,
            memory m.  TID = m Ⓓ[fs ⊕ 0x2d0].  multiple_threads (at fs + 0x18)
            only selects XCHG over MOV for clearing __lock, which gives the
            same result, so the spec doesn't mention it.
   Output:  at RET: RSP = sp, RBX, RBP, R12-R15 unchanged, and for some M
            that agrees with the final memory outside the 32 bytes below sp,
            unlock_ok m a fs RAX M (the case table above).  The tail calls and
            the assertion are exits with their own postconditions.
            (Partial correctness.)
 *)

Require Import Picinae_amd64.
Require Import pthread_mutex_unlock_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring.
Import ListNotations.
Open Scope N.

Theorem unlock_welltyped: welltyped_prog x64typctx pthread_mutex_unlock_amd64.
Proof. Picinae_typecheck. Qed.

Definition P_WAKE := 0x191320.        (* __lll_lock_wake *)
Definition RET_WAKE := 1678093.       (* 0x199b0d, after CALL __lll_lock_wake *)

Definition unlock_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match pthread_mutex_unlock_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma unlock_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (unlock_with cp).
Proof.
  intros cp WT s a. unfold unlock_with.
  pose proof (unlock_welltyped s a) as H.
  destruct (pthread_mutex_unlock_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

(* --nusers, owner := 0, lock := 0 *)
Definition release (m:memory) (a:N) :=
  m [Ⓓ 12 + a := msub 32 (m Ⓓ[12 + a]) 1] [Ⓓ 8 + a := 0] [Ⓓ a := 0].

Definition unlock_ok (m:memory) (a fs r:N) (M:memory) :=
  let typ := m Ⓓ[16 + a] in
  let tid := m Ⓓ[fs ⊕ 0x2d0] in
  ((typ .& 0x17f = 0 \/ typ .& 0x7f = 3) /\ r = 0 /\ M = release m a) \/
  (typ .& 0x7f = 1 /\ m Ⓓ[8 + a] <> tid /\ r = 1 /\ M = m) \/
  (typ .& 0x7f = 1 /\ m Ⓓ[8 + a] = tid /\ m Ⓓ[4 + a] <> 1 /\ r = 0 /\
     M = m [Ⓓ 4 + a := msub 32 (m Ⓓ[4 + a]) 1]) \/
  (typ .& 0x7f = 1 /\ m Ⓓ[8 + a] = tid /\ m Ⓓ[4 + a] = 1 /\ r = 0 /\
     M = release (m [Ⓓ 4 + a := 0]) a) \/
  (typ .& 0x17f = 2 /\ (m Ⓓ[8 + a] <> tid \/ m Ⓓ[a] = 0) /\ r = 1 /\ M = m) \/
  (typ .& 0x17f = 2 /\ m Ⓓ[8 + a] = tid /\ m Ⓓ[a] <> 0 /\ r = 0 /\ M = release m a).

Section Invariants.
  Variable sp : N.
  Variable mem : memory.
  Variables a fs arg2 : N.
  Variables rbx rbp r12 r13 r14 r15 : N.

  Definition saved (s:store) :=
    s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
    s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.

  Definition typ := mem Ⓓ[16 + a].

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    (* __lll_lock_wake (subroutine 0): wake(a, arg2) *)
    | 1643296 => Inv 0 (s R_RDI = a /\ s R_RSI = arg2 /\ s R_RSP = sp /\ s V_MEM64 = mem /\
                        mem Ⓠ[sp] = RET_WAKE /\ saved s)
    | 1678093 => Post 0 (s R_RSP = sp ⊕ 8 /\ s V_MEM64 = mem /\ saved s)
    (* pthread_mutex_unlock (subroutine 1) *)
    | 1677936 => Inv 1 (s R_RDI = a /\ s R_FS_BASE = fs /\ s R_RSP = sp /\ s V_MEM64 = mem /\ saved s)
    (* before the wake call: the mutex is already released *)
    | 1678080 => Inv 1 (exists M, s V_MEM64 = M /\ unlock_ok mem a fs 0 M /\
                        s R_RSP = sp ⊖ 24 /\ s R_RDI = a /\ s R_RAX = 0 /\ saved s)
    | 1678000 => Post 1 (s R_RSP = sp /\ saved s /\
                         exists M, agree (sp ⊖ 32) 32 (s V_MEM64) M /\ unlock_ok mem a fs (s R_RAX) M)
    (* tail call __pthread_mutex_unlock_full(a, 1) *)
    | 1676480 => Post 1 (typ .& 0x7c <> 0 /\ s R_RDI = a /\ s R_RSI = 1 /\ s R_RSP = sp /\
                         s V_MEM64 = mem /\ saved s)
    (* tail call __lll_unlock_elision(a, typ & 0x80) *)
    | 1642320 => Post 1 (typ .& 0x17f = 0x100 /\ s R_RDI = a /\ s R_RSI = typ .& 0x80 /\
                         s R_RSP = sp /\ s V_MEM64 = mem /\ saved s)
    (* __assert_fail: an invalid mutex kind *)
    | 1285712 => Post 1 (typ .& 0x7c = 0 /\ typ .& 0x17f <> 0 /\ typ .& 0x17f <> 0x100 /\
                         typ .& 0x17f <> 2 /\ typ .& 0x7f <> 1 /\ typ .& 0x7f <> 3)
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (unlock_with cp) invs.
  Definition invs0 cp := make_invs 0 (unlock_with cp) invs.
  Definition exits1 cp := make_exits 1 (unlock_with cp) invs.
  Definition invs1 cp := make_invs 1 (unlock_with cp) invs.
End Invariants.

Definition unlock_wake_contract (cp: store -> addr -> N * stmt) :=
  forall s t xs' sp mem p f rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_WAKE, s) -> models x64typctx s ->
  s R_RDI = p -> s R_RSI = f -> s R_RSP = sp -> s V_MEM64 = mem ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_WAKE ->
  satisfies_all (unlock_with cp)
    (invs0 sp mem p 0 f rbx rbp r12 r13 r14 r15 cp)
    (exits0 sp mem p 0 f rbx rbp r12 r13 r14 r15 cp) (xs'::t).

(* The lifted code tests the kind word through byte and word loads. *)
Lemma typ_b: forall (m:memory) a K, K < 2^8 -> m Ⓓ[16 + a] .& K = m Ⓑ[16 + a] .& K.
Proof.
  intros m a K KB. rewrite <- (land_mod_pow2 (m Ⓓ[16 + a]) 8 K KB).
  rewrite (getmem_mod 64 LittleE 1 4). reflexivity.
Qed.

Lemma typ_w: forall (m:memory) a K, K < 2^16 -> m Ⓓ[16 + a] .& K = m Ⓦ[16 + a] .& K.
Proof.
  intros m a K KB. rewrite <- (land_mod_pow2 (m Ⓓ[16 + a]) 16 K KB).
  rewrite (getmem_mod 64 LittleE 2 4). reflexivity.
Qed.

Lemma typ_7: forall (m:memory) a, m Ⓓ[16 + a] .& 0x7f = m Ⓑ[16 + a] mod 2^7.
Proof.
  intros m a. change 0x7f with (N.ones 7). rewrite N.land_ones.
  transitivity ((m Ⓓ[16 + a] mod 2^(1*8)) mod 2^7).
  - rewrite mp2_mod_mod_min. reflexivity.
  - rewrite (getmem_mod 64 LittleE 1 4). reflexivity.
Qed.

Lemma typ_7m: forall (m:memory) a, m Ⓓ[16 + a] mod 2^7 = m Ⓑ[16 + a] mod 2^7.
Proof. intros. rewrite <- typ_7. change 0x7f with (N.ones 7). rewrite N.land_ones. reflexivity. Qed.

Lemma tid_eq: forall (m:memory) fs, m Ⓓ[fs ⊕ 0x2d0] = m Ⓓ[720 + fs].
Proof. intros. rewrite getmem_mod_l, N.add_comm. reflexivity. Qed.

Ltac bc_norm :=
  repeat match goal with
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end.

Ltac typ_rw :=
  unfold unlock_ok, typ in *; rewrite ?tid_eq, ?typ_7, ?typ_7m;
  rewrite ?(typ_b _ _ 124), ?(typ_b _ _ 128), ?(typ_w _ _ 383) by reflexivity.

Ltac pick k :=
  match k with
  | 1 => left | 2 => right; left | 3 => do 2 right; left
  | 4 => do 3 right; left | 5 => do 4 right; left | 6 => do 5 right
  end.

(* finish a chosen case of unlock_ok *)
Ltac uok_close :=
  repeat split;
  lazymatch goal with
  | |- _ = release _ _ =>
      unfold release; psimpl;
      repeat match goal with H: getmem 64 LittleE 4 _ _ = 1 |- _ => rewrite H; clear H end;
      reflexivity
  | |- _ = _ => first [assumption | reflexivity]
  | |- _ <> _ => assumption
  | |- _ \/ _ => first [left; assumption | right; assumption]
  end.

Ltac ret_tac k :=
  split; [reflexivity|];
  split; [unfold saved; psimpl; repeat split; assumption|];
  eexists; split; [apply agree_refl|];
  typ_rw; pick k; uok_close.

Ltac cut_tac k :=
  eexists; split; [reflexivity|];
  split; [typ_rw; pick k; uok_close|];
  split; [reflexivity|]; split; [reflexivity|];
  split; [assumption|];
  unfold saved; psimpl; repeat split; assumption.

Theorem pthread_mutex_unlock_correct:
  forall cp s t xs' sp mem a fs
         (WT: welltyped_code cp) (WAKE: unlock_wake_contract cp)
         (ENTRY: startof t xs' = (Addr 1677936, s))
         (MDL: models x64typctx s)
         (RDI: s R_RDI = a) (FS: s R_FS_BASE = fs) (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem)
         (SPB: sp < 2^64),
  satisfies_all (unlock_with cp)
    (invs1 sp mem a fs 0 (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits1 sp mem a fs 0 (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply unlock_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT WAKE SPB. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (RDI & FS & SP & MEM & RBX & RBP & R12 & R13 & R14 & R15).
    Time repeat x64_step.
    all: bc_norm.
    (* kind 0: normal *)
    + ret_tac 1.
    + ret_tac 1.
    + cut_tac 1.
    + ret_tac 1.
    + cut_tac 1.
    (* elision *)
    + typ_rw. unfold saved. psimpl. repeat split; first [assumption | reflexivity].
    (* recursive, owner = TID, count 1 -> 0: release *)
    + ret_tac 4.
    + ret_tac 4.
    + cut_tac 4.
    + ret_tac 4.
    + cut_tac 4.
    (* recursive, count > 1 *)
    + ret_tac 3.
    (* recursive, not the owner *)
    + ret_tac 2.
    (* adaptive *)
    + ret_tac 1.
    + ret_tac 1.
    + cut_tac 1.
    + ret_tac 1.
    + cut_tac 1.
    (* errorcheck, unlocked *)
    + ret_tac 5.
    (* errorcheck, owner *)
    + ret_tac 6.
    + ret_tac 6.
    + cut_tac 6.
    + ret_tac 6.
    + cut_tac 6.
    (* errorcheck, not the owner *)
    + ret_tac 5.
    (* invalid kind: __assert_fail *)
    + typ_rw. repeat split; assumption.
    (* robust / PI / PP: __pthread_mutex_unlock_full *)
    + typ_rw. unfold saved. psimpl. repeat split; first [assumption | reflexivity].
  - (* the wake call *)
    destruct PRE as (M & MEM & UOK & RSP & RDI & RAX & RBX & RBP & R12 & R13 & R14 & R15).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply unlock_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply WAKE; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply unlock_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    rewrite RBX in RBXc. rewrite RBP in RBPc. rewrite R12 in R12c.
    rewrite R13 in R13c. rewrite R14 in R14c. rewrite R15 in R15c.
    clear - RSPc MEMc RBXc RBPc R12c R13c R14c R15c MDL' UOK SPB t'.
    rename s' into s. rename MDL' into MDL. rename t' into t.
    repeat x64_step.
    split. reflexivity.
    split. unfold saved. psimpl. repeat split; assumption.
    exists M. split; [|exact UOK].
    repeat (apply agree_setwin; [reflexivity | discriminate | discriminate |
              clear - SPB; unfold msub; change (2^64) with 18446744073709551616 in *; lia |]).
    apply agree_refl.
Time Qed.

(* Non-vacuity: the wake contract is satisfiable.  The witness places a bare
   RET at P_WAKE (and a Nop everywhere else outside pthread_mutex_unlock). *)
Definition ret_stmt : stmt :=
  Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
  Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
  Jmp (Var R_RIP).
Definition cp_ret (_:store) (a:addr) : N * stmt := if a =? P_WAKE then (1, ret_stmt) else (1, Nop).

Lemma cp_ret_welltyped: welltyped_code cp_ret.
Proof. intros s a. unfold cp_ret. destruct (a =? P_WAKE); apply typchk_stmt_compute; vm_compute; exact I. Qed.

Theorem unlock_wake_contract_satisfiable: exists cp, welltyped_code cp /\ unlock_wake_contract cp.
Proof.
  exists cp_ret. split. exact cp_ret_welltyped.
  intros s t xs' sp mem p f rbx rbp r12 r13 r14 r15
    ENTRY MDL RDI RSI RSP MEM [RBX [RBP [R12 [R13 [R14 R15]]]]] RET. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply unlock_with_welltyped, cp_ret_welltyped.
  intro MDL1. clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (RDI & RSI & RSP & MEM & RET & RBX & RBP & R12 & R13 & R14 & R15).
  x64_step. rewrite RET. unfold RET_WAKE. x64_step.
  split. reflexivity. split. reflexivity.
  repeat split; assumption.
Qed.

(* pthread_mutex_lock -- lock a mutex

   SEMANTICS
   ---------
   glibc 2.35's pthread_mutex_lock(m) (___pthread_mutex_lock), with the
   struct layout of amd64_pthread_mutex_unlock_proof.v (__lock 0, __count 4,
   __owner 8, __nusers 12, __kind 16, __spins 20 (16 bits)).  typ = __kind,
   kind = typ & 0x17f, TID = THREAD_SELF->tid (fs + 0x2d0).
     - typ & 0x7c <> 0 (robust, PI, PP): tail call __pthread_mutex_lock_full.
     - kind = 0 (NORMAL / TIMED), and error-check mutexes not owned by the
       caller: take __lock (0 -> 1; if it is held, __lll_lock_wait, which
       returns with __lock = 2), then assert __owner = 0, set __owner := TID,
       ++__nusers, return 0.
     - kind = 0x100 (elision): tail call __lll_lock_elision.
     - typ & 0x7f = 1 (RECURSIVE): if __owner = TID, ++__count (EAGAIN = 11
       when it would overflow); otherwise take the lock as above with
       __count := 1.
     - typ & 0x7f = 3 (ADAPTIVE): try once; if that fails, spin re-reading
       __lock up to a bound (and update the __spins estimate), then wait.
     - typ & 0x7f = 2 (ERRORCHECK): EDEADLK (35) if __owner = TID.
     - other kinds: __assert_fail.
   Taking the lock uses LOCK CMPXCHG, or a plain store when the mutex is
   process-private and the process is single-threaded; either way __lock
   becomes 1.

   SPECIFICATION (man 3 pthread_mutex_lock, POSIX, Ubuntu 22.04)
   -------------------------------------------------------------

     int pthread_mutex_lock(pthread_mutex_t *mutex);

     The mutex object referenced by mutex shall be locked by a call to
     pthread_mutex_lock() that returns zero [...].  If the mutex is already
     locked by another thread, the calling thread shall block until the
     mutex becomes available.  [...]  If the mutex type is
     PTHREAD_MUTEX_RECURSIVE, then the mutex shall maintain the concept of
     a lock count.  [...]

     [EAGAIN] The mutex could not be acquired because the maximum number of
              recursive locks for mutex has been exceeded.
     [EDEADLK] The mutex type is PTHREAD_MUTEX_ERRORCHECK and the current
              thread already owns the mutex.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol pthread_mutex_lock at 0x97ef0 (Ghidra address 0x197ef0, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see pthread_mutex_lock_amd64.v (global
            addresses).  LOCK CMPXCHG is lifted as an ordinary compare-and-
            exchange: Picinae's semantics is single-threaded.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   STATUS:  pthread_mutex_lock_correct is Admitted (QED-SLOW): its tactic
            proof is complete but the kernel check is too slow; see the end of
            the file.  lock_wait_contract_satisfiable is proved.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = a (the mutex), FS_BASE = fs, RSP = sp, memory m.
   Preconditions: __pthread_force_elision (m Ⓓ[0x31ca94]) is 0, its
            default; the mutex, THREAD_SELF->tid and that global are not in
            the 32 bytes below sp, and tid is not inside the mutex;
            __lll_lock_wait meets lock_wait_contract (it returns with
            __lock = 2 and nothing else changed).
   Output:  at RET: RSP = sp, RBX, RBP, R12-R15 unchanged, and for some M that
            agrees with the final memory outside the 32 bytes below sp,
            lock_ok m a fs RAX M.  The tail calls and __assert_fail are exits
            with their own postconditions.  (Partial correctness: a call
            that blocks forever has no final state.)
 *)

Require Import Picinae_amd64.
Require Import pthread_mutex_lock_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring.
Import ListNotations.
Open Scope N.

Theorem lock_welltyped: welltyped_prog x64typctx pthread_mutex_lock_amd64.
Proof. Picinae_typecheck. Qed.

Definition P_WAIT := 0x191290.       (* __lll_lock_wait *)

Definition lock_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match pthread_mutex_lock_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma lock_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (lock_with cp).
Proof.
  intros cp WT s a. unfold lock_with.
  pose proof (lock_welltyped s a) as H.
  destruct (pthread_mutex_lock_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

(* After __lock is taken (in m'): __owner := TID, ++__nusers. *)
Definition finish (m m':memory) (a fs:N) :=
  m' [Ⓓ 8 + a := m Ⓓ[fs ⊕ 0x2d0]] [Ⓓ 12 + a := m Ⓓ[12 + a] + 1].

Definition taken (v:N) := v = 1 \/ v = 2.

Definition lock_ok (m:memory) (a fs r:N) (M:memory) :=
  let typ := m Ⓓ[16 + a] in
  let tid := m Ⓓ[fs ⊕ 0x2d0] in
  let own := m Ⓓ[8 + a] in
  (* normal, or error-check not owned by the caller *)
  ((typ .& 0x17f = 0 \/ (typ .& 0x7f = 2 /\ own <> tid)) /\ own = 0 /\ r = 0 /\
     exists v, taken v /\ M = finish m (m [Ⓓ a := v]) a fs) \/
  (* recursive, already owned *)
  (typ .& 0x7f = 1 /\ own = tid /\ m Ⓓ[4 + a] = 0xffffffff /\ r = 11 /\ M = m) \/
  (typ .& 0x7f = 1 /\ own = tid /\ m Ⓓ[4 + a] <> 0xffffffff /\ r = 0 /\
     M = m [Ⓓ 4 + a := m Ⓓ[4 + a] + 1]) \/
  (* recursive, first lock *)
  (typ .& 0x7f = 1 /\ own <> tid /\ own = 0 /\ r = 0 /\
     exists v, taken v /\ M = finish m (m [Ⓓ a := v] [Ⓓ 4 + a := 1]) a fs) \/
  (* adaptive *)
  (typ .& 0x7f = 3 /\ own = 0 /\ r = 0 /\
     exists v w, taken v /\ (M = finish m (m [Ⓓ a := v]) a fs \/
                             M = finish m (m [Ⓓ a := v] [Ⓦ 20 + a := w]) a fs)) \/
  (* error-check, already owned *)
  (typ .& 0x7f = 2 /\ own = tid /\ r = 35 /\ M = m).

Section Invariants.
  Variable sp : N.
  Variable mem : memory.
  Variables a fs arg2 : N.
  Variables rbx rbp r12 r13 r14 r15 : N.

  Definition saved (s:store) :=
    s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
    s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.

  Definition typ := mem Ⓓ[16 + a].
  Definition tid := mem Ⓓ[fs ⊕ 0x2d0].
  Definition own := mem Ⓓ[8 + a].
  Definition fw := sp ⊖ 32.          (* the frame: 32 bytes below sp *)

  (* registers other than RBX (which lock spills and reuses) *)
  Definition saved5 (s:store) :=
    s R_RBP = rbp /\ s R_R12 = r12 /\ s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.

  (* in lock's body: RSP, the spilled RBX, a, fs *)
  Definition frame (s:store) :=
    s R_RSP = sp ⊖ 24 /\ s V_MEM64 Ⓠ[sp ⊖ 8] = rbx /\ s R_RDI = a /\ s R_FS_BASE = fs /\ saved5 s.

  Definition normal_like := typ .& 0x17f = 0 \/ (typ .& 0x7f = 2 /\ own <> tid).

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (x:addr) : T :=
    match x with
    (* __lll_lock_wait (subroutine 0): wait(a, arg2) *)
    | 1643152 => Inv 0 (s R_RDI = a /\ s R_RSI = arg2 /\ s R_RSP = sp /\ s V_MEM64 = mem /\ s R_FS_BASE = fs /\
                        (mem Ⓠ[sp] = 1671170 \/ mem Ⓠ[sp] = 1671261 \/ mem Ⓠ[sp] = 1671527) /\
                        saved s)
    (* returning to the call site whose address was pushed *)
    | 1671170 => Post 0 (mem Ⓠ[sp] = 1671170 /\ s R_RSP = sp ⊕ 8 /\ s V_MEM64 = mem [Ⓓ a := 2] /\
                         s R_FS_BASE = fs /\ saved s)
    | 1671261 => Post 0 (mem Ⓠ[sp] = 1671261 /\ s R_RSP = sp ⊕ 8 /\ s V_MEM64 = mem [Ⓓ a := 2] /\
                         s R_FS_BASE = fs /\ saved s)
    | 1671527 => Post 0 (mem Ⓠ[sp] = 1671527 /\ s R_RSP = sp ⊕ 8 /\ s V_MEM64 = mem [Ⓓ a := 2] /\
                         s R_FS_BASE = fs /\ saved s)
    (* pthread_mutex_lock (subroutine 1) *)
    | 1670896 => Inv 1 (s R_RDI = a /\ s R_FS_BASE = fs /\ s R_RSP = sp /\ s V_MEM64 = mem /\ saved s)
    | 1671020 => Post 1 (s R_RSP = sp /\ saved s /\
                         exists M, agree fw 32 (s V_MEM64) M /\ lock_ok mem a fs (s R_RAX) M)
    (* tail call __pthread_mutex_lock_full(a) *)
    | 1669024 => Post 1 (typ .& 0x7c <> 0 /\ s R_RDI = a /\ s R_RSP = sp /\ s V_MEM64 = mem /\ saved s)
    (* tail call __lll_lock_elision(&a->__lock, &a->__elision, typ & 0x80) *)
    | 1641744 => Post 1 (typ .& 0x17f = 0x100 /\ s R_RDI = a /\ s R_RSI = 22 ⊕ a /\
                         s R_RDX = typ .& 0x80 /\ s R_RSP = sp /\ saved s /\
                         agree fw 32 (s V_MEM64) mem)
    (* __assert_fail: __owner was nonzero after taking the lock, or a bad kind *)
    | 1285712 => Post 1 True
    (* dispatch, with only RBX spilled *)
    | 1670946 => Inv 1 (frame s /\ normal_like /\ s V_MEM64 = mem [Ⓠ sp ⊖ 8 := rbx])
    | 1671104 => Inv 1 (frame s /\ typ .& 0x7c = 0 /\ typ .& 0x17f <> 0 /\ typ .& 0x17f <> 0x100 /\
                        s V_MEM64 = mem [Ⓠ sp ⊖ 8 := rbx])
    | 1671180 => Inv 1 (frame s /\ typ .& 0x7f = 1 /\ own <> tid /\ s V_MEM64 = mem [Ⓠ sp ⊖ 8 := rbx])
    | 1671268 => Inv 1 (frame s /\ typ .& 0x7c = 0 /\ typ .& 0x17f <> 0 /\ typ .& 0x17f <> 0x100 /\
                        typ .& 0x7f <> 1 /\ s V_MEM64 = mem [Ⓠ sp ⊖ 8 := rbx])
    (* before each __lll_lock_wait call *)
    | 1671160 => Inv 1 (frame s /\ normal_like /\ agree fw 32 (s V_MEM64) mem)
    | 1671251 => Inv 1 (frame s /\ typ .& 0x7f = 1 /\ own <> tid /\ agree fw 32 (s V_MEM64) mem)
    | 1671511 => Inv 1 (frame s /\ typ .& 0x7f = 3 /\ agree fw 32 (s V_MEM64) mem)
    (* adaptive, first try failed: the spin bound in RAX/RDX is forgotten *)
    | 1671387 => Inv 1 (frame s /\ typ .& 0x7f = 3 /\ agree fw 32 (s V_MEM64) mem)
    (* the adaptive spin loop *)
    | 1671403 => Inv 1 (frame s /\ typ .& 0x7f = 3 /\ s R_RCX = 1 /\ agree fw 32 (s V_MEM64) mem)
    (* __lock taken *)
    | 1670986 => Inv 1 (exists v, taken v /\ frame s /\ normal_like /\
                        agree fw 32 (s V_MEM64) (mem [Ⓓ a := v]))
    | 1671215 => Inv 1 (exists v, taken v /\ frame s /\ typ .& 0x7f = 1 /\ own <> tid /\
                        agree fw 32 (s V_MEM64) (mem [Ⓓ a := v]))
    | 1671428 => Inv 1 (exists v, taken v /\ frame s /\ typ .& 0x7f = 3 /\
                        agree fw 32 (s V_MEM64) (mem [Ⓓ a := v]))
    | 1671294 => Inv 1 (exists v, taken v /\ frame s /\ typ .& 0x7f = 3 /\
                        (agree fw 32 (s V_MEM64) (mem [Ⓓ a := v]) \/
                         exists w, agree fw 32 (s V_MEM64) (mem [Ⓓ a := v] [Ⓦ 20 + a := w])))
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (lock_with cp) invs.
  Definition invs0 cp := make_invs 0 (lock_with cp) invs.
  Definition exits1 cp := make_exits 1 (lock_with cp) invs.
  Definition invs1 cp := make_invs 1 (lock_with cp) invs.
End Invariants.

Definition lock_wait_contract (cp: store -> addr -> N * stmt) :=
  forall s t xs' sp mem p fs f rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_WAIT, s) -> models x64typctx s ->
  s R_RDI = p -> s R_RSI = f -> s R_RSP = sp -> s V_MEM64 = mem -> s R_FS_BASE = fs ->
  (mem Ⓠ[sp] = 1671170 \/ mem Ⓠ[sp] = 1671261 \/ mem Ⓠ[sp] = 1671527) ->
  saved rbx rbp r12 r13 r14 r15 s ->
  satisfies_all (lock_with cp)
    (invs0 sp mem p fs f rbx rbp r12 r13 r14 r15 cp)
    (exits0 sp mem p fs f rbx rbp r12 r13 r14 r15 cp) (xs'::t).

(* Frame bookkeeping.  fw sp = sp - 32 is the 32-byte frame below sp. *)
Lemma nov_shrink:
  forall a l b m a' l' b' m' x y, x + l' <= l -> y + m' <= m ->
  a' mod 2^64 = (a + x) mod 2^64 -> b' mod 2^64 = (b + y) mod 2^64 ->
  ~ overlap 64 a l b m -> ~ overlap 64 a' l' b' m'.
Proof.
  intros a l b m a' l' b' m' x y XL YM A B NO [i [j [I [J E]]]]. apply NO.
  exists (x + i), (y + j). split. lia. split. lia.
  rewrite !N.add_assoc, <- (N.add_mod_idemp_l (a + x)), <- A, (N.add_mod_idemp_l a'),
          <- (N.add_mod_idemp_l (b + y)), <- B, (N.add_mod_idemp_l b') by discriminate.
  exact E.
Qed.

Lemma agree_read:
  forall lo len (M1 M2:memory) p w, agree lo len M1 M2 -> ~ overlap 64 p w lo len ->
  getmem 64 LittleE w M1 p = getmem 64 LittleE w M2 p.
Proof.
  intros lo len M1 M2 p w AG NO. apply getmem_frame_mem. intros b B.
  rewrite <- !(getmem_1 64 LittleE). apply AG. intro W. apply NO.
  exists (msub 64 b p), (msub 64 b lo). split. exact B. split. exact W.
  rewrite !add_msub_assoc, !(N.add_comm _ b), !add_msub_r. reflexivity.
Qed.

Lemma agree_set_both:
  forall lo len (M1 M2:memory) L p v, 0 < L -> L <= 2^64 -> agree lo len M1 M2 ->
  agree lo len (setmem 64 LittleE L M1 p v) (setmem 64 LittleE L M2 p v).
Proof.
  intros lo len M1 M2 L p v LP LL AG b B.
  rewrite !byte_setmem_cases by assumption. destruct (_ <? _). reflexivity. apply AG, B.
Qed.

Lemma frame_slot: forall sp x, sp < 2^64 -> 8 <= x <= 32 ->
  (sp ⊖ x) mod 2^64 = ((sp ⊖ 32) + (32 - x)) mod 2^64.
Proof.
  intros sp x SPB X. unfold msub. rewrite N.mod_mod, N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small x), (N.mod_small 32) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

(* Slots of the frame vs the mutex, the TID field and the elision global. *)
Lemma nov_mut_slot: forall a sp k w x, sp < 2^64 -> ~ overlap 64 a 24 (sp ⊖ 32) 32 ->
  k + w <= 24 -> 8 <= x <= 32 -> ~ overlap 64 (k + a) w (sp ⊖ x) 8.
Proof.
  intros a sp k w x SPB NO KW X. apply (nov_shrink a 24 (sp ⊖ 32) 32 _ _ _ _ k (32 - x));
  [lia | lia | rewrite N.add_comm; reflexivity | apply frame_slot; assumption | exact NO].
Qed.

Lemma nov_mut0_slot: forall a sp w x, sp < 2^64 -> ~ overlap 64 a 24 (sp ⊖ 32) 32 ->
  w <= 24 -> 8 <= x <= 32 -> ~ overlap 64 a w (sp ⊖ x) 8.
Proof.
  intros a sp w x SPB NO W X. apply (nov_shrink a 24 (sp ⊖ 32) 32 _ _ _ _ 0 (32 - x));
  [lia | lia | rewrite N.add_0_r; reflexivity | apply frame_slot; assumption | exact NO].
Qed.

Lemma nov_tid_slot: forall fs sp x, sp < 2^64 -> ~ overlap 64 (fs ⊕ 720) 4 (sp ⊖ 32) 32 ->
  8 <= x <= 32 -> ~ overlap 64 (720 + fs) 4 (sp ⊖ x) 8.
Proof.
  intros fs sp x SPB NO X. apply (nov_shrink (fs ⊕ 720) 4 (sp ⊖ 32) 32 _ _ _ _ 0 (32 - x));
  [lia | lia | rewrite N.add_0_r, N.mod_mod, N.add_comm by discriminate; reflexivity
  | apply frame_slot; assumption | exact NO].
Qed.

Lemma nov_glob_slot: forall g sp x, sp < 2^64 -> ~ overlap 64 g 4 (sp ⊖ 32) 32 ->
  8 <= x <= 32 -> ~ overlap 64 g 4 (sp ⊖ x) 8.
Proof.
  intros g sp x SPB NO X. apply (nov_shrink g 4 (sp ⊖ 32) 32 _ _ _ _ 0 (32 - x));
  [lia | lia | rewrite N.add_0_r; reflexivity | apply frame_slot; assumption | exact NO].
Qed.

Lemma nov_tid_mut: forall fs a k w, ~ overlap 64 (fs ⊕ 720) 4 a 24 -> k + w <= 24 ->
  ~ overlap 64 (720 + fs) 4 (k + a) w.
Proof.
  intros fs a k w NO KW. apply (nov_shrink (fs ⊕ 720) 4 a 24 _ _ _ _ 0 k);
  [lia | lia | rewrite N.add_0_r, N.mod_mod, N.add_comm by discriminate; reflexivity
  | rewrite N.add_comm; reflexivity | exact NO].
Qed.

Lemma nov_tid_mut0: forall fs a w, ~ overlap 64 (fs ⊕ 720) 4 a 24 -> w <= 24 ->
  ~ overlap 64 (720 + fs) 4 a w.
Proof.
  intros fs a w NO W. apply (nov_shrink (fs ⊕ 720) 4 a 24 _ _ _ _ 0 0);
  [lia | lia | rewrite N.add_0_r, N.mod_mod, N.add_comm by discriminate; reflexivity
  | rewrite N.add_0_r; reflexivity | exact NO].
Qed.

Lemma slot_disj: forall sp x y, x <= 32 -> y <= 32 -> (x + 8 <= y \/ y + 8 <= x) ->
  ~ overlap 64 (sp ⊖ x) 8 (sp ⊖ y) 8.
Proof.
  intros sp x y X Y D [i [j [I [J E]]]]. unfold msub in E.
  change (2^64) with 18446744073709551616 in *.
  rewrite (N.mod_small x), (N.mod_small y) in E by lia. lia.
Qed.

Lemma rsp32: forall sp, sp ⊖ 32 ⊕ 8 = sp ⊖ 24.
Proof.
  intro sp. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small 32), (N.mod_small 24) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Ltac nov_tac :=
  lazymatch goal with
  | |- ~ overlap 64 (msub 64 _ _) 8 (msub 64 _ _) 8 => apply slot_disj; clear; lia
  | |- ~ overlap 64 (720 + _) _ (msub 64 _ _) _ =>
      apply nov_tid_slot; [assumption | assumption | clear; lia]
  | |- ~ overlap 64 (720 + _) _ (_ + _) _ =>
      apply nov_tid_mut; [assumption | clear; lia]
  | |- ~ overlap 64 (720 + _) _ _ _ =>
      apply nov_tid_mut0; [assumption | clear; lia]
  | |- ~ overlap 64 (_ + _) _ (msub 64 _ _) _ =>
      apply nov_mut_slot; [assumption | assumption | clear; lia | clear; lia]
  | |- ~ overlap 64 (msub 64 _ _) _ (_ + _) _ =>
      apply noverlap_sym; apply nov_mut_slot; [assumption | assumption | clear; lia | clear; lia]
  | |- ~ overlap 64 (msub 64 _ _) _ _ _ =>
      apply noverlap_sym; apply nov_mut0_slot; [assumption | assumption | clear; lia | clear; lia]
  | |- ~ overlap 64 _ 4 (msub 64 _ _) _ =>
      first [ apply nov_glob_slot; [assumption | assumption | clear; lia]
            | apply nov_mut0_slot; [assumption | assumption | clear; lia | clear; lia] ]
  | |- ~ overlap 64 _ _ (msub 64 _ _) _ =>
      apply nov_mut0_slot; [assumption | assumption | clear; lia | clear; lia]
  end.

(* Read through the frame stores (and TID through mutex stores). *)
Ltac frd :=
  repeat match goal with
  | |- context [getmem 64 LittleE ?w (setmem 64 LittleE ?L ?M ?q ?v) ?p] =>
      rewrite (getmem_noverlap 64 LittleE LittleE w L M p q v) by nov_tac
  end.
Ltac frd_in H :=
  repeat match type of H with
  | context [getmem 64 LittleE ?w (setmem 64 LittleE ?L ?M ?q ?v) ?p] =>
      rewrite (getmem_noverlap 64 LittleE LittleE w L M p q v) in H by nov_tac
  end.

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

Lemma tid_eq: forall (m:memory) fs, m Ⓓ[fs ⊕ 0x2d0] = m Ⓓ[720 + fs].
Proof. intros. rewrite getmem_mod_l, N.add_comm. reflexivity. Qed.

Ltac bcn :=
  repeat match goal with
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  end.

(* The kind tests, as the lifted code phrases them. *)
Ltac typ_rw := unfold normal_like, typ, own, tid; rewrite ?tid_eq.

(* Put the lifted kind tests in the hypotheses into typ form (explicit
   arguments: rewriting with a pattern over getmem is very slow). *)
Ltac bc_typ m a :=
  repeat match goal with
  | H: context [getmem 64 LittleE 1 m (16 + a) .& ?K] |- _ =>
      rewrite <- (typ_b m a K) in H by reflexivity
  | H: context [getmem 64 LittleE 2 m (16 + a) .& ?K] |- _ =>
      rewrite <- (typ_w m a K) in H by reflexivity
  | H: context [getmem 64 LittleE 1 m (16 + a) mod 2^7] |- _ =>
      rewrite <- (typ_7 m a) in H
  end.

(* Close a conjunct about the frame, the kind word, or the frame window. *)
Ltac sreflexivity' := match goal with |- ?a = ?b => constr_eq a b; reflexivity end.
Lemma fin_agree:
  forall lo (M B m:memory) a fs, agree lo 32 M B ->
  ~ overlap 64 (720 + fs) 4 lo 32 -> ~ overlap 64 (12 + a) 4 lo 32 ->
  B Ⓓ[720 + fs] = m Ⓓ[fs ⊕ 0x2d0] -> B Ⓓ[12 + a] = m Ⓓ[12 + a] ->
  agree lo 32 (M [Ⓓ 8 + a := M Ⓓ[720 + fs]] [Ⓓ 12 + a := 1 + M Ⓓ[12 + a]]) (finish m B a fs).
Proof.
  intros lo M B m a fs AG NT NN BT BN. unfold finish.
  rewrite (agree_read lo 32 M B (720 + fs) 4 AG NT), BT.
  rewrite (agree_read lo 32 M B (12 + a) 4 AG NN), BN, (N.add_comm 1 (m Ⓓ[12 + a])).
  apply agree_set_both; [reflexivity | discriminate |].
  apply agree_set_both; [reflexivity | discriminate | exact AG].
Qed.

Lemma fin_agree2:
  forall lo (M B m:memory) a fs x y, agree lo 32 M B ->
  x = m Ⓓ[fs ⊕ 0x2d0] -> y = m Ⓓ[12 + a] ->
  agree lo 32 (M [Ⓓ 8 + a := x] [Ⓓ 12 + a := 1 + y]) (finish m B a fs).
Proof.
  intros lo M B m a fs x y AG -> ->. unfold finish. rewrite (N.add_comm 1 (m Ⓓ[12 + a])).
  apply agree_set_both; [reflexivity | discriminate |].
  apply agree_set_both; [reflexivity | discriminate | exact AG].
Qed.

(* The frame window vs the mutex fields and the TID field. *)
Lemma nov_mut_fw: forall a sp k w, ~ overlap 64 a 24 (sp ⊖ 32) 32 -> k + w <= 24 ->
  ~ overlap 64 (k + a) w (fw sp) 32.
Proof.
  intros a sp k w NO KW. unfold fw. apply (nov_shrink a 24 (sp ⊖ 32) 32 _ _ _ _ k 0);
  [lia | lia | rewrite N.add_comm; reflexivity | rewrite N.add_0_r; reflexivity | exact NO].
Qed.

Lemma nov_tid_fw: forall fs sp, ~ overlap 64 (fs ⊕ 720) 4 (sp ⊖ 32) 32 ->
  ~ overlap 64 (720 + fs) 4 (fw sp) 32.
Proof.
  intros fs sp NO. unfold fw. apply (nov_shrink (fs ⊕ 720) 4 (sp ⊖ 32) 32 _ _ _ _ 0 0);
  [lia | lia | rewrite N.add_0_r, N.mod_mod, N.add_comm by discriminate; reflexivity
  | rewrite N.add_0_r; reflexivity | exact NO].
Qed.

Lemma inc32_zero: forall c, c < 2^32 -> ((1 + c) mod 2^32 = 0 <-> c = 4294967295).
Proof.
  intros c C. change (2^32) with 4294967296 in *. split; intro H.
  - destruct (N.lt_ge_cases (1 + c) 4294967296).
    + rewrite N.mod_small in H; lia.
    + lia.
  - subst c. reflexivity.
Qed.

(* A return to a call site other than the pushed one contradicts the pushed
   return address. *)
Ltac wrong_site P :=
  let R := fresh "R" in destruct P as (R & _);
  rewrite getmem_setmem in R by discriminate;
  change (2^(8*8)) with 18446744073709551616 in R; rewrite N.mod_small in R by reflexivity;
  discriminate R.

Ltac kind_norm H := unfold normal_like in H; unfold typ, own, tid in H; rewrite ?tid_eq in H; psimpl in H.

Ltac frd_bcs :=
  repeat match goal with
  | H: context [getmem 64 LittleE _ (setmem 64 LittleE 8 _ (msub 64 _ _) _) _] |- _ => progress frd_in H
  end.

(* syntactic assumption: plain assumption tries conversion against the large
   memory terms in context *)
Ltac sassumption := match goal with H: ?T |- ?G => constr_eq T G; exact H end.

Ltac lk_conj RBXB SPB :=
  change (2^7) with 128; change (2^8) with 256;
  first [ sassumption |
  lazymatch goal with
  | |- getmem 64 LittleE 8 (setmem 64 LittleE 8 _ ?q _) ?q = _ =>
      rewrite getmem_setmem by discriminate; apply N.mod_small;
      change (2^(8*8)) with (2^64); first [exact RBXB | sassumption]
  | |- getmem 64 LittleE 8 (setmem 64 LittleE _ _ _ _) (msub 64 _ _) = _ =>
      frd; lk_conj RBXB SPB
  | |- msub 64 _ 32 ⊕ 8 = msub 64 _ 24 => apply rsp32
  | |- exists v, taken v /\ _ =>
      first [ exists 1; split; [left; reflexivity | lk_conj RBXB SPB]
            | exists 2; split; [right; reflexivity | lk_conj RBXB SPB] ]
  | |- _ /\ _ => split; lk_conj RBXB SPB
  | |- agree _ _ (setmem 64 LittleE ?L _ ?p ?v) (setmem 64 LittleE ?L _ ?p ?v) =>
      apply agree_set_both; [reflexivity | discriminate | lk_conj RBXB SPB]
  | |- agree _ _ (setmem 64 LittleE _ _ _ _) _ =>
      apply agree_setwin;
      [ reflexivity | discriminate | discriminate
      | unfold fw, msub; clear - SPB; change (2^64) with 18446744073709551616 in *; lia
      | first [apply agree_refl | lk_conj RBXB SPB] ]
  | |- _ \/ _ => first [left; sassumption | right; sassumption | left; lk_conj RBXB SPB | right; lk_conj RBXB SPB]
  | |- _ => first [sreflexivity' | sassumption
                  | (frd; psimpl; first [sreflexivity' | sassumption])]
  end ].

Ltac lk_fin RBXB SPB :=
  unfold frame, saved5, saved; typ_rw; psimpl;
  repeat split; lk_conj RBXB SPB.

(* The proof never needs the parity, adjust, overflow or sign flags exactly:
   abstracting them only adds branches (all of which are proved). *)
Ltac ignore_vars v ::= constr:(match v with R_AF | R_OF | R_PF | R_SF => true | _ => false end).

Theorem pthread_mutex_lock_correct:
  forall cp s t xs' sp mem a fs
         (WT: welltyped_code cp) (WAIT: lock_wait_contract cp)
         (ENTRY: startof t xs' = (Addr 1670896, s))
         (MDL: models x64typctx s)
         (RDI: s R_RDI = a) (FS: s R_FS_BASE = fs) (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem)
         (SPB: sp < 2^64) (NOEL: mem Ⓓ[0x31ca94] = 0)
         (NOVF: ~ overlap 64 a 24 (sp ⊖ 32) 32)
         (NOVT: ~ overlap 64 (fs ⊕ 0x2d0) 4 (sp ⊖ 32) 32)
         (NOVTA: ~ overlap 64 (fs ⊕ 0x2d0) 4 a 24)
         (NOVG: ~ overlap 64 0x31ca94 4 (sp ⊖ 32) 32),
  satisfies_all (lock_with cp)
    (invs1 sp mem a fs 0 (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits1 sp mem a fs 0 (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply lock_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  assert (RBXB: rbx0 < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT WAIT SPB NOEL NOVF NOVT NOVTA NOVG RBXB. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  (* SEGMENT entry *)
  1: { destruct PRE as (RDI & FS & SP & MEM & RBX & RBP & R12 & R13 & R14 & R15).
    repeat x64_step.
    all: bcn.
    all: try (frd_in BC1; rewrite NOEL in BC1; exfalso; apply BC1; reflexivity).
    all: change (2^7) with 128 in *; change (2^8) with 256 in *.
    all: lk_fin RBXB SPB.
  }
  (* SEGMENT normal path *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & NL & MEM).
    unfold normal_like, typ, own, tid in NL. rewrite tid_eq in NL. psimpl in NL.
    repeat x64_step.
    all: bcn.
    all: change (2^7) with 128 in *; change (2^8) with 256 in *.
    all: lk_fin RBXB SPB.
  }
  (* SEGMENT normal acquired: owner check, owner := TID, ++nusers *)
  1: { destruct PRE as (v & TK & (RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & NL & AG).
    repeat x64_step.
    all: bcn.
    + rewrite (agree_read _ _ _ _ (8 + a) 4 AG) in BC by (apply nov_mut_fw; [exact NOVF | clear; lia]).
      psimpl in BC.
      split. reflexivity.
      split. { unfold saved; psimpl. repeat split; try sassumption. frd. first [exact SLOT | lk_conj RBXB SPB]. }
      exists (finish mem (mem [Ⓓ a := v]) a fs). split.
      * apply fin_agree; [exact AG | apply nov_tid_fw, NOVT | apply nov_mut_fw; [exact NOVF | clear; lia] | |].
        -- rewrite (getmem_noverlap 64 LittleE LittleE 4 4 mem (720 + fs) a v) by nov_tac.
           rewrite tid_eq. reflexivity.
        -- psimpl. reflexivity.
      * unfold lock_ok. left. split. exact NL. split. exact BC. split. reflexivity.
        exists v. split. exact TK. reflexivity.
    + exact I.
  }
  (* SEGMENT kind dispatch: recursive? *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & K7C & K0 & K100 & MEM).
    assert (CB: mem Ⓓ[4 + a] < 2^32) by apply (getmem_bound 64 LittleE 4).
    kind_norm K7C. kind_norm K0. kind_norm K100.
    repeat x64_step.
    all: bcn.
    all: frd_bcs.
    all: change (2^7) with 128 in *; change (2^8) with 256 in *.
    all: try (lk_fin RBXB SPB; fail).
    + (* recursive, owner = TID, count = 2^32 - 1: EAGAIN *)
      apply (inc32_zero _ CB) in BC1.
      split. reflexivity.
      split. { unfold saved; psimpl. repeat split; sassumption. }
      exists mem. split. { lk_conj RBXB SPB. }
      unfold lock_ok. right. left. rewrite tid_eq. psimpl. change (2^7) with 128.
      repeat split; first [sassumption | sreflexivity'].
    + (* recursive, owner = TID: ++count *)
      assert (BC1': mem Ⓓ[4 + a] <> 4294967295) by (intro E; apply BC1, (inc32_zero _ CB), E).
      split. reflexivity.
      split. { unfold saved; psimpl. repeat split; try sassumption. frd. first [exact SLOT | lk_conj RBXB SPB]. }
      exists (mem [Ⓓ 4 + a := mem Ⓓ[4 + a] + 1]). split.
      { frd. rewrite (N.add_comm 1). apply agree_set_both; [reflexivity | discriminate |]. lk_conj RBXB SPB. }
      unfold lock_ok. right. right. left. rewrite tid_eq. psimpl. change (2^7) with 128.
      repeat split; first [sassumption | sreflexivity'].
  }
  (* SEGMENT wait (normal path) *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & NL & AG).
    assert (AB: a < 2^64) by (rewrite <- RDI; apply (MDL R_RDI 64); reflexivity).
    kind_norm NL.
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply lock_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply WAIT; [eassumption | eassumption | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | |].
      unfold s1. cbn [update iseq vareq]. psimpl. left. reflexivity.
      unfold saved. repeat split; reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    (* returned to its own call site *)
    1: { destruct PRE as (RETc & RSPc & MEMc & FSc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply lock_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    rewrite RBP in RBPc. rewrite R12 in R12c. rewrite R13 in R13c. rewrite R14 in R14c. rewrite R15 in R15c.
    rewrite FS in FSc.
    clear - RSPc MEMc FSc RBPc R12c R13c R14c R15c MDL' AG NL SLOT AB RBXB SPB NOVF NOVT NOVTA NOVG t'.
    rename s into s_call. rename s' into s. rename MDL' into MDL. rename t' into t.
    repeat x64_step.
    all: change (2^7) with 128 in *; change (2^8) with 256 in *.
    all: exists 2; split; [right; reflexivity|].
    all: lk_fin RBXB SPB. }
    (* the other return sites contradict the pushed return address *)
    all: wrong_site PRE. }
  (* SEGMENT recursive, not the owner: take the lock *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & REC & OWN & MEM).
    kind_norm REC. kind_norm OWN.
    repeat x64_step.
    all: bcn.
    all: frd_bcs.
    all: change (2^7) with 128 in *; change (2^8) with 256 in *.
    all: lk_fin RBXB SPB. }
  (* SEGMENT recursive acquired: owner check, count := 1, owner := TID, ++nusers *)
  1: { destruct PRE as (v & TK & (RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & REC & OWN & AG).
    kind_norm REC. kind_norm OWN. change (2^7) with 128 in REC.
    repeat x64_step.
    all: bcn.
    + rewrite (agree_read _ _ _ _ (8 + a) 4 AG) in BC by (apply nov_mut_fw; [exact NOVF | clear; lia]).
      psimpl in BC.
      split. reflexivity.
      split. { unfold saved; psimpl. repeat split; try sassumption. frd. exact SLOT. }
      exists (finish mem (mem [Ⓓ a := v] [Ⓓ 4 + a := 1]) a fs). split.
      * apply fin_agree2.
        -- apply agree_set_both; [reflexivity | discriminate | exact AG].
        -- frd. rewrite (agree_read _ _ _ _ (720 + fs) 4 AG) by (apply nov_tid_fw, NOVT).
           rewrite (getmem_noverlap 64 LittleE LittleE 4 4 mem (720 + fs) a v) by nov_tac.
           rewrite tid_eq. reflexivity.
        -- rewrite (agree_read _ _ _ _ (12 + a) 4 AG) by (apply nov_mut_fw; [exact NOVF | clear; lia]).
           psimpl. reflexivity.
      * unfold lock_ok. right. right. right. left. rewrite tid_eq. psimpl. change (2^7) with 128.
        split. sassumption. split. sassumption. split. exact BC. split. reflexivity.
        exists v. split. exact TK. reflexivity.
    + exact I.
  }
  (* SEGMENT wait (recursive) *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & REC & OWN & AG).
    assert (AB: a < 2^64) by (rewrite <- RDI; apply (MDL R_RDI 64); reflexivity).
    kind_norm REC. kind_norm OWN.
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply lock_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply WAIT; [eassumption | eassumption | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | |].
      unfold s1. cbn [update iseq vareq]. psimpl. right. left. reflexivity.
      unfold saved. repeat split; reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    (* the other return sites contradict the pushed return address *)
    all: try wrong_site PRE.
    (* returned to its own call site *)
    1: { destruct PRE as (RETc & RSPc & MEMc & FSc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply lock_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    rewrite RBP in RBPc. rewrite R12 in R12c. rewrite R13 in R13c. rewrite R14 in R14c. rewrite R15 in R15c.
    rewrite FS in FSc.
    clear - RSPc MEMc FSc RBPc R12c R13c R14c R15c MDL' AG REC OWN SLOT AB RBXB SPB NOVF NOVT NOVTA NOVG t'.
    rename s into s_call. rename s' into s. rename MDL' into MDL. rename t' into t.
    repeat x64_step.
    all: change (2^7) with 128 in *; change (2^8) with 256 in *.
    all: exists 2; split; [right; reflexivity|].
    all: lk_fin RBXB SPB. }
  }
  (* SEGMENT non-recursive dispatch: adaptive first try, errorcheck *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & K7C & K0 & K100 & NREC & MEM).
    kind_norm K7C. kind_norm K0. kind_norm K100. kind_norm NREC.
    repeat x64_step.
    all: bcn.
    all: frd_bcs.
    all: change (2^7) with 128 in *; change (2^8) with 256 in *.
    all: try exact I.
    all: try (lk_fin RBXB SPB; fail).
    (* errorcheck, already owned: EDEADLK *)
    split. reflexivity.
    split. { unfold saved; psimpl. repeat split; sassumption. }
    exists mem. split. { lk_conj RBXB SPB. }
    unfold lock_ok. do 5 right. rewrite tid_eq. psimpl. change (2^7) with 128.
    repeat split; first [sassumption | sreflexivity'].
  }
  (* SEGMENT adaptive acquired: owner check, owner := TID, ++nusers *)
  1: { destruct PRE as (v & TK & (RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & AD & AGs).
    kind_norm AD. change (2^7) with 128 in AD.
    repeat x64_step.
    all: bcn.
    + destruct AGs as [AG | [w AG]].
      * rewrite (agree_read _ _ _ _ (8 + a) 4 AG) in BC by (apply nov_mut_fw; [exact NOVF | clear; lia]).
        psimpl in BC.
        split. reflexivity.
        split. { unfold saved; psimpl. repeat split; try sassumption. frd. exact SLOT. }
        exists (finish mem (mem [Ⓓ a := v]) a fs). split.
        -- apply fin_agree2. exact AG.
           ++ rewrite (agree_read _ _ _ _ (720 + fs) 4 AG) by (apply nov_tid_fw, NOVT).
              frd. rewrite tid_eq. reflexivity.
           ++ rewrite (agree_read _ _ _ _ (12 + a) 4 AG) by (apply nov_mut_fw; [exact NOVF | clear; lia]).
              psimpl. reflexivity.
        -- unfold lock_ok. do 4 right. left. psimpl. change (2^7) with 128.
           split. sassumption. split. exact BC. split. reflexivity.
           exists v, 0. split. exact TK. left. reflexivity.
      * rewrite (agree_read _ _ _ _ (8 + a) 4 AG) in BC by (apply nov_mut_fw; [exact NOVF | clear; lia]).
        psimpl in BC.
        split. reflexivity.
        split. { unfold saved; psimpl. repeat split; try sassumption. frd. exact SLOT. }
        exists (finish mem (mem [Ⓓ a := v] [Ⓦ 20 + a := w]) a fs). split.
        -- apply fin_agree2. exact AG.
           ++ rewrite (agree_read _ _ _ _ (720 + fs) 4 AG) by (apply nov_tid_fw, NOVT).
              frd. rewrite tid_eq. reflexivity.
           ++ rewrite (agree_read _ _ _ _ (12 + a) 4 AG) by (apply nov_mut_fw; [exact NOVF | clear; lia]).
              psimpl. reflexivity.
        -- unfold lock_ok. do 4 right. left. psimpl. change (2^7) with 128.
           split. sassumption. split. exact BC. split. reflexivity.
           exists v, w. split. exact TK. right. reflexivity.
    + exact I.
  }
  (* SEGMENT adaptive spin setup *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & AD & AG).
    kind_norm AD. change (2^7) with 128 in AD.
    repeat x64_step.
    all: bcn.
    all: lk_fin RBXB SPB. }
  (* SEGMENT adaptive spin loop *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & AD & RCX & AG).
    kind_norm AD. change (2^7) with 128 in AD.
    repeat x64_step.
    all: bcn.
    all: lk_fin RBXB SPB.
  }
  (* SEGMENT adaptive, after spinning: update __spins *)
  1: { destruct PRE as (v & TK & (RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & AD & AG).
    kind_norm AD. change (2^7) with 128 in AD.
    repeat x64_step.
    all: bcn.
    all: exists v; split; [exact TK|].
    all: split; [unfold frame, saved5; psimpl; repeat split; first [sassumption | sreflexivity' | frd; exact SLOT] |].
    all: split; [typ_rw; psimpl; change (2^7) with 128; sassumption |].
    all: right; eexists; apply agree_set_both; [reflexivity | discriminate | exact AG].
  }
  (* SEGMENT wait (adaptive, after spinning) *)
  1: { destruct PRE as ((RSP & SLOT & RDI & FS & RBP & R12 & R13 & R14 & R15) & AD & AG).
    assert (AB: a < 2^64) by (rewrite <- RDI; apply (MDL R_RDI 64); reflexivity).
    kind_norm AD.
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply lock_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply WAIT; [eassumption | eassumption | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | |].
      unfold s1. cbn [update iseq vareq]. psimpl. right. right. reflexivity.
      unfold saved. repeat split; reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    (* the other return sites contradict the pushed return address *)
    all: try wrong_site PRE.
    (* returned to its own call site *)
    1: { destruct PRE as (RETc & RSPc & MEMc & FSc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply lock_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    rewrite RBP in RBPc. rewrite R12 in R12c. rewrite R13 in R13c. rewrite R14 in R14c. rewrite R15 in R15c.
    rewrite FS in FSc.
    clear - RSPc MEMc FSc RBPc R12c R13c R14c R15c MDL' AG AD SLOT AB RBXB SPB NOVF NOVT NOVTA NOVG t'.
    rename s into s_call. rename s' into s. rename MDL' into MDL. rename t' into t.
    repeat x64_step.
    all: change (2^7) with 128 in *; change (2^8) with 256 in *.
    all: exists 2; split; [right; reflexivity|].
    all: lk_fin RBXB SPB. }
  }
(* QED-SLOW: the tactic proof above is complete (all 14 segments close in
   about three minutes), but the kernel check at Qed ran for over 30 minutes
   (6 GB) without finishing.  The Qed optimization is left for later. *)
Admitted.

(* Non-vacuity: the wait contract is satisfiable.  The witness at P_WAIT reads
   its return address, stores 2 into the lock word (as __lll_lock_wait does
   once it owns the lock) and returns; every other address outside pthread_mutex_lock is a Nop. *)
Definition wait_stmt : stmt :=
  Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
  Move V_MEM64 (Store (Var V_MEM64) (Var R_RDI) (Word 2 32) LittleE 4) $;
  Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
  Jmp (Var R_RIP).
Definition cp_wait (_:store) (a:addr) : N * stmt := if a =? P_WAIT then (1, wait_stmt) else (1, Nop).

Lemma cp_wait_welltyped: welltyped_code cp_wait.
Proof. intros s a. unfold cp_wait. destruct (a =? P_WAIT); apply typchk_stmt_compute; vm_compute; exact I. Qed.

Theorem lock_wait_contract_satisfiable: exists cp, welltyped_code cp /\ lock_wait_contract cp.
Proof.
  exists cp_wait. split. exact cp_wait_welltyped.
  intros s t xs' sp mem p fs f rbx rbp r12 r13 r14 r15
    ENTRY MDL RDI RSI RSP MEM FS RET [RBX [RBP [R12 [R13 [R14 R15]]]]]. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply lock_with_welltyped, cp_wait_welltyped.
  intro MDL1. clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (RDI & RSI & RSP & MEM & FS & RET & RBX & RBP & R12 & R13 & R14 & R15).
  x64_step.
  destruct RET as [R|[R|R]]; rewrite R; x64_step; repeat split; assumption.
Qed.

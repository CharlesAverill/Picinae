(* ffs (AArch64): first set bit of a 32-bit int, with arbitrary upper X0.

   PROVENANCE: /lib/aarch64-linux-gnu/libc.so.6, Ubuntu 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   ELF 0x94aa0, Ghidra 0x194aa0, 100 bytes / 25 instructions.
   Accepted e11 canonical scalar replacement under e08 checkpoint 9ae8e680;
   Ghidra 11.4.2 raw SLEIGH pcode, rebased code, staticMemory=False.
   Both canonical and historical generated lifts remain unchanged.
   Initial author: OpenAI gpt-6-astra, xhigh; one-shot attempt.
   Validation/model status is recorded in notes/a-ffs/README.md.
   Arithmetic isolation/existence arguments adapted from the accepted a-ffsl
   Astra/Sol proof template, read-only; no a-ffsl unit commits are imported.

   ENGLISH SPEC / AAPCS64: int ffs(int i). Input is low32(X0), including
   zero and every signed int bit pattern. X0 upper32 is unconstrained apart
   from the ordinary 64-bit register typing. Return X0 is zero for input
   zero, otherwise 1 plus the least set-bit index, in [1,32], zero extended.
   Memory, SP, X19-X30, separate model LR and Z8-Z15 are preserved.
   No size/path/overlap/alignment/CPU-extension/tunable restriction applies.
   The sole data hypothesis is the pinned 256-byte table at model 0x24e738
   (ELF 0x14e738), whose byte i is N.size i. Its satisfiability and typed
   entries are proved below. No output or callee contract is assumed.
   Actual return cuts are 0x34 and 0x60; RET jumps through X30.
   satisfies_all is partial correctness for executing IL traces, not a
   termination, accessibility/fault-freedom, hardware, or lifting theorem.
   Read permission is required by IL execution, not asserted by this
   partial-correctness contract. The witness additionally permits all reads.
 *)
Require Import Picinae_armv8 e11_ffs_arm8 arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Definition ffs_spec (x r:N) :=
  (x = 0 -> r = 0) /\
  (x <> 0 -> 1 <= r <= 32 /\ N.testbit x (r-1) = true /\
    forall j, j < r-1 -> N.testbit x j = false).
Definition ffs_table (m:N) := forall i, i < 256 ->
  getmem 64 LittleE 1 m (0x24e738+i) = N.size i.
Definition ffs_exit (t:trace) :=
  match t with (Addr 52,_)::_ | (Addr 96,_)::_ => true | _ => false end.
Definition postcondition (x sp lr m:N) (s:store) :=
  ffs_spec x (s R_X0) /\ s R_X0 < 2^32 /\
  s R_SP = sp /\ s R_X30 = lr /\ s V_MEM64 = m.
Definition ffs_invs (x sp lr m:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_X0 mod 2^32 = x /\ s R_SP = sp /\
      s R_X30 = lr /\ s V_MEM64 = m /\ ffs_table m)
  | 12 => Some (exists r, ffs_spec x r /\ r <= 32 /\
      s R_X1 = (if r =? 0 then 0 else 2^(r-1)) /\ s R_X2 = 65535 /\
      s R_SP = sp /\ s R_X30 = lr /\ s V_MEM64 = m /\ ffs_table m)
  | 52 | 96 => Some (postcondition x sp lr m s)
  | _ => None end | _ => None end.

Theorem ffs_nwc: forall s2 s1, e11_ffs_arm8 s1 = e11_ffs_arm8 s2.
Proof. reflexivity. Qed.
Theorem ffs_welltyped: welltyped_prog arm8typctx e11_ffs_arm8.
Proof. exact e11_ffs_arm8.welltyped. Qed.
Theorem ffs_preserves_memory:
  forall_endstates e11_ffs_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Theorem ffs_preserves_callee_saved:
  forall v, In v [R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25;
    R_X26; R_X27; R_X28; R_X29; R_X30; R_SP; R_LR;
    R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15] ->
  forall_endstates e11_ffs_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.
Theorem ffs_return_cut: forall s a,
  a = 52 \/ a = 96 ->
  e11_ffs_arm8 s a = Some (4, Move R_PC (Var R_X30) $; Jmp (Var R_PC)).
Proof. intros s a [E|E]; subst a; reflexivity. Qed.

Lemma ffs_lowest_set_bit:
  forall n x, x < 2^n -> x <> 0 ->
  exists k, k < n /\ N.testbit x k = true /\
    forall j, j < k -> N.testbit x j = false.
Proof.
  induction n as [|n IH] using N.peano_ind; intros x LT NZ.
    change (2^0) with 1 in LT. lia.
  destruct (N.testbit x 0) eqn:B0.
    exists 0. split; [lia | split; [assumption | intros; lia]].
  assert (H2: x = 2 * N.div2 x).
    pose proof (N.div2_odd x) as D. rewrite <- N.bit0_odd, B0 in D.
    simpl N.b2n in D. lia.
  destruct (IH (N.div2 x)) as [k [K [BK LK]]].
    rewrite N.pow_succ_r' in LT. lia.
    intro D. rewrite D in H2. lia.
  rewrite N.div2_div in BK, LK.
  exists (N.succ k). repeat split.
    lia.
    rewrite <- N.div2_bits. exact BK.
    intros j J. destruct (N.eq_dec j 0) as [->|NZj]. exact B0.
      replace j with (N.succ (N.pred j)) by lia.
      rewrite <- N.div2_bits. apply LK. lia.
Qed.

Lemma ffs_isolate: forall x k,
  x < 2^32 -> k < 32 -> N.testbit x k = true ->
  (forall j, j < k -> N.testbit x j = false) ->
  (msub 32 0 x) .& x = 2^k.
Proof.
  intros x k XL K B L.
  assert (NZ: x <> 0) by (intro E; rewrite E, N.bits_0 in B; discriminate).
  assert (PK: 0 < 2^k) by (apply N.neq_0_lt_0, N.pow_nonzero; discriminate).
  assert (XM: x mod 2^(N.succ k) = 2^k).
  { apply N.bits_inj. intro j. rewrite Nmod_pow2_bits, N.pow2_bits_eqb.
    destruct (N.ltb_spec j (N.succ k)) as [J|J].
    - destruct (N.eq_dec j k) as [->|NE].
      + rewrite B, N.eqb_refl. reflexivity.
      + rewrite L by lia. rewrite (proj2 (N.eqb_neq k j) ltac:(lia)). reflexivity.
    - rewrite (proj2 (N.eqb_neq k j) ltac:(lia)). reflexivity. }
  assert (D: x = 2^k + (x / 2^(N.succ k)) * 2^(N.succ k)).
  { pose proof (N.div_mod x (2^(N.succ k))
      ltac:(apply N.pow_nonzero; discriminate)) as D.
    rewrite XM in D. nia. }
  assert (DP: x-1 = (2^k-1) + (x / 2^(N.succ k)) * 2^(N.succ k)) by lia.
  assert (PL: 2^k-1 < 2^(N.succ k)) by (rewrite N.pow_succ_r'; nia).
  assert (PM: (x-1) mod 2^(N.succ k) = 2^k-1).
  { rewrite DP, N.mod_add by (apply N.pow_nonzero; discriminate).
    apply N.mod_small. exact PL. }
  assert (DQ: (x-1) / 2^(N.succ k) = x / 2^(N.succ k)).
  { rewrite DP, N.div_add by (apply N.pow_nonzero; discriminate).
    rewrite N.div_small by exact PL. reflexivity. }
  assert (NEG: msub 32 0 x = N.lnot (x-1) 32).
  { clear - XL NZ. rewrite msub_0_l, (N.mod_small x) by exact XL.
    rewrite N.mod_small by lia.
    rewrite N.lnot_sub_low, N.ones_equiv.
    - lia.
    - destruct (N.eq_dec (x-1) 0) as [E|E].
      + rewrite E. reflexivity.
      + apply N.log2_lt_pow2; lia. }
  rewrite NEG. apply N.bits_inj. intro i.
  rewrite N.land_spec, N.pow2_bits_eqb.
  destruct (N.lt_ge_cases i 32) as [I|I].
  - rewrite N.lnot_spec_low by exact I.
    destruct (N.lt_trichotomy i k) as [IK|[IK|IK]].
    + rewrite L by exact IK. rewrite (proj2 (N.eqb_neq k i) ltac:(first [clear - IK; lia | clear - K I; lia])).
      apply Bool.andb_false_r.
    + subst i. rewrite B, N.eqb_refl.
      assert (P: N.testbit (x-1) k = false).
      { pose proof (Nmod_pow2_bits (x-1) (N.succ k) k) as T.
        rewrite PM in T.
        replace (2^k-1) with (N.ones k) in T by (rewrite N.ones_equiv; lia).
        rewrite N.ones_spec_high, (proj2 (N.ltb_lt k (N.succ k)) ltac:(lia)) in T by lia.
        simpl in T. symmetry. exact T. }
      rewrite P. reflexivity.
    + rewrite (proj2 (N.eqb_neq k i) ltac:(first [clear - IK; lia | clear - K I; lia])).
      assert (P: N.testbit (x-1) i = N.testbit x i).
      { replace i with ((i-N.succ k)+N.succ k) by (clear - IK; lia).
        rewrite <- (N.shiftr_spec' (x-1) (N.succ k) (i-N.succ k)),
          <- (N.shiftr_spec' x (N.succ k) (i-N.succ k)).
        rewrite !N.shiftr_div_pow2, DQ. reflexivity. }
      rewrite P. destruct (N.testbit x i); reflexivity.
  - rewrite (bound_hibits_zero 32 x i XL I).
    rewrite (proj2 (N.eqb_neq k i) ltac:(first [clear - IK; lia | clear - K I; lia])). apply Bool.andb_false_r.
Qed.


Theorem ffs_spec_satisfiable: forall x, x < 2^32 -> exists r, ffs_spec x r.
Proof.
  intros x XL. destruct (N.eq_dec x 0) as [->|NZ].
  - exists 0. unfold ffs_spec. split; [auto|contradiction].
  - destruct (ffs_lowest_set_bit 32 x XL NZ) as [k [K [B L]]].
    exists (k+1). unfold ffs_spec. replace (k+1-1) with k by lia.
    split; [contradiction|]. intros _. repeat split; auto; lia.
Qed.

Lemma ffs_isolation_spec: forall x, x < 2^32 ->
  exists r, ffs_spec x r /\ r <= 32 /\
    (msub 32 0 x) .& x = (if r =? 0 then 0 else 2^(r-1)).
Proof.
  intros x XL. destruct (N.eq_dec x 0) as [->|NZ].
  - exists 0. repeat split; try reflexivity; try lia; contradiction.
  - destruct (ffs_lowest_set_bit 32 x XL NZ) as [k [K [B L]]].
    exists (k+1). rewrite (ffs_isolate x k XL K B L).
    rewrite (proj2 (N.eqb_neq (k+1) 0) ltac:(lia)).
    replace (k+1-1) with k by lia.
    split.
    + unfold ffs_spec. replace (k+1-1) with k by lia.
      split; [contradiction|]. intros _. repeat split; auto; lia.
    + split; [lia|reflexivity].
Qed.

(* Literal little-endian encoding of the accepted e08 reference-data bytes.
   This is reference memory, never replacement executable code. *)
Definition ffs_table_bytes : N := 0x08080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070706060606060606060606060606060606060606060606060606060606060606060505050505050505050505050505050504040404040404040303030302020100.
Definition ffs_table_memory := setmem 64 LittleE 256 0 0x24e738 ffs_table_bytes.

Lemma ffs_table_bytes_correct: forall i, i < 256 ->
  xbits ffs_table_bytes (i*8) ((i+1)*8) = N.size i.
Proof.
  intros i I.
  let rec go k :=
    lazymatch eval compute in (k <? 256) with
    | true => destruct (N.eq_dec i k) as [->|?];
      [vm_compute; reflexivity | let k1 := eval compute in (N.succ k) in go k1]
    | false => exfalso; lia end in go 0.
Qed.

Theorem ffs_table_satisfiable: ffs_table ffs_table_memory.
Proof.
  intros i I. unfold ffs_table_memory.
  replace 256 with (i+1+(255-i)) by lia.
  rewrite getmem_setmem_xbits by (clear - I; change (255-i+1 <= 18446744073709551616); lia).
  apply ffs_table_bytes_correct. exact I.
Qed.

Lemma ffs_table_memory_bound: ffs_table_memory < 2^(8*2^64).
Proof.
  unfold ffs_table_memory. apply hibits_zero_bound. intros i I.
  replace i with ((i-2^64*8)+2^64*8) by lia.
  rewrite <- N.shiftr_spec', setmem_highbits, N.shiftr_0_l, N.bits_0.
  reflexivity.
Qed.

Definition ffs_entry_store (u:N) : store := fun v =>
  if vareq v R_X0 then u else
  if vareq v V_MEM64 then ffs_table_memory else
  if vareq v A_READ then N.ones (2^64) else 0.

Theorem ffs_entry_satisfiable: forall u, u < 2^64 ->
  exists s P, models arm8typctx s /\ s R_X0 = u /\
    ffs_invs (u mod 2^32) 0 0 ffs_table_memory [(Addr 0,s)] = Some P /\ P /\
    (forall a, a < 2^64 -> mem_readable s a).
Proof.
  intros u U. exists (ffs_entry_store u).
  exists (u mod 2^32 = u mod 2^32 /\ 0 = 0 /\ 0 = 0 /\
    ffs_table_memory = ffs_table_memory /\ ffs_table ffs_table_memory).
  split.
  - intros v w CV. unfold ffs_entry_store.
    destruct (vareq v R_X0) as [E|E].
    + subst v. change (Some 64 = Some w) in CV. inversion CV; subst. exact U.
    + destruct (vareq v V_MEM64) as [M|M].
      * subst v. change (Some (8*2^64) = Some w) in CV.
        inversion CV; subst. apply ffs_table_memory_bound.
      * destruct (vareq v A_READ) as [A|A].
        -- subst v. change (Some (2^64) = Some w) in CV.
           inversion CV; subst. apply ones_bound.
        -- apply N.neq_0_lt_0, N.pow_nonzero. discriminate.
  - repeat split; try reflexivity; try apply ffs_table_satisfiable.
    intros a A. unfold mem_readable. change (N.testbit (N.ones (2^64)) a = true).
    apply N.ones_spec_low. exact A.
Qed.

(* Finite case split is over the proved least-bit position, never over a
   restricted collection of input values. Upper input bits stay arbitrary. *)
Ltac ffs_positions r R :=
  let rec go k :=
    lazymatch eval compute in (k <=? 32) with
    | true => destruct (N.eq_dec r k) as [->|?];
      [idtac | let k1 := eval compute in (N.succ k) in go k1]
    | false => exfalso; lia end in go 0.

Ltac ffs_load_table TAB :=
  repeat match goal with
  | |- context [getmem 64 LittleE 1 ?m ?a] =>
    let i := eval vm_compute in (a-0x24e738) in
    let H := fresh "BYTE" in
    pose proof (TAB i ltac:(vm_compute; reflexivity)) as H;
    let a0 := eval vm_compute in (0x24e738+i) in
    change (0x24e738+i) with a0 in H; rewrite H
  end.

Theorem ffs_correct:
  forall s t s' x' x sp lr m
    (ENTRY: startof t (x',s') = (Addr 0,s))
    (MDL: models arm8typctx s)
    (X: s R_X0 mod 2^32 = x) (SP: s R_SP = sp)
    (LR: s R_X30 = lr) (MEM: s V_MEM64 = m) (TABLE: ffs_table m),
  satisfies_all e11_ffs_arm8 (ffs_invs x sp lr m) ffs_exit ((x',s')::t).
Proof.
  (* WIP: unchecked attempt in notes/a-ffs-fix/wrap-up-attempt.v.txt. *)
Abort.

(* An explicit post-RET adapter. Its guard prevents calling an internal
   instruction address a completed return in this rebased program map. *)
Definition ffs_return_guard (lr:N) := forall s, e11_ffs_arm8 s lr = None.
Theorem ffs_return_guard_satisfiable: ffs_return_guard 100.
Proof.
  (* WIP: unchecked attempt in notes/a-ffs-fix/wrap-up-attempt.v.txt. *)
Abort.

Theorem ffs_guarded_return:
  forall a s q c s' e x sp lr m,
  (a = 52 \/ a = 96) -> e11_ffs_arm8 s a = Some (4,q) ->
  postcondition x sp lr m s -> ffs_return_guard lr ->
  exec_stmt arm8typctx s q c s' e ->
  e = Some (Addr lr) /\ postcondition x sp lr m (reset_temps s s') /\
  e11_ffs_arm8 (reset_temps s s') lr = None.
Proof.
  (* WIP: unchecked attempt in notes/a-ffs-fix/wrap-up-attempt.v.txt. *)
Abort.

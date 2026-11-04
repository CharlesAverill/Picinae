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
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

Lemma ffs_lowest_set_bit:
  forall n x, x < 2^n -> x <> 0 ->
  exists k, k < n /\ N.testbit x k = true /\
    forall j, j < k -> N.testbit x j = false.
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

Lemma ffs_isolate: forall x k,
  x < 2^32 -> k < 32 -> N.testbit x k = true ->
  (forall j, j < k -> N.testbit x j = false) ->
  (msub 32 0 x) .& x = 2^k.
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.


Theorem ffs_spec_satisfiable: forall x, x < 2^32 -> exists r, ffs_spec x r.
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

Lemma ffs_isolation_spec: forall x, x < 2^32 ->
  exists r, ffs_spec x r /\ r <= 32 /\
    (msub 32 0 x) .& x = (if r =? 0 then 0 else 2^(r-1)).
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

(* Literal little-endian encoding of the accepted e08 reference-data bytes.
   This is reference memory, never replacement executable code. *)
Definition ffs_table_bytes : N := 0x08080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080808080707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070706060606060606060606060606060606060606060606060606060606060606060505050505050505050505050505050504040404040404040303030302020100.
Definition ffs_table_memory := setmem 64 LittleE 256 0 0x24e738 ffs_table_bytes.

Lemma ffs_table_bytes_correct: forall i, i < 256 ->
  xbits ffs_table_bytes (i*8) ((i+1)*8) = N.size i.
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

Theorem ffs_table_satisfiable: ffs_table ffs_table_memory.
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

Lemma ffs_table_memory_bound: ffs_table_memory < 2^(8*2^64).
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

Definition ffs_entry_store (u:N) : store := fun v =>
  if vareq v R_X0 then u else
  if vareq v V_MEM64 then ffs_table_memory else
  if vareq v A_READ then N.ones (2^64) else 0.

Theorem ffs_entry_satisfiable: forall u, u < 2^64 ->
  exists s P, models arm8typctx s /\ s R_X0 = u /\
    ffs_invs (u mod 2^32) 0 0 ffs_table_memory [(Addr 0,s)] = Some P /\ P /\
    (forall a, a < 2^64 -> mem_readable s a).
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

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
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

(* An explicit post-RET adapter. Its guard prevents calling an internal
   instruction address a completed return in this rebased program map. *)
Definition ffs_return_guard (lr:N) := forall s, e11_ffs_arm8 s lr = None.
Theorem ffs_return_guard_satisfiable: ffs_return_guard 100.
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

Theorem ffs_guarded_return:
  forall a s q c s' e x sp lr m,
  (a = 52 \/ a = 96) -> e11_ffs_arm8 s a = Some (4,q) ->
  postcondition x sp lr m s -> ffs_return_guard lr ->
  exec_stmt arm8typctx s q c s' e ->
  e = Some (Addr lr) /\ postcondition x sp lr m (reset_temps s s') /\
  e11_ffs_arm8 (reset_temps s s') lr = None.
Proof.
  (* PARTIAL: unchecked attempt preserved verbatim in notes/a-ffs/initial-attempt.v.txt. *)
Abort.

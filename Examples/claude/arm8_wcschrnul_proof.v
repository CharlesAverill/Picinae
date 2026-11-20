(* wcschrnul -- first matching or zero 32-bit wide character (AArch64).

   PROVENANCE: Ubuntu glibc 2.35-0ubuntu3.15, aarch64 libc.so.6 SHA256
   79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   ELF entry 0x9e4c0; Ghidra image base 0x100000; IL entry 0x19e4c0.
   The unchanged e30_wcschrnul_arm8 map contains all nine instructions,
   extracted by the reviewed e30 strict scalar CCMP pipeline (Ghidra 11.4.2).
   Its manifest and raw pcode remain beside the generated file.
   Initial author: OpenAI gpt-6-astra, xhigh, one-shot proof attempt.
   Proof status and final proof producer: see notes/a-wcschrnul/README.md.

   ENGLISH SPEC / ABI: X0=p, W1=c (low 32 bits of X1), X30=lr, SP=sp.
   A wchar_t is four little-endian bytes; pointers are 64 bits. K is the
   least index whose word equals c or zero. All earlier words differ from
   both. Every byte through the entire stop word is readable and
   p + 4*(K+1) <= 2^64. There is no alignment, signed-wchar positivity,
   CPU-feature, tunable, nonoverlap, or disjoint-code/data hypothesis.
   Input is read-only; aliasing the stack or code is harmless in this IL.
   At RET, X0=p+4*K; memory, SP, X30, X1, X19-X29 and Z8-Z15 are unchanged.
   A separate RET lemma specifies the ordinary jump to X30 and its frame.

   SCOPE: partial correctness of this complete scalar IL map. No assertion
   of termination, hardware fault freedom, concurrency, or verified
   machine-byte-to-IL refinement. Readability is expressed using the model's
   actual A_READ bitmap. Arbitrarily aligned loads are allowed by this IL;
   applying this to hardware needs an environment allowing those loads.
   No callee contracts are assumed. The inherited lifter remains trusted.
 *)
Require Import Picinae_armv8.
Require Import e30_wcschrnul_arm8.
Import ARM8Notations.
From Stdlib Require Import NArith Lia List.
Import ListNotations.
Open Scope N.

Definition wcschrnul_stop (m:memory) (p c k:N) : Prop :=
  (forall i, i < k -> m Ⓓ[p+4*i] <> c /\ m Ⓓ[p+4*i] <> 0) /\
  (m Ⓓ[p+4*k] = c \/ m Ⓓ[p+4*k] = 0).

Definition wcschrnul_input (s:store) (m:memory) (p c k sp lr:N) : Prop :=
  s V_MEM64 = m /\ s R_X0 = p /\ s R_X1 mod 2^32 = c /\
  s R_SP = sp /\ s R_X30 = lr /\
  p + 4*(k+1) <= 2^64 /\
  (forall j, j < 4*(k+1) -> mem_readable s (p+j)) /\
  wcschrnul_stop m p c k.

Definition wcschrnul_state (m:memory) (c sp lr:N) (s:store) :=
  s V_MEM64 = m /\ s R_X1 mod 2^32 = c /\ s R_SP = sp /\ s R_X30 = lr.

Definition postcondition (m:memory) (p c k sp lr:N) (s:store) :=
  wcschrnul_state m c sp lr s /\ s R_X0 = p+4*k.

Definition wcschrnul_exit (t:trace) :=
  match t with (Addr 0x19e4e0,_)::_ => true | _ => false end.

Definition wcschrnul_check (m:memory) (p c k sp lr:N) (s:store) :=
  wcschrnul_state m c sp lr s /\
  exists i, i <= k /\ s R_X0 = p+4*i /\ s R_X2 = m Ⓓ[p+4*i].

Definition wcschrnul_invs (m:memory) (p c k sp lr:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x19e4c0 => Some (wcschrnul_state m c sp lr s /\ s R_X0 = p)
  | 0x19e4c4 | 0x19e4d4 => Some (wcschrnul_check m p c k sp lr s)
  | 0x19e4d0 => Some (wcschrnul_state m c sp lr s /\
                       exists i, i < k /\ s R_X0 = p+4*i)
  | 0x19e4e0 => Some (postcondition m p c k sp lr s)
  | _ => None
  end | _ => None end.

Theorem wcschrnul_nwc: forall s2 s1,
  e30_wcschrnul_arm8 s1 = e30_wcschrnul_arm8 s2.
Proof. reflexivity. Qed.

Theorem wcschrnul_welltyped: welltyped_prog arm8typctx e30_wcschrnul_arm8.
Proof. exact e30_wcschrnul_arm8.welltyped. Qed.

Theorem wcschrnul_preserves_memory:
  forall_endstates e30_wcschrnul_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wcschrnul_preserves_callee_saved:
  forall v, In v [R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25;
                  R_X26; R_X27; R_X28; R_X29; R_X30; R_SP;
                  R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15;
                  A_READ; A_WRITE; R_X1] ->
  forall_endstates e30_wcschrnul_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Lemma wcschrnul_stop_hit: forall m p c k i,
  wcschrnul_stop m p c k -> i <= k ->
  (m Ⓓ[p+4*i] = 0 \/ m Ⓓ[p+4*i] = c) -> i = k.
Proof.
  intros m p c k i [BEFORE STOP] LE HIT.
  destruct (N.lt_ge_cases i k) as [LT|GE].
  - destruct (BEFORE i LT) as [NC NZ]. destruct HIT; contradiction.
  - clear - LE GE. lia.
Qed.

Lemma wcschrnul_stop_miss: forall m p c k i,
  wcschrnul_stop m p c k -> i <= k ->
  m Ⓓ[p+4*i] <> 0 -> m Ⓓ[p+4*i] <> c -> i < k.
Proof.
  intros m p c k i [BEFORE STOP] LE NZ NC.
  destruct (N.eq_dec i k) as [E|NE].
  - subst i. destruct STOP; contradiction.
  - clear - LE NE. lia.
Qed.

Lemma wcschrnul_addr_bound: forall p k i,
  p+4*(k+1) <= 2^64 -> i <= k -> p+4*i < 2^64.
Proof. intros. lia. Qed.

(* No sign restriction: modulo subtraction detects equality of all 32 bits. *)
Lemma wcschrnul_eq32: forall a b,
  a < 2^32 -> b < 2^32 -> (msub 32 a b =? 0) = (a =? b).
Proof.
  intros a b A B. destruct (N.eqb_spec a b) as [E|NE].
  - subst b. rewrite msub_diag. reflexivity.
  - apply N.eqb_neq. intro H. apply msub_move_0_r in H.
    rewrite (N.mod_small a), (N.mod_small b) in H by assumption.
    contradiction.
Qed.

(* A concrete readable, typed, unaligned empty string for every character
   bit pattern. This witnesses the entire input, not merely its stop clause. *)
Definition wcschrnul_witness (c:N) : store := fun v =>
  match v with R_X0 => 1 | R_X1 => c mod 2^32 | A_READ => 30 | _ => 0 end.

Theorem wcschrnul_input_satisfiable: forall c,
  models arm8typctx (wcschrnul_witness c) /\
  wcschrnul_input (wcschrnul_witness c) 0 1 (c mod 2^32) 0 0 0.
(* PARTIAL: exact initial proof is archived in notes/a-wcschrnul/initial-attempt.v.txt. *)
Abort.

Theorem wcschrnul_correct:
  forall s t s' x' m p c k sp lr
    (ENTRY: startof t (x',s') = (Addr 0x19e4c0,s))
    (MDL: models arm8typctx s)
    (INPUT: wcschrnul_input s m p c k sp lr),
  satisfies_all e30_wcschrnul_arm8 (wcschrnul_invs m p c k sp lr)
    wcschrnul_exit ((x',s')::t).
(* PARTIAL: exact initial proof is archived in notes/a-wcschrnul/initial-attempt.v.txt. *)
Abort.

(* Ordinary RET, independent of the scan proof and without a callee oracle.
   The exact instruction is the unchanged map lookup at the unique exit. *)
Theorem wcschrnul_return:
  forall s q ct s' x m p c k sp lr,
  e30_wcschrnul_arm8 s 0x19e4e0 = Some (4,q) ->
  models arm8typctx s -> postcondition m p c k sp lr s ->
  exec_stmt arm8typctx s q ct s' x ->
  x = Some (Addr lr) /\ postcondition m p c k sp lr (reset_temps s s').
(* PARTIAL: exact initial proof is archived in notes/a-wcschrnul/initial-attempt.v.txt. *)
Abort.

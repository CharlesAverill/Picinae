(* wcschrnul -- first matching or zero 32-bit wide character (AArch64).

   PROVENANCE: Ubuntu glibc 2.35-0ubuntu3.15, aarch64 libc.so.6 SHA256
   79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   ELF entry 0x9e4c0; Ghidra image base 0x100000; IL entry 0x19e4c0.
   The unchanged e30_wcschrnul_arm8 map contains all nine instructions,
   extracted by the reviewed e30 strict scalar CCMP pipeline (Ghidra 11.4.2).
   Its manifest and raw pcode remain beside the generated file.
   Initial author: OpenAI gpt-6-astra, xhigh, one-shot proof attempt.
   Proof repair and final proof producer: OpenAI gpt-6.1-sol, xhigh.
   Kernel-check evidence and scope: notes/a-wcschrnul-fix/README.md.
   Original one-shot evidence: notes/a-wcschrnul/README.md.

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
Proof.
  intro c. split.
  - intros v w T. destruct v; inversion T; subst w;
      cbn [wcschrnul_witness];
      try (apply N.neq_0_lt_0; apply N.pow_nonzero; discriminate);
      try (change (1 < 18446744073709551616); lia);
      try (change (30 < 2^(2^64));
           eapply N.lt_le_trans with (m:=2^5); [reflexivity|];
           apply N.pow_le_mono_r; lia).
    eapply N.lt_le_trans. apply N.mod_lt. discriminate.
    apply N.pow_le_mono_r; lia.
  - unfold wcschrnul_input, wcschrnul_stop.
    cbn [wcschrnul_witness].
    rewrite N.mod_mod by discriminate.
    repeat split; try reflexivity; try (intros; lia).
    + intros j J. assert (j=0 \/ j=1 \/ j=2 \/ j=3) by lia.
      destruct H as [E|[E|[E|E]]]; subst j; reflexivity.
    + right. reflexivity.
Qed.

(* Branch normalization operates on abstract words, never on memory syntax. *)
Ltac wcschrnul_branches :=
  repeat match goal with
  | H: (?a =? ?b) = true |- _ => apply N.eqb_eq in H
  | H: (?a =? ?b) = false |- _ => apply N.eqb_neq in H
  | H: negb ?b = true |- _ => apply Bool.negb_true_iff in H
  | H: negb ?b = false |- _ => apply Bool.negb_false_iff in H
  end.

Ltac wcschrnul_finish i k w C WB HIT MISS :=
  cbn [wcschrnul_state postcondition] in *;
  try rewrite C in *;
  try rewrite (N.mod_small w 4294967296) in * by exact WB;
  try rewrite wcschrnul_eq32 in * by assumption;
  wcschrnul_branches;
  first
  [ assert (IK: i=k) by (apply HIT; intuition congruence);
    subst i; repeat split; assumption
  | split; [repeat split; assumption|];
    exists i; split; [apply MISS; congruence|assumption] ].

Theorem wcschrnul_correct:
  forall s t s' x' m p c k sp lr
    (ENTRY: startof t (x',s') = (Addr 0x19e4c0,s))
    (MDL: models arm8typctx s)
    (INPUT: wcschrnul_input s m p c k sp lr),
  satisfies_all e30_wcschrnul_arm8 (wcschrnul_invs m p c k sp lr)
    wcschrnul_exit ((x',s')::t).
Proof.
  intros s t s' x' m p c k sp lr ENTRY MDL
    [MEM [P [C [SP [LR [RANGE [READ STOP]]]]]]].
  apply prove_invs.
  - simpl. rewrite ENTRY. arm8_step. unfold wcschrnul_state.
    repeat split; assumption.
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
    apply wcschrnul_welltyped. intro MDL1.
    clear - PRE MDL1 STOP RANGE. rename t1 into t.
    destruct_inv 64 PRE.
    + destruct PRE as [[MEM [C [SP LR]]] P].
      repeat arm8_step.
      split; [repeat split; assumption|].
      exists 0. rewrite N.mul_0_r, N.add_0_r.
      repeat split; try assumption; try reflexivity. apply N.le_0_l.
    + destruct PRE as [[MEM [C [SP LR]]] [i [LE [P X2]]]].
      remember (m Ⓓ[p+4*i]) as w eqn:W in *.
      assert (WB: w < 2^32) by (rewrite W; apply getmem_bound).
      assert (CB: c < 2^32) by (rewrite <- C; apply N.mod_lt; discriminate).
      assert (HIT: w=0 \/ w=c -> i=k).
      { rewrite W. apply wcschrnul_stop_hit; assumption. }
      assert (MISS: w<>0 -> w<>c -> i<k).
      { rewrite W. apply wcschrnul_stop_miss; assumption. }
      clear STOP RANGE W.
      repeat arm8_step; wcschrnul_finish i k w C WB HIT MISS.
    + destruct PRE as [[MEM [C [SP LR]]] [i [LT P]]].
      assert (NEXT: p+4*(i+1) < 2^64).
      { apply (wcschrnul_addr_bound p k (i+1) RANGE). clear - LT. lia. }
      assert (ADD: (4+p+4*i) mod 2^64 = p+4*(i+1)).
      { replace (4+p+4*i) with (p+4*(i+1)) by lia.
        apply N.mod_small. exact NEXT. }
      repeat arm8_step.
      split; [repeat split; assumption|]. exists (i+1).
      split; [clear - LT; lia|].
      rewrite <- ADD. split; [reflexivity|].
      rewrite getmem_mod_l. reflexivity.
    + destruct PRE as [[MEM [C [SP LR]]] [i [LE [P X2]]]].
      remember (m Ⓓ[p+4*i]) as w eqn:W in *.
      assert (WB: w < 2^32) by (rewrite W; apply getmem_bound).
      assert (CB: c < 2^32) by (rewrite <- C; apply N.mod_lt; discriminate).
      assert (HIT: w=0 \/ w=c -> i=k).
      { rewrite W. apply wcschrnul_stop_hit; assumption. }
      assert (MISS: w<>0 -> w<>c -> i<k).
      { rewrite W. apply wcschrnul_stop_miss; assumption. }
      clear STOP RANGE W.
      repeat arm8_step; wcschrnul_finish i k w C WB HIT MISS.
Qed.

(* Ordinary RET, independent of the scan proof and without a callee oracle.
   The exact instruction is the unchanged map lookup at the unique exit. *)
Theorem wcschrnul_return:
  forall s q ct s' x m p c k sp lr,
  e30_wcschrnul_arm8 s 0x19e4e0 = Some (4,q) ->
  models arm8typctx s -> postcondition m p c k sp lr s ->
  exec_stmt arm8typctx s q ct s' x ->
  x = Some (Addr lr) /\ postcondition m p c k sp lr (reset_temps s s').
Proof.
  intros s q ct s' x m p c k sp lr LOOK MDL [[MEM [C [SP LR]]] RESULT] XS.
  cbn [e30_wcschrnul_arm8] in LOOK. injection LOOK as Q. subst q.
  step_stmt XS. arm8_psimpl in XS.
  destruct XS as [[STATE EXIT] _]. split; [exact EXIT|].
  rewrite STATE. unfold postcondition, wcschrnul_state.
  repeat split; assumption.
Qed.

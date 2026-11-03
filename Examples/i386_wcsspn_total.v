(* Total correctness of the i386 nested wide-character scans.
   The original partial-correctness proof is imported unchanged. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import i386_total_helpers i386_wcsspn i386_wcsspn_proof.
Import X86Notations.
Open Scope N.

(* The specification deliberately uses memory after the callee frame is
   written.  Only the terminators need to be disjoint from that frame for
   termination; earlier characters may change and are interpreted by the
   original postcondition in the resulting memory. *)
Definition wcsspn_nil_string (m:memory) p len :=
  (forall i, i < len -> m Ⓓ[p+4*i] <> 0) /\ m Ⓓ[p+4*len] = 0.

Theorem wcsspn_preserves_readable:
  forall_endstates wcsspn_i386 (fun _ s _ s' => s A_READ = s' A_READ).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem wcsspn_preserves_writable:
  forall_endstates wcsspn_i386 (fun _ s _ s' => s A_WRITE = s' A_WRITE).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Section TotalCorrectness.
  Variable s0 : store.
  Hypothesis MDL0: models x86typctx s0.
  Hypothesis READ0: forall a, a < 2^32 -> mem_readable s0 a.
  Hypothesis WRITE0: forall a, a < 2^32 -> mem_writable s0 a.

  Definition wcsspn_done t := wcsspn_exit t = true /\
    execution_context wcsspn_i386 wcsspn_exit (Addr 0,s0) t.

  Ltac total_memory ::= unfold MemAcc, mem_readable, mem_writable in *; intros;
    psimpl; match goal with H: forall a, a < 2^32 -> N.testbit _ a = true |- _ =>
      apply H; apply N.mod_lt; discriminate end.
  Local Ltac step := ISA_total_step.
  Local Ltac done := total_here; reflexivity.
  Local Ltac readable := unfold mem_readable in *; intros; psimpl;
    match goal with H: forall a, a < 2^32 -> N.testbit _ a = true |- _ => apply H; assumption end.

  Lemma wcsspn_pop_terminates:
    forall a s hist (AT: a = 61 \/ a = 82)
      (READ: forall a, a < 2^32 -> mem_readable s a),
    eventually wcsspn_i386 (fun t => wcsspn_exit t = true) ((Addr a,s)::hist).
  Proof.
    intros a s hist AT READ.
    destruct AT as [AT|AT]; subst a; do 4 step; done.
  Qed.

  (* The inner scan finishes at a nil wide character or at a match.  CONT is
     a proof for the finite continuation at 72, not a termination assumption
     in the public theorem.  The outer induction below constructs it. *)
  Lemma wcsspn_inner_terminates:
    forall m len2 (NIL: m Ⓓ[p2 s0+4*len2] = 0) k
      (CONT: forall s hist,
        s V_MEM32 = m -> s R_EDI = p1 s0 -> s R_EBP = p2 s0 ->
        s R_ESI = m Ⓓ[p2 s0] -> s R_EAX = k ->
        (forall a, a < 2^32 -> mem_readable s a) ->
        eventually wcsspn_i386 (fun t => wcsspn_exit t = true) ((Addr 72,s)::hist)),
    forall j s hist (BOUND: j < len2)
      (MEM: s V_MEM32 = m) (EDI: s R_EDI = p1 s0) (EBP: s R_EBP = p2 s0)
      (ESI: s R_ESI = m Ⓓ[p2 s0]) (EAX: s R_EAX = k)
      (EDX: s R_EDX = p2 s0 ⊕ (4*j))
      (READ: forall a, a < 2^32 -> mem_readable s a),
    eventually wcsspn_i386 (fun t => wcsspn_exit t = true) ((Addr 52,s)::hist).
  Proof.
    intros m len2 NIL k CONT.
    assert (LOOP: forall n j s hist, len2-j = n -> j < len2 ->
      s V_MEM32 = m -> s R_EDI = p1 s0 -> s R_EBP = p2 s0 ->
      s R_ESI = m Ⓓ[p2 s0] -> s R_EAX = k -> s R_EDX = p2 s0 ⊕ (4*j) ->
      (forall a, a < 2^32 -> mem_readable s a) ->
      eventually wcsspn_i386 (fun t => wcsspn_exit t = true) ((Addr 52,s)::hist)).
    { intro n. induction n using (well_founded_induction N.lt_wf_0).
      intros j s hist REM BOUND MEM EDI EBP ESI EAX EDX READ.
      do 4 step.
      - eapply wcsspn_pop_terminates. left. reflexivity. all: try assumption. all: try readable.
      - do 2 step.
        + eapply CONT; try (psimpl; reflexivity); try assumption. all: try assumption. all: try readable.
        + assert (JL: j+1 < len2).
          { apply N.eqb_neq in BC. destruct (N.eq_dec (j+1) len2).
              rewrite <- e in NIL. rewrite N.mul_add_distr_l in NIL. psimpl in NIL. congruence.
              lia. }
          eapply H with (y:=len2-(j+1)) (j:=j+1).
          all: try lia.
          all: try (rewrite N.mul_add_distr_l; psimpl; reflexivity).
          all: try (psimpl; assumption || reflexivity).
          all: try assumption. all: try readable.
    }
    intros. eapply LOOP; eassumption || reflexivity.
  Qed.

  Lemma wcsspn_outer_terminates:
    forall m len1 len2
      (LEN: len1 < 2^32)
      (NIL1: m Ⓓ[p1 s0+4*len1] = 0)
      (NIL2: m Ⓓ[p2 s0+4*len2] = 0)
      k s hist (BOUND: k < len1)
      (MEM: s V_MEM32 = m) (EDI: s R_EDI = p1 s0) (EBP: s R_EBP = p2 s0)
      (ESI: s R_ESI = m Ⓓ[p2 s0]) (EAX: s R_EAX = k)
      (READ: forall a, a < 2^32 -> mem_readable s a),
    eventually wcsspn_i386 (fun t => wcsspn_exit t = true) ((Addr 32,s)::hist).
  Proof.
    intros m len1 len2 LEN NIL1 NIL2.
    assert (LOOP: forall n k s hist, len1-k = n -> k < len1 ->
      s V_MEM32 = m -> s R_EDI = p1 s0 -> s R_EBP = p2 s0 ->
      s R_ESI = m Ⓓ[p2 s0] -> s R_EAX = k ->
      (forall a, a < 2^32 -> mem_readable s a) ->
      eventually wcsspn_i386 (fun t => wcsspn_exit t = true) ((Addr 32,s)::hist)).
    { intro n. induction n using (well_founded_induction N.lt_wf_0).
      intros k s hist REM BOUND MEM EDI EBP ESI EAX READ.
      assert (ADV: forall s hist,
        s V_MEM32 = m -> s R_EDI = p1 s0 -> s R_EBP = p2 s0 ->
        s R_ESI = m Ⓓ[p2 s0] -> s R_EAX = k ->
        (forall a, a < 2^32 -> mem_readable s a) ->
        eventually wcsspn_i386 (fun t => wcsspn_exit t = true) ((Addr 72,s)::hist)).
      { intros st tail MEM' EDI' EBP' ESI' EAX' READ2.
        assert (KMOD: 1 ⊕ k = k+1) by
          (change ((1+k) mod 2^32 = k+1); rewrite N.mod_small by lia; lia).
        do 4 step.
        - eapply wcsspn_pop_terminates. right. reflexivity. all: try assumption. all: try readable.
        - assert (KL: k+1 < len1).
          { apply N.eqb_neq in BC. rewrite N.shiftl_mul_pow2, N.mul_comm in BC.
            rewrite N.mul_add_distr_l in BC. psimpl in BC. destruct (N.eq_dec (k+1) len1).
              rewrite <- e, N.mul_add_distr_l in NIL1. psimpl in NIL1. congruence.
              lia. }
          eapply H with (y:=len1-(k+1)) (k:=k+1).
          all: try lia.
          all: try (psimpl; assumption || reflexivity).
          all: try (psimpl; exact KMOD).
          all: try assumption. all: try readable.
      }
      do 2 step.
      - eapply wcsspn_pop_terminates. left. reflexivity. all: try assumption. all: try readable.
      - do 2 step.
        + eapply ADV; try (psimpl; reflexivity); try assumption. all: try assumption. all: try readable.
        + do 2 step.
          assert (L2: 0 < len2).
          { apply N.eqb_neq in BC. destruct len2; [psimpl in NIL2; congruence|apply N.neq_0_lt_0; discriminate]. }
          eapply wcsspn_inner_terminates with (len2:=len2) (j:=0) (k:=k) (m:=m).
            exact NIL2. exact ADV. exact L2.
            all: try (psimpl; reflexivity).
            all: try (unfold p2, mem, esp; psimpl; reflexivity).
            all: try assumption. all: try readable.
    }
    intros. eapply LOOP; eassumption || reflexivity.
  Qed.

  Lemma wcsspn_termination:
    forall len1 len2
      (LEN: len1 < 2^32)
      (STRING1: wcsspn_nil_string (mem s0) (p1 s0) len1)
      (STRING2: wcsspn_nil_string (mem s0) (p2 s0) len2)
      (FRAME1: ~overlap 32 (p1 s0+4*len1) 4 (esp s0 ⊖ 16) 16)
      (FRAME2: ~overlap 32 (p2 s0+4*len2) 4 (esp s0 ⊖ 16) 16),
    eventually wcsspn_i386 wcsspn_done ((Addr 0,s0)::nil).
  Proof.
    intros len1 len2 LEN STRING1 STRING2 FRAME1 FRAME2.
    assert (NIL1: forall fb, mem' s0 fb Ⓓ[p1 s0+4*len1] = 0).
    { intro fb. unfold mem'. rewrite getmem_noverlap by exact FRAME1. exact (proj2 STRING1). }
    assert (NIL2: forall fb, mem' s0 fb Ⓓ[p2 s0+4*len2] = 0).
    { intro fb. unfold mem'. rewrite getmem_noverlap by exact FRAME2. exact (proj2 STRING2). }
    apply i386_eventually_context.
    - pose proof MDL0 as MDL1. pose proof READ0 as READ. pose proof WRITE0 as WRITE.
      do 7 step.
      (* Earlier histories retain the shorter frames, so use fresh names
         when merging each additional push into the current 16-byte frame. *)
      generalize_frame (s0 V_MEM32) as fb8.
      generalize_frame (s0 V_MEM32) as fb12.
      generalize_frame (s0 V_MEM32) as fb.
      do 3 step.
      + eapply wcsspn_pop_terminates. left. reflexivity.
        all: try assumption. all: try readable.
      + do 3 step.
        assert (L1: 0 < len1).
        { destruct len1.
            specialize (NIL1 fb). unfold mem', p1, mem, esp in NIL1.
            psimpl in NIL1. apply N.eqb_neq in BC. congruence.
            lia. }
        eapply wcsspn_outer_terminates with (len1:=len1) (len2:=len2) (k:=0) (m:=mem' s0 fb).
          exact LEN. apply NIL1. apply NIL2. exact L1.
          all: try (psimpl; reflexivity).
          all: try (unfold mem', p1, p2, mem, esp; psimpl; reflexivity).
          all: try assumption. all: try readable.
    - split. apply exec_prog_none. split. reflexivity. constructor. reflexivity.
  Qed.

  Theorem wcsspn_total_correctness:
    forall len1 len2
      (LEN: len1 < 2^32)
      (STRING1: wcsspn_nil_string (mem s0) (p1 s0) len1)
      (STRING2: wcsspn_nil_string (mem s0) (p2 s0) len2)
      (FRAME1: ~overlap 32 (p1 s0+4*len1) 4 (esp s0 ⊖ 16) 16)
      (FRAME2: ~overlap 32 (p2 s0+4*len2) 4 (esp s0 ⊖ 16) 16),
    satisfies_total wcsspn_i386 (wcsspn_invs s0) wcsspn_exit ((Addr 0,s0)::nil).
  Proof.
    intros. eapply total_of_partial with (entry:=(Addr 0,s0)).
      intros [|[x s] t] ORIGIN; try discriminate.
      rewrite ostartof_cons in ORIGIN. injection ORIGIN as ENTRY.
      apply wcsspn_correctness; assumption.
      eapply wcsspn_termination; eassumption.
  Qed.

  Corollary wcsspn_terminates:
    forall len1 len2
      (LEN: len1 < 2^32)
      (STRING1: wcsspn_nil_string (mem s0) (p1 s0) len1)
      (STRING2: wcsspn_nil_string (mem s0) (p2 s0) len2)
      (FRAME1: ~overlap 32 (p1 s0+4*len1) 4 (esp s0 ⊖ 16) 16)
      (FRAME2: ~overlap 32 (p2 s0+4*len2) 4 (esp s0 ⊖ 16) 16),
    exists prefix, exec_prog wcsspn_i386 (prefix++(Addr 0,s0)::nil) /\
      exit_post (wcsspn_invs s0) wcsspn_exit (prefix++(Addr 0,s0)::nil).
  Proof.
    intros. apply eventually_reaches.
      eapply wcsspn_total_correctness; eassumption.
      apply exec_prog_none.
  Qed.

End TotalCorrectness.

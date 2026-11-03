(* Total correctness of the i386 byte comparison loop.
   The original partial-correctness proof is imported unchanged. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import i386_total_helpers i386_strcmp i386_strcmp_proof.
Import X86Notations.
Open Scope N.

(* Total correctness.  Memory is read only, so a terminator in the initial
   memory survives every instruction.  Addresses may wrap: the logical byte
   index used below does not wrap.  No bound on the string length is needed. *)
Definition strcmp_nil_string (m:memory) p len :=
  (forall i, i < len -> m Ⓑ[p+i] <> 0) /\ m Ⓑ[p+len] = 0.

Section TotalCorrectness.
  Variable s0 : store.
  Hypothesis MDL0: models x86typctx s0.
  Hypothesis READ0: forall a, a < 2^32 -> mem_readable s0 a.

  Definition strcmp_done t := strcmp_exit t = true /\
    execution_context strcmp_i386 strcmp_exit (Addr 0,s0) t.

  Ltac total_memory ::= unfold MemAcc, mem_readable in *; intros;
    psimpl; match goal with H: forall a, a < 2^32 -> N.testbit _ a = true |- _ =>
      apply H; apply N.mod_lt; discriminate end.
  Local Ltac step := ISA_total_step.
  Local Ltac done := total_here; reflexivity.

  Lemma strcmp_loop_terminates:
    forall len (NIL: mem s0 Ⓑ[arg1 s0+len] = 0) k s hist
      (BOUND: k <= len)
      (ECX: s R_ECX = arg1 s0 ⊕ k)
      (EDX: s R_EDX = arg2 s0 ⊕ k)
      (MEM: s V_MEM32 = mem s0)
      (READ: forall a, a < 2^32 -> mem_readable s a),
    eventually strcmp_i386 (fun t => strcmp_exit t = true) ((Addr 8,s)::hist).
  Proof.
    intros len NIL.
    assert (LOOP: forall n k s hist, len-k = n -> k <= len ->
      s R_ECX = arg1 s0 ⊕ k -> s R_EDX = arg2 s0 ⊕ k ->
      s V_MEM32 = mem s0 ->
      (forall a, a < 2^32 -> mem_readable s a) ->
      eventually strcmp_i386 (fun t => strcmp_exit t = true) ((Addr 8,s)::hist)).
    { intro n. induction n using (well_founded_induction N.lt_wf_0).
      intros k s hist REM BOUND ECX EDX MEM READ.
      do 3 step.
      - do 4 step.
        + step. done.
        + assert (KL: k < len).
          { apply N.eqb_neq in BC0. destruct (N.eq_dec k len); [subst; congruence|lia]. }
          eapply H with (y:=len-(k+1)) (k:=k+1).
          all: try (psimpl; reflexivity).
          all: try lia.
          all: try assumption.
          all: try (unfold mem_readable in *; intros; psimpl; apply READ; assumption).
      - do 3 step. done.
    }
    intros. eapply LOOP; eassumption || reflexivity.
  Qed.

  Lemma strcmp_termination:
    forall len (NIL: mem s0 Ⓑ[arg1 s0+len] = 0),
    eventually strcmp_i386 strcmp_done ((Addr 0,s0)::nil).
  Proof.
    intros. apply i386_eventually_context.
    - pose proof READ0 as READ. pose proof MDL0 as MDL1.
      do 2 step.
      eapply strcmp_loop_terminates with (len:=len) (k:=0).
        exact NIL. apply N.le_0_l.
        unfold arg1, mem, esp. psimpl. reflexivity.
        unfold arg2, mem, esp. psimpl. reflexivity.
        all: try assumption.
        psimpl. reflexivity.
        all: try (unfold mem_readable in *; intros; psimpl; apply READ; assumption).
    - split. apply exec_prog_none. split. reflexivity. constructor. reflexivity.
  Qed.

  Theorem strcmp_total_correctness:
    forall len1 len2
      (STRING1: strcmp_nil_string (mem s0) (arg1 s0) len1)
      (STRING2: strcmp_nil_string (mem s0) (arg2 s0) len2),
    satisfies_total strcmp_i386 (strcmp_invs s0) strcmp_exit ((Addr 0,s0)::nil).
  Proof.
    intros. eapply total_of_partial with (entry:=(Addr 0,s0)).
      intros [|[x s] t] ORIGIN; try discriminate.
      rewrite ostartof_cons in ORIGIN. injection ORIGIN as ENTRY.
      apply strcmp_partial_correctness; assumption.
      apply (strcmp_termination len1), STRING1.
  Qed.

  Corollary strcmp_total_preserves_esp:
    forall len1 len2
      (STRING1: strcmp_nil_string (mem s0) (arg1 s0) len1)
      (STRING2: strcmp_nil_string (mem s0) (arg2 s0) len2),
    satisfies_total strcmp_i386 (esp_invs s0) strcmp_exit ((Addr 0,s0)::nil).
  Proof.
    intros. eapply total_of_partial with (entry:=(Addr 0,s0)).
      intros [|[x s] t] ORIGIN; try discriminate.
      rewrite ostartof_cons in ORIGIN. injection ORIGIN as ENTRY.
      apply strcmp_preserves_esp; assumption.
      apply (strcmp_termination len1), STRING1.
  Qed.

  Corollary strcmp_terminates:
    forall len1 len2
      (STRING1: strcmp_nil_string (mem s0) (arg1 s0) len1)
      (STRING2: strcmp_nil_string (mem s0) (arg2 s0) len2),
    exists prefix, exec_prog strcmp_i386 (prefix++(Addr 0,s0)::nil) /\
      exit_post (strcmp_invs s0) strcmp_exit (prefix++(Addr 0,s0)::nil).
  Proof.
    intros. apply eventually_reaches.
      eapply strcmp_total_correctness; eassumption.
      apply exec_prog_none.
  Qed.

  (* All three straight-line preservation results now have a terminating
     counterpart, in addition to the ESP total corollary above. *)
  Definition strcmp_frame_invs (t:trace) :=
    match t with (_,s):: _ => Some
      (s0 V_MEM32 = s V_MEM32 /\ s0 R_EBX = s R_EBX /\ s0 A_READ = s A_READ)
    | _ => None end.

  Corollary strcmp_total_preserves_frame:
    forall len1 len2
      (STRING1: strcmp_nil_string (mem s0) (arg1 s0) len1)
      (STRING2: strcmp_nil_string (mem s0) (arg2 s0) len2),
    satisfies_total strcmp_i386 strcmp_frame_invs strcmp_exit ((Addr 0,s0)::nil).
  Proof.
    intros. unfold satisfies_total. eapply eventually_bind.
      apply (strcmp_termination len1), STRING1.
    intros [|[x s] hist] [EX [XP [ORIGIN UT]]]; try discriminate.
    rewrite ostartof_cons in ORIGIN. injection ORIGIN as ENTRY.
    total_here. split. exact EX.
    cbn [strcmp_frame_invs true_inv]. split.
      eapply strcmp_preserves_memory; eassumption.
    split.
      eapply strcmp_preserves_ebx; eassumption.
      eapply strcmp_preserves_readable; eassumption.
  Qed.

End TotalCorrectness.

(* A first-instruction PLT model for the identified ELF, conditional on
   already-resolved GOT entries. The resolver path is not modeled here. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_correctness.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
From Stdlib Require Import NArith List.
Open Scope N.

Definition gmp_plt_indirect (a : addr) : option (N * stmt) :=
  match a with
  | 0x10c030 => Some (6, Jmp (Load (Var V_MEM64) (Word 0x178800 64) LittleE 8))
  | 0x10b8f0 => Some (6, Jmp (Load (Var V_MEM64) (Word 0x178460 64) LittleE 8))
  | 0x10bbe0 => Some (6, Jmp (Load (Var V_MEM64) (Word 0x1785d8 64) LittleE 8))
  | _ => None
  end.

Definition gmp_linked_got : program := fun s a =>
  match gmp_plt_indirect a with
  | Some code => Some code
  | None => gmp_linked s a
  end.

Lemma gmp_plt_indirect_welltyped :
  welltyped_prog x64typctx (fun _ => gmp_plt_indirect).
Proof. Picinae_typecheck. Qed.

Theorem gmp_linked_got_welltyped : welltyped_prog x64typctx gmp_linked_got.
Proof.
  intros s a. unfold gmp_linked_got.
  destruct (gmp_plt_indirect a) as [[sz q]|] eqn:PLT.
  - pose proof (gmp_plt_indirect_welltyped s a) as H.
    cbv beta in H. rewrite PLT in H. exact H.
  - exact (gmp_linked_welltyped s a).
Qed.

Lemma gmp_plt_indirect_add :
  gmp_plt_indirect 0x10c030 =
  Some (6, Jmp (Load (Var V_MEM64) (Word 0x178800 64) LittleE 8)).
Proof. reflexivity. Qed.
Lemma gmp_plt_indirect_sub :
  gmp_plt_indirect 0x10b8f0 =
  Some (6, Jmp (Load (Var V_MEM64) (Word 0x178460 64) LittleE 8)).
Proof. reflexivity. Qed.
Lemma gmp_plt_indirect_copy :
  gmp_plt_indirect 0x10bbe0 =
  Some (6, Jmp (Load (Var V_MEM64) (Word 0x1785d8 64) LittleE 8)).
Proof. reflexivity. Qed.

Lemma gmp_linked_got_add : forall s,
  gmp_linked_got s 0x10c030 = gmp_plt_indirect 0x10c030.
Proof. reflexivity. Qed.
Lemma gmp_linked_got_sub : forall s,
  gmp_linked_got s 0x10b8f0 = gmp_plt_indirect 0x10b8f0.
Proof. reflexivity. Qed.
Lemma gmp_linked_got_copy : forall s,
  gmp_linked_got s 0x10bbe0 = gmp_plt_indirect 0x10bbe0.
Proof. reflexivity. Qed.

Lemma gmp_plt_indirect_other : forall a,
  a <> 0x10c030 -> a <> 0x10b8f0 -> a <> 0x10bbe0 ->
  gmp_plt_indirect a = None.
Proof.
  intros a HA HS HC. unfold gmp_plt_indirect.
  destruct a as [|a];
  repeat first [reflexivity | solve [exfalso; apply HA; reflexivity] |
    solve [exfalso; apply HS; reflexivity] |
    solve [exfalso; apply HC; reflexivity] | destruct a as [a|a|] ].
Qed.

(* gmp_plt_got_resolved precondition *)
Definition gmp_plt_got_resolved (s : store) (slot target : N) : Prop :=
  (forall i, i < 8 -> mem_readable s ((slot+i) mod 2^64)) /\
  getmem 64 LittleE 8 (s V_MEM64) slot = target.

(* gmp_plt_got_resolved postcondition *)
Lemma gmp_plt_got_resolved_frame : forall before after slot target d bytes,
  gmp_plt_got_resolved before slot target ->
  after A_READ = before A_READ ->
  outside_output (before V_MEM64) (after V_MEM64) d bytes ->
  ~overlap 64 slot 8 d bytes ->
  gmp_plt_got_resolved after slot target.
Proof.
  intros before after slot target d bytes [READ VALUE] PERM FRAME DISJ.
  split.
  - intros i LT. unfold mem_readable. rewrite PERM. apply READ, LT.
  - rewrite (FRAME slot 8 DISJ). exact VALUE.
Qed.

(* gmp_plt_got_resolved postcondition *)
Lemma gmp_plt_got_resolved_jump : forall s slot target,
  gmp_plt_got_resolved s slot target ->
  exec_stmt x64typctx s
    (Jmp (Load (Var V_MEM64) (Word slot 64) LittleE 8))
    x64typctx s (Some (Addr target)).
Proof.
  intros s slot target [READ VALUE].
  rewrite <- VALUE.
  apply XJmp with (w:=64).
  eapply ELoad with (w:=64) (m:=s V_MEM64) (a:=slot).
  - apply EVar. reflexivity.
  - apply EWord.
  - exact READ.
Qed.

(* gmp_plt_got_resolved postcondition *)
Lemma gmp_plt_got_resolved_step_equiv : forall s slot target c' s' x,
  gmp_plt_got_resolved s slot target ->
  (exec_stmt x64typctx s
     (Jmp (Load (Var V_MEM64) (Word slot 64) LittleE 8)) c' s' x
   <-> exec_stmt x64typctx s (Jmp (Word target 64)) c' s' x).
Proof.
  intros s slot target c' s' x READY. split; intro STEP.
  - pose proof (gmp_plt_got_resolved_jump s slot target READY) as EXPECTED.
    assert (NO_UNKNOWN : forall_exps_in_stmt not_unknown
      (Jmp (Load (Var V_MEM64) (Word slot 64) LittleE 8))) by
      (simpl; repeat split; auto).
    pose proof (exec_stmt_deterministic NO_UNKNOWN STEP EXPECTED) as EQ.
    inversion EQ; subst. apply XJmp with (w:=64). apply EWord.
  - pose proof (gmp_plt_got_resolved_jump s slot target READY) as EXPECTED.
    assert (DIRECT : exec_stmt x64typctx s (Jmp (Word target 64))
      x64typctx s (Some (Addr target))) by
      (apply XJmp with (w:=64); apply EWord).
    assert (NO_UNKNOWN : forall_exps_in_stmt not_unknown
      (Jmp (Word target 64))) by (simpl; auto).
    pose proof (exec_stmt_deterministic NO_UNKNOWN STEP DIRECT) as EQ.
    inversion EQ; subst. exact EXPECTED.
Qed.

(* gmp_plt_indirect postcondition *)
Theorem gmp_plt_add_resolved : forall s,
  gmp_plt_got_resolved s 0x178800 0x1284e0 ->
  exec_stmt x64typctx s
    (Jmp (Load (Var V_MEM64) (Word 0x178800 64) LittleE 8))
    x64typctx s (Some (Addr 0x1284e0)).
Proof. exact (fun s H => gmp_plt_got_resolved_jump s _ _ H). Qed.

Theorem gmp_plt_sub_resolved : forall s,
  gmp_plt_got_resolved s 0x178460 0x128740 ->
  exec_stmt x64typctx s
    (Jmp (Load (Var V_MEM64) (Word 0x178460 64) LittleE 8))
    x64typctx s (Some (Addr 0x128740)).
Proof. exact (fun s H => gmp_plt_got_resolved_jump s _ _ H). Qed.

Theorem gmp_plt_copy_resolved : forall s,
  gmp_plt_got_resolved s 0x1785d8 0x15b186 ->
  exec_stmt x64typctx s
    (Jmp (Load (Var V_MEM64) (Word 0x1785d8 64) LittleE 8))
    x64typctx s (Some (Addr 0x15b186)).
Proof. exact (fun s H => gmp_plt_got_resolved_jump s _ _ H). Qed.

(* gmp_plt_all_resolved precondition *)
Definition gmp_plt_all_resolved (s : store) : Prop :=
  gmp_plt_got_resolved s 0x178800 0x1284e0 /\
  gmp_plt_got_resolved s 0x178460 0x128740 /\
  gmp_plt_got_resolved s 0x1785d8 0x15b186.

(* gmp_linked_got postcondition *)
Theorem gmp_linked_got_lookup_step_equiv : forall s a,
  gmp_plt_all_resolved s ->
  match gmp_linked_got s a, gmp_linked s a with
  | Some (n1,q1), Some (n2,q2) =>
      n1=n2 /\ (forall c' s' x,
        exec_stmt x64typctx s q1 c' s' x <->
        exec_stmt x64typctx s q2 c' s' x)
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros s a [ADD [SUB COPY]].
  destruct (N.eq_dec a 0x10c030) as [HA|HA]; [subst a|].
  - rewrite gmp_linked_got_add, gmp_plt_indirect_add, gmp_link_add.
    split; [reflexivity|]. intros; apply gmp_plt_got_resolved_step_equiv; exact ADD.
  - destruct (N.eq_dec a 0x10b8f0) as [HS|HS]; [subst a|].
    + rewrite gmp_linked_got_sub, gmp_plt_indirect_sub, gmp_link_sub.
      split; [reflexivity|]. intros; apply gmp_plt_got_resolved_step_equiv; exact SUB.
    + destruct (N.eq_dec a 0x10bbe0) as [HC|HC]; [subst a|].
      * rewrite gmp_linked_got_copy, gmp_plt_indirect_copy, gmp_link_copy.
        split; [reflexivity|]. intros; apply gmp_plt_got_resolved_step_equiv; exact COPY.
      * unfold gmp_linked_got. rewrite (gmp_plt_indirect_other a HA HS HC).
        destruct (gmp_linked s a) as [[n q]|]; simpl; auto.
        split; [reflexivity|]. intros; tauto.
Qed.

(* gmp_linked_got postcondition *)
Theorem gmp_linked_got_can_step_equiv : forall s a next,
  gmp_plt_all_resolved s ->
  (can_step gmp_linked_got (next, (Addr a,s)) <->
   can_step gmp_linked (next, (Addr a,s))).
Proof.
  intros s a next READY. split; intro STEP.
  - inversion STEP as [aa ss sz q c' s' x LU XS]; subst.
    pose proof (gmp_linked_got_lookup_step_equiv s a READY) as EQ.
    rewrite LU in EQ.
    destruct (gmp_linked s a) as [[sz2 q2]|] eqn:LOOK; [|contradiction].
    destruct EQ as [SIZE STEPS]; subst sz2.
    eapply CanStep with (q:=q2) (c':=c') (s':=s') (x:=x).
    + exact LOOK.
    + apply (proj1 (STEPS c' s' x)); exact XS.
  - inversion STEP as [aa ss sz q c' s' x LU XS]; subst.
    pose proof (gmp_linked_got_lookup_step_equiv s a READY) as EQ.
    rewrite LU in EQ.
    destruct (gmp_linked_got s a) as [[sz2 q2]|] eqn:LOOK; [|contradiction].
    destruct EQ as [SIZE STEPS]; subst sz2.
    eapply CanStep with (q:=q2) (c':=c') (s':=s') (x:=x).
    + exact LOOK.
    + apply (proj2 (STEPS c' s' x)); exact XS.
Qed.

(* gmp_edge_got_ready precondition *)
Definition gmp_edge_got_ready (edge : (exit*store)*(exit*store)) : Prop :=
  match fst (snd edge) with
  | Addr _ => gmp_plt_all_resolved (snd (snd edge))
  | Raise _ => True
  end.

(* gmp_linked_got postcondition *)
Lemma gmp_linked_got_edge_equiv : forall edge,
  gmp_edge_got_ready edge ->
  (can_step gmp_linked_got edge <-> can_step gmp_linked edge).
Proof.
  intros [[next ns] [current s]] READY.
  destruct current as [a|i].
  - exact (gmp_linked_got_can_step_equiv s a (next,ns) READY).
  - split; intro STEP; inversion STEP.
Qed.

(* gmp_plt_all_resolved precondition *)
(* gmp_linked_got postcondition *)
Theorem gmp_linked_got_trace_equiv : forall t,
  Forall gmp_edge_got_ready (stepsof t) ->
  (exec_prog gmp_linked_got t <-> exec_prog gmp_linked t).
Proof.
  intros t READY. unfold exec_prog.
  split; intro STEPS; apply Forall_forall; intros edge IN;
    pose proof (proj1 (Forall_forall _ _) READY edge IN) as HR;
    pose proof (proj1 (Forall_forall _ _) STEPS edge IN) as HS;
    pose proof (gmp_linked_got_edge_equiv edge HR) as EQ; tauto.
Qed.

(* __gmpn_add_n_sub_n precondition *)
(* __gmpn_add_n_sub_n postcondition *)
Corollary add_n_sub_n_post_at_return_resolved_got :
  forall r cc ac sc t s,
  startof t (Addr 0x15c443,s)=(Addr 0x15c360,r) ->
  wrapper_pre r ->
  exec_prog gmp_linked_got ((Addr 0x15c443,s)::t) ->
  Forall gmp_edge_got_ready (stepsof ((Addr 0x15c443,s)::t)) ->
  unterminated (gmp_exits 3 cc ac sc (wrapper_property r)) t ->
  wrapper_post r s.
Proof.
  intros r cc ac sc t s ENTRY ROOT EXEC READY UT.
  eapply add_n_sub_n_post_at_return; eauto.
  apply (proj1 (gmp_linked_got_trace_equiv _ READY)); exact EXEC.
Qed.

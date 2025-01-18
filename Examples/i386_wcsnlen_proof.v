Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import i386_wcsnlen.
Require Import Lia.
Import X86Notations.
Open Scope N.

(* Type safety:
   We first prove that the program is well-typed (automated by the Picinae_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem wcsnlen_welltyped: welltyped_prog x86typctx i386_wcsnlen.
Proof. Picinae_typecheck. Qed.

(* wcsnlen preserves readable *)
Theorem wcsnlen_preserves_readable:
  forall_endstates i386_wcsnlen (fun _ s _ s' => s A_READ = s' A_READ).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* Define function exit points *)
Definition wcsnlen_exit (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 111 | 115 | 122 | 129 => true
  | _ => false
  end | _ => false end.

(* Define binary-level string len: *)
Definition wcsnlen_atleast (m:memory) (p1:addr) (len:N) :=
  ∀ i, i < len -> 0 <> m Ⓓ[p1 + 4*i].

(*there's a library theorem that does this, we need to replace this function w that*)
Lemma rewrite_gt_lt : forall a b : N,
  a > b <-> b < a.
Proof.
  Require Import Lia. lia.
Qed.

Theorem succ_k_small1:
  forall mem' esp k (S1: mem' Ⓓ[8 + esp] > k), 1⊕k=1+k.
Proof.
  intros. apply N.gt_lt in S1. apply N.mod_small.
  change (2^32) with (1+ N.pred (2^32)). apply N.add_lt_mono_l.
  apply (N.lt_le_trans _ _ _ S1), N.lt_le_pred, getmem_bound.
Qed.

Lemma gt_plus_one (n a b: N):
  (n > a) /\ ( (n =? b ) = false) /\ (b = a+1) -> (n > b).
Proof.
  intros. destruct H. destruct H0. subst. assert (a+1 <= n). lia. apply N.le_lteq in H1. destruct H1.
  lia. apply N.eqb_neq in H0. subst. contradiction.
Qed.

Lemma lt_add_lhs (a b c d: N):
  (a > b) /\ (a + c = d) -> (b + c < d).
Proof.
  intros. destruct H. subst. lia.
Qed.

Lemma gt_to_neq (mem:memory) (esp:addr) (k:N):
    (forall i: N, i <= k -> i <> mem Ⓓ[ 8 + esp ]) -> (mem Ⓓ[ 8 + esp ] > k).
Proof.
  intros. apply N.lt_gt.
  assert (k >= mem Ⓓ[ 8 + esp ] -> False). intros.
  assert (∃i:N, i <= k /\ i = mem Ⓓ[ 8 + esp]). exists (mem Ⓓ[ 8 + esp]). split.
  lia. reflexivity. destruct H1. destruct H1. apply H in H1. contradiction.
  assert ((mem Ⓓ[ 8 + esp ] <= k) \/ (k < mem Ⓓ[ 8 + esp ])).
  apply (N.le_gt_cases (mem Ⓓ[ 8 + esp ]) k). destruct H1.
  apply (N.le_ge (mem Ⓓ[ 8 + esp ]) k) in H1. apply H0 in H1. contradiction.
  assumption.
Qed.

Lemma wcsnlen_inductive (m:memory) (p1:addr) (len:N):
  wcsnlen_atleast m p1 (len) -> ((0 <> m Ⓓ[p1 + len * 4]) -> wcsnlen_atleast m p1 (1 + len)).
  Proof.
  unfold wcsnlen_atleast. intros.
  assert (len < (1 + len)) by lia.
  eapply N.lt_le_pred in H1. rewrite N.pred_sub in H1. psimpl in H1.
  eapply N.le_lteq in H1. destruct H1.
  eapply H. eassumption.
  erewrite H1. rewrite N.mul_comm. eassumption.
  Qed.

Lemma wcsnlen_alt_def (m:memory) (p1:addr) (len:N):
  ((0 ≠ m Ⓓ[ p1 + 4 * len ]) /\ (wcsnlen_atleast m p1 len) )-> (wcsnlen_atleast m p1 (1+len)).
Proof.
  unfold wcsnlen_atleast. intros. destruct H.
  apply N.lt_le_pred in H0. rewrite N.pred_sub in H0. psimpl in H0.
  apply N.le_lteq in H0. destruct H0.
  apply H1. assumption. rewrite H0. exact H.
Qed.

Lemma rewrite_mod_plus (k n:N):
 (n + k < 2^32) /\ (1<=n) -> (n ⊕ k) = 1 + ((n - 1) + k).
Proof.
  intros. destruct H.
  psimpl. rewrite N.add_sub_assoc. psimpl. apply N.mod_small. assumption. assumption.
Qed.

(* Invariants*)
Section Invariants.

  Variable mem : memory. (* initial memory state *)
  Variable esp : N.         (* initial stack pointer *)
  Variable ebx : N.

  Definition p1 := mem Ⓓ[4+esp]. (* first stack argument *)
  Definition p2 := mem Ⓓ[8+esp]. (* second stack argument *)

  (* Define the memory state AFTER pushing the callee stack frame.*)
  Definition mem' fbytes:= setmem 32 LittleE 4 mem (esp ⊖ 4) fbytes.

  (*full invariant set: *)
  Definition wcsnlen_invs (t:trace) :=
  match t with (Addr a,s)::_ => match a with

  (* function entry point *)
  | 0 => Some (s V_MEM32 = mem /\ s R_ESP = esp /\
    s R_EBX = ebx)
  (* loop invariant , p1 and p2*)
  | 101  => Some (∃ eax k n fb,
      (s R_ESP = (esp ⊖ 4)) /\
      (s V_MEM32 = (mem' fb)) /\
      (s R_ECX = n) /\
      (s R_EDX = k)/\
      (s R_EAX = eax)/\
      (wcsnlen_atleast (mem' fb) (p1) (k)) /\
      (s R_EBX = p1) /\
      (*ebx points to the beginning of the string*)
      (p2 > k) /\
      (*maxlen characters = ecx (characters to be counted) + k(characters counted so far) +2(first two cases)*)
      (n + k = p2 + 2 /\ n > 2)
      )
  (* init post condition *)
  | 111 | 115 | 122 | 129 => Some (∃ k fb,
      (s R_EAX = k) /\ (s V_MEM32 = mem' fb) /\
      (wcsnlen_atleast (mem' fb) (p1) k) /\
      (* k is the specified max length, OR the k+1 character is null *)
      ( p2 = k \/ (mem' fb) Ⓓ[p1 + (4 * k)] = 0)
     )
  | _ => None
  end | _ => None end.
End Invariants.

(* Main correctness theorem & proof: *)

Theorem wcsnlen_partial_correctness:
  forall s esp ebx mem t s' x'
         (ENTRY: startof t (x',s') = (Addr 0, s))
         (MDL: models x86typctx s)
         (ESP: s R_ESP = esp) (MEM: s V_MEM32 = mem)
         (EBX: s R_EBX = ebx),
  satisfies_all i386_wcsnlen (wcsnlen_invs mem esp ebx) wcsnlen_exit ((x',s')::t).
Proof.
  Local Ltac step := time x86_step.
  intros. unfold satisfies_all. apply prove_invs.

  simpl. rewrite ENTRY. step.
  repeat split. assumption. assumption. assumption.

  (* Time how long it takes for each symbolic interpretation step to complete
     (for profiling and to give visual cues that something is happening...). *)


  (* Optional: The following proof ignores all flag values except CF and ZF, so
     we can make evaluation faster and shorter by telling Picinae to ignore the
     other flags (i.e., abstract their values away).
  Ltac x86_ignore v ::= constr:(match v with
    R_AF | R_DF | R_OF | R_PF | R_SF => true
  | _ => false end).*)

  (* step to address 1 *)

  intros.
  eapply startof_prefix in ENTRY ; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply wcsnlen_welltyped).
  clear - PRE MDL. rename t1 into t. rename s1 into s.

  destruct_inv 32 PRE.

  destruct PRE as [MEM [ESP EBX]].
  step. step. step.

  (* step to address 11, fork: ret 0 or continue *)
  (* step to address 115, return value = 0 *)
  step. step. step. step.
    exists 0, ebx. repeat split. unfold mem'.
      unfold wcsnlen_atleast. intros. inversion H. destruct i ; discriminate.
      left. rewrite N.eqb_eq in BC; symmetry in BC. unfold mem'; psimpl; eassumption.

  (* step to address 17, fork: ret 0, or continue *)
  step. step.

    (* step to address 115, return value = 0 *)
    step. step. step.
    exists 0, ebx. repeat split.
    unfold wcsnlen_atleast. intros. inversion H. destruct i; discriminate.
    right. unfold mem',p1; psimpl. rewrite N.eqb_eq in BC0; symmetry in BC0. eassumption.


  (* step to address 22, fork: ret 1, or continue *)
  step.

    (* step to address 122, return value = 1 *)
    step. step. step.
    exists 1, ebx. repeat split.
    unfold wcsnlen_atleast. intros.
    unfold mem'. psimpl.
    inversion H. apply N.lt_1_r in H1. rewrite H1. psimpl. unfold mem'. psimpl.
    apply N.eqb_neq in BC0. psimpl.
     psimpl in BC0. eassumption.
    left. unfold mem'. psimpl. apply N.eqb_eq in BC1. eassumption.
    (* Prove post-condition for addr 122 (return value = 1) *)

  (* step to address 29, fork: ret 1, or continue *)
  step. step.

    (* step to address 122, return value = 1 *)
    step. step. step. exists 1, ebx. repeat split.
    unfold wcsnlen_atleast. intros.
    unfold mem'. psimpl.
    inversion H. apply N.lt_1_r in H1. rewrite H1. psimpl.
    apply N.eqb_neq in BC0. eassumption.
    right.
    unfold mem', p1; psimpl. apply N.eqb_eq in BC2; symmetry in BC2.  eassumption.
    (* Prove post-condition for addr 122 (return value = 1) *)

  (* step to address 34, fork: ret 2, or continue *)
  step.

    (* step to address 129, return value = 2 *)
    step. step. step. eexists 2, ebx. do 3 split.
    unfold wcsnlen_atleast. intros.
    unfold mem'. psimpl. inversion H. eapply N.eqb_neq in BC0, BC2. induction i using N.peano_ind. psimpl. eassumption.
      induction i using N.peano_ind. psimpl. simpl N.succ. psimpl. assumption. Require Import Lia. lia.
    apply N.eqb_eq in BC3.
    left. psimpl. eassumption.
    (* Prove post-condition for addr 129 (return value = 2) *)

  (* step to address 41, jump into loop *)
  step.

  (* step to address 101, loop invariant *)
  step. eapply N.eqb_neq in BC3, BC0, BC1, BC2, BC. unfold mem',p2; psimpl. repeat eexists; try eapply gt_to_neq; psimpl.
      unfold wcsnlen_atleast. intros.
        induction i using  N.peano_ind. psimpl; eassumption.
        induction i using N.peano_ind; simpl N.succ. psimpl; eassumption.
        lia.
      intros.
        induction i using N.peano_ind. eassumption. lia.
      reflexivity.
      intros.
        induction i using N.peano_ind. eassumption. lia.

  destruct PRE as [n [k [ecx [fb [ESP [MEM [ECX [EDX [EAX [AL [EBX [S1 [C1 C2]]]]]]]]]]]]].

  (* step to address 106, fork: continue loop, or return based on eax =? 0 *)
  step. step.

    (* step to address 111, post-condition after loop *)
    step. step. step. exists k, fb. repeat split.
    unfold p1. assumption.
      right.
        rewrite N.shiftl_mul_pow2 in BC; psimpl in BC. rewrite N.mul_comm in BC.
        rewrite N.eqb_eq in BC; symmetry in BC. eassumption.

  (* step to address 54, fork: continue loop, or return based on ecx =? 3 *)
  step. step.

    (* step to address 111, post-condition after loop *)
    step. step. exists (1⊕k), fb.
    assert (1 ⊕ k = 1 + k ). eapply succ_k_small1. eassumption.
    erewrite H. apply N.eqb_neq in BC. rewrite N.shiftl_mul_pow2 in BC; psimpl in BC.
    repeat split.
    apply wcsnlen_inductive with (len:= (k)) in AL; eassumption.
    left.
      apply N.eqb_eq in BC0.
      erewrite <- N.add_cancel_r with (p:= 2). symmetry.
      replace (1 + k + 2) with (3 + k) by lia. rewrite BC0 in C1. eassumption.
    (* Prove post-condition for addr 111 (after loop) *)

  (* step to address 61, fork: continue loop, or return based on str[edx + 1] =? \0 *)
  (* by str[edx + 1] we mean 0x4(%ebx,%edx,4) *)
  step.

    (* step to address 111, post-condition after loop *)
    step. step. exists (1 ⊕ k), fb.
    assert (1 ⊕ k = 1 + k ). eapply succ_k_small1. unfold mem' in S1; psimpl in S1. eassumption.
    do 3 split.
    erewrite H. apply N.eqb_neq in BC. erewrite N.shiftl_mul_pow2, N.mul_comm in BC; psimpl in BC.
      unfold wcsnlen_atleast. eapply wcsnlen_alt_def. split. psimpl. eassumption.
    apply N.eqb_eq in BC1. rewrite N.shiftl_mul_pow2 in BC1. eassumption.
    unfold mem' at 1. psimpl.
    right.
      psimpl. rewrite N.mul_add_distr_l. psimpl.
      rewrite N.eqb_eq in BC1. symmetry in BC1.
      rewrite N.shiftl_mul_pow2, N.mul_comm in BC1; psimpl in BC1; eassumption.
    (*  Prove post-condition for addr 111 (after loop) *)
    (* ecx <- ecx - 4 occurs here *)
  (* step to address 69, fork: continue loop, or return based on ecx =? 0 *)

  step. step.

  (* step to address 111, post-condition after loop *)
  step. step. exists (2 ⊕ k), fb.
  assert(2 ⊕ k = 1 + (1 + k)). erewrite rewrite_mod_plus. psimpl (2 - 1). reflexivity.
    psimpl in C1. split.
    apply Neqb_ok in BC2. rewrite BC2 in C1. change 4 with (2+2) in C1  at 1 . rewrite <- N.add_assoc in C1. apply N.add_cancel_l in C1.
    rewrite C1. apply getmem_bound.
    lia.
  repeat split.
  (*erewrite H. *)
  erewrite H. repeat split.
  apply wcsnlen_inductive with (len:= (k)) in AL.

  apply wcsnlen_alt_def. split. apply N.eqb_neq. rewrite N.mul_add_distr_l. psimpl. assumption. assumption.
  apply N.eqb_neq in BC. rewrite N.shiftl_mul_pow2 in BC; psimpl in BC.
  eassumption.
  left.
    rewrite N.eqb_eq in BC2. erewrite BC2 in C1.
    symmetry in C1. rewrite <- N.add_cancel_r with (p:=2). rewrite C1, H. psimpl. reflexivity.
  (* Prove post-condition for addr 111 (after loop) *)

(* step to address 76, fork: continue loop, or return based on str[edx + 2] =? \0 *)
  step.

  (* step to address 111, post-condition after loop *)
  step. step. exists (2 ⊕ k), fb.
  assert(2 ⊕ k = 1 + (1 + k)). erewrite rewrite_mod_plus. psimpl (2 - 1). reflexivity.
    unfold mem' in C1. psimpl in C1. split.
    assert (ecx > 3). apply (gt_plus_one ecx 2 3). split. assumption. split. assumption. lia.
    assert (ecx > 4). apply (gt_plus_one ecx 3 4). split. assumption. split. assumption. lia.
    assert (4 + k < mem Ⓓ[ 8 + esp ] + 2).
    apply (lt_add_lhs ecx 4 k (mem Ⓓ[ 8 + esp ] + 2)).
    split. lia. symmetry. erewrite N.add_comm. symmetry. assumption.
    assert (2 + k < mem Ⓓ[ 8 + esp ]). lia. apply (N.lt_le_trans _ _ _ H2).
    apply N.lt_le_incl. apply getmem_bound.
  lia.
  erewrite H. repeat split.
  apply wcsnlen_inductive with (len:= (k)) in AL. apply wcsnlen_alt_def.
  split. apply N.eqb_neq. rewrite N.mul_add_distr_l. psimpl. eassumption.
  eassumption.
  apply N.eqb_neq in BC. rewrite N.shiftl_mul_pow2 in BC; psimpl in BC; eassumption.
  right.
    rewrite N.eqb_eq in BC3. rewrite N.shiftl_mul_pow2, N.mul_comm in BC3; psimpl in BC3; symmetry in BC3.
    psimpl; erewrite N.mul_add_distr_l; psimpl; eassumption.
  (* Prove post-condition for addr 111 (after loop) *)

(* step to address 84, fork: continue loop, or return based on ecx =? 1 *)
  step. step.

  (* step to address 111, post-condition after loop *)
  step. step. eexists (3 ⊕ k), fb.
  assert(3 ⊕ k = 1 + (2 + k)). erewrite rewrite_mod_plus. psimpl (3 - 1). reflexivity.
    psimpl in C1. split.
    apply Neqb_ok in BC4. rewrite BC4 in C1. assert (3 + k = p2 mem esp). lia. rewrite H. apply getmem_bound.
  lia.
  erewrite H. repeat split.
  apply wcsnlen_inductive with (len := k) in AL. apply wcsnlen_inductive with (len := (1 + k)) in AL. psimpl in AL.
    apply wcsnlen_alt_def. split. apply N.eqb_neq. rewrite N.mul_add_distr_l. psimpl. eassumption. eassumption.
  apply N.eqb_neq in BC1. rewrite N.shiftl_mul_pow2 in BC1; psimpl in BC1. erewrite N.mul_add_distr_r. psimpl. eassumption.
  apply N.eqb_neq in BC. rewrite N.shiftl_mul_pow2 in BC; psimpl in BC. eassumption.
  left.
    rewrite N.eqb_eq in BC4. erewrite BC4 in C1; symmetry in C1.
    rewrite <- N.add_cancel_r with (p:=2). psimpl ( 1 + (2 + k) + 2). eassumption.
  (* Prove post-condition for addr 111 (after loop) *)

(* step to address 91, fork: continue loop, or return based on str[edx + 3] =? \0 *)
  step.

  (* step to address 111, post-condition after loop *)
  step. step. eexists (3 ⊕ k), fb.
  assert(3 ⊕ k = 1 + (2 + k)). erewrite rewrite_mod_plus. psimpl (3 - 1). reflexivity.
    unfold mem' in C1. psimpl in C1. split.
    assert (ecx > 3). apply (gt_plus_one ecx 2 3). split. assumption. split. assumption. lia.
    assert (ecx > 4). apply (gt_plus_one ecx 3 4). split. assumption. split. assumption. lia.
    assert (ecx > 5). apply (gt_plus_one ecx 4 5). split. assumption. split. assumption. lia.
    assert (5 + k < mem Ⓓ[ 8 + esp ] + 2).
    apply (lt_add_lhs ecx 5 k (mem Ⓓ[ 8 + esp ] + 2)).
    split.
    lia. symmetry. erewrite N.add_comm. symmetry. eassumption.
    assert (3 + k < mem Ⓓ[ 8 + esp ]). lia. apply (N.lt_le_trans _ _ _ H3).
    apply N.lt_le_incl. apply getmem_bound.
  lia.
  erewrite H. repeat split.
  apply wcsnlen_inductive with (len := k) in AL. apply wcsnlen_inductive with (len := (1 + k)) in AL. psimpl in AL.
    apply wcsnlen_alt_def. split. apply N.eqb_neq. rewrite N.mul_add_distr_l. psimpl. eassumption. eassumption.
  apply N.eqb_neq in BC1. rewrite N.shiftl_mul_pow2 in BC1; psimpl in BC1.
  erewrite N.mul_add_distr_r. psimpl. eassumption.
  apply N.eqb_neq in BC. rewrite N.shiftl_mul_pow2 in BC; psimpl in BC. eassumption.
  right.
    psimpl. rewrite N.eqb_eq in BC5. rewrite N.shiftl_mul_pow2, N.mul_comm in BC5; psimpl in BC5; symmetry in BC5. psimpl.
    erewrite N.mul_add_distr_l; psimpl. eassumption.
  (* Prove post-condition for addr 111 (after loop) *)

(* edx <- edx + 4 occurs here *)
(* step to address 99, fork: continue loop, or return based on ecx =? 2 *)
  step. step.

  (* step to address 111, post-condition after loop *)
  step. step. step. exists (4 ⊕ k), fb.
  assert(4 ⊕ k = 1 + (3 + k)). erewrite rewrite_mod_plus. psimpl (4 - 1). reflexivity.
    psimpl in C1. split.
    apply Neqb_ok in BC6. rewrite BC6 in C1. assert (4 + k = p2 mem esp). lia. rewrite H. apply getmem_bound.
  lia.
  erewrite H. repeat split.
  apply wcsnlen_inductive with (len := k) in AL. apply wcsnlen_inductive with (len := (1 + k)) in AL.
  apply wcsnlen_inductive with (len := (1 +(1 + k))) in AL. psimpl in AL.
  apply wcsnlen_alt_def. split. apply N.eqb_neq. rewrite N.mul_add_distr_l. psimpl. assumption. assumption. psimpl.
    apply N.eqb_neq in BC3. rewrite N.shiftl_mul_pow2 in BC3; psimpl in BC3. erewrite N.mul_add_distr_r. psimpl. eassumption.
  apply N.eqb_neq in BC1. rewrite N.shiftl_mul_pow2 in BC1; psimpl in BC1. erewrite N.mul_add_distr_r. psimpl. eassumption.
  apply N.eqb_neq in BC. rewrite N.shiftl_mul_pow2 in BC; psimpl in BC. eassumption.
  left.
    rewrite N.eqb_eq in BC6. erewrite BC6 in C1; symmetry in C1.
    rewrite <- N.add_cancel_r with (p:=2). psimpl (1 + (3 + k) + 2). eassumption.
  (* Prove post-condition for addr 111 (after loop) *)

(* step to address 111, post-condition after loop *)
(* Prove post-condition for addr 111 (after loop) *)
  eexists. eexists (4 ⊕ k). eexists. eexists fb.
  assert(CX1: ecx ⊖ 4 = ecx - 4).
    apply N.eqb_neq in BC0, BC2, BC4, BC6.
    psimpl. erewrite (msub_nowrap _ 4). psimpl. reflexivity. psimpl. lia.
  assert(4 ⊕ k = 1 + (3 + k)). erewrite rewrite_mod_plus. psimpl (4 - 1). reflexivity.
    unfold mem' in C1. psimpl in C1. repeat split.
    assert (ecx > 3). apply (gt_plus_one ecx 2 3). repeat split. lia. assumption.
    assert (ecx > 4). apply (gt_plus_one ecx 3 4). repeat split. lia. assumption.
    assert (ecx > 5). apply (gt_plus_one ecx 4 5). repeat split. lia. assumption.
    assert (ecx > 6). apply (gt_plus_one ecx 5 6). repeat split. lia. assumption.
    assert (6 + k < mem Ⓓ[ 8 + esp ] + 2).
    apply (lt_add_lhs ecx 6 k (mem Ⓓ[ 8 + esp ] + 2)).
    split. lia. symmetry. erewrite N.add_comm. symmetry. eassumption.
    assert (4 + k < mem Ⓓ[ 8 + esp ]). lia. apply (N.lt_le_trans _ _ _ H4).
    apply N.lt_le_incl. apply getmem_bound.
  lia.
  eapply N.eqb_neq in BC0, BC2, BC4, BC6.
  erewrite H. repeat split. eassumption.
  apply wcsnlen_inductive with (len := k) in AL. apply wcsnlen_inductive with (len := (1 + k)) in AL.
    apply wcsnlen_inductive with (len := (1 +(1 + k))) in AL. psimpl in AL.
    apply wcsnlen_alt_def. split. apply N.eqb_neq. rewrite N.mul_add_distr_l. psimpl. assumption. assumption. psimpl.
    apply N.eqb_neq in BC3. rewrite N.shiftl_mul_pow2 in BC3; psimpl in BC3.
    erewrite N.mul_add_distr_r. psimpl. eassumption.
    apply N.eqb_neq in BC1. rewrite N.shiftl_mul_pow2 in BC1; psimpl in BC1.
    erewrite N.mul_add_distr_r. psimpl. eassumption.
    apply N.eqb_neq in BC. rewrite N.shiftl_mul_pow2 in BC; psimpl in BC. eassumption.
  psimpl.
  rewrite rewrite_gt_lt.
    erewrite N.add_lt_mono_r with (p := ecx).
    assert (E1: 6 < ecx) by lia.
    assert (6 + k < k + ecx) by lia. psimpl in H0.
    rewrite rewrite_gt_lt in S1. erewrite N.add_lt_mono_r with (p := ecx) in S1.
    rewrite S1 in H0.
    replace (4 + k + ecx) with (4 + ecx + k) by lia. rewrite <- N.add_assoc. rewrite C1. rewrite N.add_assoc. psimpl.
    erewrite N.add_lt_mono_r with (p := p2 mem esp) in E1. erewrite N.add_comm with (n := p2 mem esp) (m := ecx).
    eassumption.
  erewrite CX1. psimpl. erewrite N.add_sub_assoc. psimpl. erewrite N.add_comm with (n := 2) (m := p2 mem esp). eassumption. lia.
  erewrite CX1. assert (6 < ecx) by lia. lia.
Qed.

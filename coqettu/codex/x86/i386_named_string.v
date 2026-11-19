(* Finite static-name recognition from an executed strcmp result. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_stringcmp.
From Stdlib Require Import NArith Lia Bool.
Open Scope N.
Fixpoint name_checks (last:nat) (read letters:N->N):bool:=
  match last with
  | O=>read 0=?letters 0
  | S n=>name_checks n read letters && (read (N.of_nat (S n))=?letters (N.of_nat (S n)))
  end.
Lemma name_checks_spec:forall last read letters,name_checks last read letters=true <->
  forall i,i<=N.of_nat last ->read i=letters i.
Proof.
  induction last as [|n IH];intros read letters.
  - cbn [name_checks N.of_nat]. rewrite N.eqb_eq. split.
    + intros E i I. replace i with 0 by lia. exact E.
    + intro H. apply H. lia.
  - cbn [name_checks]. rewrite Bool.andb_true_iff,IH,N.eqb_eq,Nat2N.inj_succ. split.
    + intros [H E] i I. destruct (N.le_gt_cases i (N.of_nat n)).
      * apply H;assumption.
      * replace i with (N.succ (N.of_nat n)) by lia. exact E.
    + intro H. split;[intros i I;apply H;lia|apply H;lia].
Qed.
Definition fixed_name_matchb (m:memory) (p:N) (letters:N->N) (last:N):=
  name_checks (N.to_nat last) (fun i=>getmem 32 LittleE 1 m (p+i)) letters.
Lemma fixed_name_matchb_spec:forall m p letters last,fixed_name_matchb m p letters last=true <->
  forall i,i<=last ->getmem 32 LittleE 1 m (p+i)=letters i.
Proof. intros. unfold fixed_name_matchb. rewrite name_checks_spec,N2Nat.id. reflexivity. Qed.
Lemma fixed_name_compare_zero:forall m p q letters last value,
  (forall i,i<=last ->getmem 32 LittleE 1 m (q+i)=letters i) ->
  letters last=0 ->(forall i,i<last ->letters i<>0) ->
  string_compare_result m p q value ->
  (value=0 <->fixed_name_matchb m p letters last=true).
Proof.
  intros m p q letters last value DATA END NZ (k & K & PREFIX & STOP & VALUE).
  pose proof (string_equal_prefix_right _ _ _ _ PREFIX) as NZQ.
  assert (KL:k<=last).
  { destruct (N.le_gt_cases k last);[assumption|]. exfalso.
    pose proof (NZQ last ltac:(lia)) as NONZERO. rewrite DATA,END in NONZERO by lia. contradiction. }
  rewrite fixed_name_matchb_spec. split.
  - intro ZERO. rewrite ZERO in VALUE. symmetry in VALUE. apply msub_move_0_r in VALUE. psimpl in VALUE.
    assert (PZERO:getmem 32 LittleE 1 m (p+k)=0) by tauto.
    assert (EQ:k=last).
    { destruct (N.eq_dec k last);[assumption|]. pose proof (NZ k ltac:(lia)) as NONZERO.
      rewrite VALUE,DATA in PZERO by lia. contradiction. }
    subst k. intros i I. destruct (N.lt_ge_cases i last).
    + rewrite (proj1 PREFIX i H),DATA by lia. reflexivity.
    + replace i with last by lia. rewrite END. exact PZERO.
  - intro MATCH. assert (EQ:k=last).
    { destruct (N.eq_dec k last);[assumption|]. exfalso. pose proof (NZ k ltac:(lia)) as NONZERO.
      rewrite MATCH,DATA in STOP by lia. tauto. }
    subst k. rewrite MATCH,DATA,END in VALUE by lia. exact VALUE.
Qed.

(* Frozen-source byte copying, pointwise results and exact outside-region frame. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_memory i386_strings.
From Stdlib Require Import NArith Lia.
Open Scope N.
Definition copy_bytes (source:memory) (q p k:N) (m:memory):memory:=
  N.recursion m (fun i acc=>setmem 32 LittleE 1 acc (p+i) (getmem 32 LittleE 1 source (q+i))) k.
Lemma copy_bytes_zero:forall source q p m,copy_bytes source q p 0 m=m.
Proof. reflexivity. Qed.
Lemma copy_bytes_succ:forall source q p k m,copy_bytes source q p (k+1) m=
  setmem 32 LittleE 1 (copy_bytes source q p k m) (p+k) (getmem 32 LittleE 1 source (q+k)).
Proof.
  intros. replace (k+1) with (N.succ k) by lia. unfold copy_bytes.
  rewrite N.recursion_succ by (repeat (hnf;intros);subst;reflexivity). reflexivity.
Qed.
Lemma distinct_byte_cells:forall p n i j,n<=2^32 ->i<n ->j<n ->i<>j ->~overlap 32 (p+i) 1 (p+j) 1.
Proof.
  intros p n i j BOUND I J NE (u & v & U & V & EQ).
  assert (u=0 /\ v=0) by lia. destruct H;subst u v. rewrite !N.add_0_r in EQ.
  pose proof (f_equal (fun a=>msub 32 a p) EQ) as DELTA. cbn beta in DELTA.
  rewrite !msub_mod_l,!add_msub_l in DELTA by reflexivity.
  rewrite !N.mod_small in DELTA by lia. contradiction.
Qed.
Lemma copy_bytes_frame:forall source q p k m,memory_region_frame m (copy_bytes source q p k m) p k.
Proof.
  intros source q p k. induction k using N.peano_ind;intros m a count NO.
  - reflexivity.
  - replace (N.succ k) with (k+1) in * by lia. rewrite copy_bytes_succ.
    rewrite getmem_noverlap.
    + apply IHk. eapply noverlap_shrink;[|exact NO]. rewrite msub_diag;lia.
    + apply noverlap_symmetry. eapply noverlap_index_l;[exact NO|lia].
Qed.
Lemma copy_bytes_prefix:forall source q p k m,k<=2^32 ->forall i,i<k ->
  getmem 32 LittleE 1 (copy_bytes source q p k m) (p+i)=getmem 32 LittleE 1 source (q+i).
Proof.
  intros source q p k. induction k using N.peano_ind;intros m BOUND i I;[lia|].
  replace (N.succ k) with (k+1) in * by lia. rewrite copy_bytes_succ.
  destruct (N.eq_dec i k) as [EQ|NE].
  - subst i. rewrite getmem_setmem by lia. apply N.mod_small. apply getmem_bound.
  - rewrite getmem_noverlap.
    + apply IHk;lia.
    + apply distinct_byte_cells with (n:=k+1);lia.
Qed.
Definition copy_terminated (source:memory) (q p k:N) (m:memory):memory:=
  setmem 32 LittleE 1 (copy_bytes source q p k m) (p+k) 0.
Lemma copy_terminated_zero:forall source q p k m,getmem 32 LittleE 1 (copy_terminated source q p k m) (p+k)=0.
Proof. intros. unfold copy_terminated. rewrite getmem_setmem by lia;reflexivity. Qed.
Lemma copy_terminated_prefix:forall source q p k m,k<2^32 ->forall i,i<k ->
  getmem 32 LittleE 1 (copy_terminated source q p k m) (p+i)=getmem 32 LittleE 1 source (q+i).
Proof.
  intros source q p k m BOUND i I. unfold copy_terminated. rewrite getmem_noverlap.
  - apply copy_bytes_prefix;lia.
  - apply distinct_byte_cells with (n:=k+1);lia.
Qed.
Lemma copy_terminated_frame:forall source q p k m,memory_region_frame m (copy_terminated source q p k m) p (k+1).
Proof.
  intros source q p k m a count NO. unfold copy_terminated. rewrite getmem_noverlap.
  - apply copy_bytes_frame. eapply noverlap_shrink;[|exact NO]. rewrite msub_diag;lia.
  - apply noverlap_symmetry. eapply noverlap_index_l;[exact NO|lia].
Qed.

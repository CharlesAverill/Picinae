(* Reused argument/return stack slots and exact overwrite collapse. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_deep_stack.
From Stdlib Require Import NArith Lia.
Open Scope N.
Transparent memsize.
Lemma call_setmem_shadow:forall w e len m a old new,
  setmem w e len (setmem w e len m a old) a new=setmem w e len m a new.
Proof.
  intros.
  rewrite <- (recompose_bytes (2^w*8) (setmem w e len (setmem w e len m a old) a new)).
  rewrite <- (recompose_bytes (2^w*8) (setmem w e len m a new)).
  rewrite !setmem_highbits. apply f_equal2;[|reflexivity].
  pose proof (byte_equivalent w (setmem w e len (setmem w e len m a old) a new)
    (setmem w e len m a new)) as EQ.
  unfold memsize in EQ. apply EQ. intro p. destruct (overlap_dec w p 1 a len) as [OV|NO].
  - apply overlap_getbyte_updated;exact OV.
  - rewrite <- !(getmem_1 w e),!getmem_noverlap by exact NO. reflexivity.
Qed.
Opaque memsize.
Definition case_call_pair (m:memory) (sp arg ra:N):=
  setmem 32 LittleE 4 (setmem 32 LittleE 4 m (msub 32 sp 44) arg) (msub 32 sp 48) ra.
Lemma case_call_pair_shadow:forall m sp arg1 ra1 arg2 ra2,
  case_call_pair (case_call_pair m sp arg1 ra1) sp arg2 ra2=case_call_pair m sp arg2 ra2.
Proof.
  intros. assert (NO:~overlap 32 (msub 32 sp 48) 4 (msub 32 sp 44) 4).
  { apply sep_noverlap;left;rewrite stack_depth_difference;vm_compute;discriminate. }
  unfold case_call_pair.
  rewrite (setmem_swap 32 LittleE 4 4 (setmem 32 LittleE 4 m (msub 32 sp 44) arg1)
    (msub 32 sp 48) (msub 32 sp 44) ra1 arg2 NO).
  rewrite !call_setmem_shadow. reflexivity.
Qed.
Fixpoint case_call_history (m:memory) (sp:N) (calls:list (N*N)):memory:=
  match calls with
  | nil=>m
  | (arg,ra)::older=>case_call_pair (case_call_history m sp older) sp arg ra
  end.
Lemma case_call_history_shadow:forall calls m sp arg ra,
  case_call_pair (case_call_history m sp calls) sp arg ra=case_call_pair m sp arg ra.
Proof.
  induction calls as [|[oldarg oldra] older IH];intros m sp arg ra.
  - reflexivity.
  - cbn [case_call_history]. rewrite case_call_pair_shadow. apply IH.
Qed.

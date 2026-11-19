(* Linked code and shared unary stack interface for wctrans. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_stack2 i386_deep_stack i386_unary_call i386_binary_call
  i386_strings i386_stringcmp i386_wstringcmp strcmp_proof wctrans_i386 pc_thunk_bx_i386 strcmp_i386.
From Stdlib Require Import NArith Lia List Bool.
Import X86Notations.
Open Scope N.

Definition wctrans_linked : program := updateall2 wctrans_i386 (updateall2 pc_thunk_bx_i386 strcmp_i386).
Lemma wctrans_linked_caller : wctrans_i386 ⊆2 wctrans_linked.
Proof.
  intros s a insn H. unfold wctrans_linked,updateall2,updateall,wctrans_i386,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma wctrans_linked_strcmp : strcmp_i386 ⊆2 wctrans_linked.
Proof. intros s a insn H. unfold wctrans_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma wctrans_linked_thunk : pc_thunk_bx_i386 ⊆2 wctrans_linked.
Proof.
  intros s a insn H. unfold wctrans_linked,updateall2,updateall,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem wctrans_linked_welltyped : welltyped_prog x86typctx wctrans_linked.
Proof.
  intros s a. unfold wctrans_linked,updateall2,updateall.
  destruct (strcmp_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (strcmp_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply wctrans_i386.welltyped.
Qed.



Definition wctrans_got:N:=0xb4f9c.
Definition wctrans_target (second:bool):N:=if second then 0xb3068 else 0xb3060.
Definition wctrans_ra (second:bool):N:=if second then 0x4f88b else 0x4f867.
Definition wctrans_letter (second:bool) (i:N):N:=match i with
  | 0=>116 | 1=>111 | 2=>if second then 108 else 117
  | 3=>if second then 111 else 112 | 4=>if second then 119 else 112
  | 5=>101 | 6=>114 | _=>0 end.
Definition wctrans_matches (s0:store) (second:bool):=forall i,i<=7 ->
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i)=wctrans_letter second i.
Definition wctrans_matchb (s0:store) (second:bool):=
  forallb (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i)=?wctrans_letter second i)
    (0::1::2::3::4::5::6::7::nil).
Lemma wctrans_matchb_spec:forall s0 second,wctrans_matchb s0 second=true <->wctrans_matches s0 second.
Proof.
  intros s0 second. unfold wctrans_matchb,wctrans_matches. rewrite forallb_forall. split.
  - intros H i I. apply N.eqb_eq. apply H.
    assert (i=0 \/i=1 \/i=2 \/i=3 \/i=4 \/i=5 \/i=6 \/i=7) by lia.
    simpl. intuition congruence.
  - intros H i I. apply N.eqb_eq. apply H. simpl in I. intuition subst;lia.
Qed.
Lemma wctrans_letter_nonzero:forall second i,i<7 ->wctrans_letter second i<>0.
Proof.
  intros second i I. assert (E:i=0 \/i=1 \/i=2 \/i=3 \/i=4 \/i=5 \/i=6) by lia.
  repeat destruct E as [E|E];subst i;destruct second;discriminate.
Qed.
Definition wctrans_pre (s0:store):=models x86typctx s0 /\
  binary_string_avoids s0 1 (cdecl_arg s0) /\
  (forall second,binary_string_avoids s0 1 (wctrans_target second)) /\
  (forall second i,i<=7 ->getmem 32 LittleE 1 (s0 V_MEM32) (wctrans_target second+i)=wctrans_letter second i).
Definition wctrans_spec (s0:store):N:=if wctrans_matchb s0 false then 1 else if wctrans_matchb s0 true then 2 else 0.
Lemma wctrans_compare_zero:forall s0 second value,wctrans_pre s0 ->
  string_compare_result (s0 V_MEM32) (cdecl_arg s0) (wctrans_target second) value ->
  (value=0 <->wctrans_matchb s0 second=true).
Proof.
  intros s0 second value (_ & A & B & DATA) (k & K & PREFIX & STOP & VALUE).
  pose proof (string_equal_prefix_right _ _ _ _ PREFIX) as NZQ.
  assert (K7:k<=7).
  { destruct (N.le_gt_cases k 7);[assumption|]. exfalso.
    pose proof (NZQ 7 ltac:(lia)) as NZ. rewrite DATA in NZ by lia. exact (NZ eq_refl). }
  rewrite wctrans_matchb_spec. split.
  - intro ZERO. rewrite ZERO in VALUE. symmetry in VALUE. apply msub_move_0_r in VALUE. psimpl in VALUE.
    assert (PZERO:getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)=0) by tauto.
    assert (EQ7:k=7).
    { destruct (N.eq_dec k 7);[assumption|].
      pose proof (wctrans_letter_nonzero second k ltac:(lia)) as NZ.
      rewrite VALUE,DATA in PZERO by lia. contradiction. }
    subst k. intros i I. destruct (N.lt_ge_cases i 7).
    + rewrite (proj1 PREFIX i H),DATA by lia. reflexivity.
    + replace i with 7 by lia. exact PZERO.
  - intro MATCH. assert (EQ7:k=7).
    { destruct (N.eq_dec k 7);[assumption|]. exfalso.
      pose proof (wctrans_letter_nonzero second k ltac:(lia)) as NZ.
      rewrite MATCH,DATA in STOP by lia. tauto. }
    subst k. rewrite MATCH,DATA in VALUE by lia. exact VALUE.
Qed.
Definition wctrans_m1:=unary_m1.
Definition wctrans_m2 (s0:store):=unary_m2 s0 0x4f84e.
Definition wctrans_args_on (s0:store) (m:memory) (second:bool):=
  setmem 32 LittleE 4 (setmem 32 LittleE 4 m (msub 32 (s0 R_ESP) 24) (wctrans_target second))
    (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition wctrans_entry_on (s0:store) (m:memory) (second:bool):=
  setmem 32 LittleE 4 (wctrans_args_on s0 m second) (msub 32 (s0 R_ESP) 32) (wctrans_ra second).
Definition wctrans_after_on (s0:store) (m:memory) (second:bool):=
  setmem 32 LittleE 4 (setmem 32 LittleE 4 (wctrans_entry_on s0 m second)
    (msub 32 (s0 R_ESP) 36) (s0 R_ESI)) (msub 32 (s0 R_ESP) 40) wctrans_got.
Definition wctrans_before (s0:store) (second:bool):=
  if second then wctrans_after_on s0 (wctrans_m2 s0) false else wctrans_m2 s0.
Definition wctrans_args (s0:store) (second:bool):=wctrans_args_on s0 (wctrans_before s0 second) second.
Definition wctrans_entry (s0:store) (second:bool):=wctrans_entry_on s0 (wctrans_before s0 second) second.
Definition wctrans_after (s0:store) (second:bool):=wctrans_after_on s0 (wctrans_before s0 second) second.
Definition wctrans_memory (s0:store):=if wctrans_matchb s0 false then wctrans_after s0 false else wctrans_after s0 true.
Definition wctrans_reference (s0:store):=s0[V_MEM32:=wctrans_memory s0].
Definition wctrans_frame:=unary_frame.
Lemma wctrans_callee_args:forall s0 second sc,wctrans_frame s0 (wctrans_entry s0 second) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ strcmp_arg2 sc=wctrans_target second.
Proof.
  intros s0 second sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. unfold strcmp_arg2 at 1. rewrite MEM,SP. psimpl.
  unfold wctrans_entry,wctrans_entry_on,wctrans_args_on. split;rewrite !deep_saved_word_frame by lia;
    rewrite getmem_setmem by lia;apply N.mod_small.
  - unfold cdecl_arg;apply getmem_bound.
  - destruct second;vm_compute;reflexivity.
Qed.
Lemma wctrans_callee_memory:forall s0 second sc,wctrans_frame s0 (wctrans_entry s0 second) 32 sc ->
  sc R_EBX=wctrans_got ->save_si_bx_memory sc=wctrans_after s0 second.
Proof.
  intros s0 second sc (MEM & SP & SI & DI & BP & RD & WR) BX.
  unfold save_si_bx_memory. rewrite MEM,SP,SI,BX. psimpl. reflexivity.
Qed.
Lemma wctrans_call_return:forall s0 second sc value x se,
  wctrans_frame s0 (wctrans_entry s0 second) 32 sc ->sc R_EBX=wctrans_got ->
  cdecl_returned (save_si_bx_reference sc) value x se ->
  x=Addr (wctrans_ra second) /\ wctrans_frame s0 (wctrans_after s0 second) 28 se /\
  se R_EBX=wctrans_got /\ se R_EAX=value.
Proof.
  intros s0 second sc value x se F BX RETURN.
  pose proof (wctrans_callee_memory s0 second sc F BX) as MM.
  pose proof (save_si_bx_stack_word sc 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,save_si_bx_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold wctrans_entry,wctrans_entry_on in PC. rewrite getmem_setmem in PC by lia.
  split;[destruct second;exact PC|]. split.
  - unfold wctrans_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
Lemma wctrans_outer_stack:forall s0 second off,off<=8 ->
  getmem 32 LittleE 4 (wctrans_after s0 second) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 second off OFF. destruct second;unfold wctrans_after,wctrans_entry,wctrans_args,wctrans_before,wctrans_after_on,wctrans_entry_on,wctrans_args_on,wctrans_m2,unary_m2,unary_m1,save_ebx_memory;
    rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma wctrans_saved_bx:forall s0 second,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (wctrans_after s0 second) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 second BOUND. destruct second;unfold wctrans_after,wctrans_entry,wctrans_args,wctrans_before,wctrans_after_on,wctrans_entry_on,wctrans_args_on,wctrans_m2,unary_m2,unary_m1;
    rewrite !deep_saved_word_frame by lia;apply saved_ebx_load;exact BOUND.
Qed.
Lemma wctrans_before_stack:forall s0 second off,off<=8 ->
  getmem 32 LittleE 4 (wctrans_before s0 second) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 [|] off OFF.
  - apply (wctrans_outer_stack s0 false off OFF).
  - apply unary_m2_stack;exact OFF.
Qed.
Lemma wctrans_entry_read:forall s0 second p k,binary_string_avoids s0 1 p ->
  nonzero_prefix (s0 V_MEM32) p k ->
  getmem 32 LittleE 1 (wctrans_entry s0 second) (p+k)=getmem 32 LittleE 1 (s0 V_MEM32) (p+k).
Proof.
  intros s0 second p k AVOID PREFIX.
  pose proof (AVOID k ltac:(apply call_prefix_byte;exact PREFIX)) as NO.
  rewrite N.mul_1_l in NO.
  assert (CELL:forall depth,4<=depth ->depth<=40 ->
    ~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (p+k) 1).
  { intros depth LO HI. eapply descending_stack_subregion;[exact HI|exact LO|exact NO]. }
  destruct second;unfold wctrans_after,wctrans_entry,wctrans_args,wctrans_before,wctrans_after_on,wctrans_entry_on,wctrans_args_on,wctrans_m2,unary_m2,unary_m1,save_ebx_memory;
    rewrite !getmem_noverlap by (apply noverlap_symmetry;apply CELL;lia);reflexivity.
Qed.
Lemma wctrans_prefix_back:forall s0 second p k,binary_string_avoids s0 1 p ->
  nonzero_prefix (wctrans_entry s0 second) p k ->nonzero_prefix (s0 V_MEM32) p k.
Proof.
  intros s0 second p k AVOID PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (p+i))
    (fun i=>getmem 32 LittleE 1 (wctrans_entry s0 second) (p+i)) _ k PREFIX).
  intros j P. apply wctrans_entry_read;assumption.
Qed.
Lemma wctrans_callee_pre:forall s0 second sc,wctrans_pre s0 ->models x86typctx sc ->
  wctrans_frame s0 (wctrans_entry s0 second) 32 sc ->strcmp_pre sc.
Proof.
  intros s0 second sc (_ & P & Q & DATA) MDL FRAME.
  destruct (wctrans_callee_args s0 second sc FRAME) as [ARG1 ARG2].
  split;[exact MDL|]. rewrite ARG1,ARG2.
  assert (AVOID:forall p,binary_string_avoids s0 1 p ->string_avoids_saves sc p).
  { intros p AVOID k PREFIX. rewrite (proj1 FRAME) in PREFIX.
    pose proof (wctrans_prefix_back s0 second p k AVOID PREFIX) as ORIGINAL.
    pose proof (AVOID k ltac:(apply call_prefix_byte;exact ORIGINAL)) as NO.
    rewrite N.mul_1_l in NO. rewrite (proj1 (proj2 FRAME)). psimpl. split;
      eapply descending_stack_subregion;[| |exact NO| | |exact NO];lia. }
  split;apply AVOID;auto.
Qed.
Lemma wctrans_callee_result:forall s0 second sc value,wctrans_pre s0 ->
  wctrans_frame s0 (wctrans_entry s0 second) 32 sc ->
  string_compare_result (sc V_MEM32) (cdecl_arg sc) (strcmp_arg2 sc) value ->
  (value=0 <->wctrans_matchb s0 second=true).
Proof.
  intros s0 second sc value PRE FRAME RESULT.
  destruct (wctrans_callee_args s0 second sc FRAME) as [ARG1 ARG2].
  rewrite ARG1,ARG2,(proj1 FRAME) in RESULT.
  destruct PRE as (MDL & P & Q & DATA).
  destruct RESULT as (k & K & PREFIX & STOP & VALUE).
  pose proof (proj2 PREFIX) as NZP.
  pose proof (string_equal_prefix_right _ _ _ _ PREFIX) as NZQ.
  assert (READ:forall p,binary_string_avoids s0 1 p ->
    nonzero_prefix (wctrans_entry s0 second) p k ->forall i,i<=k ->
    getmem 32 LittleE 1 (wctrans_entry s0 second) (p+i)=getmem 32 LittleE 1 (s0 V_MEM32) (p+i)).
  { intros p AVOID NZ i I. apply wctrans_entry_read;[exact AVOID|].
    pose proof (wctrans_prefix_back s0 second p k AVOID NZ) as ORIGINAL.
    intros j J. apply ORIGINAL. clear - I J;lia. }
  pose proof (READ _ P NZP) as READP. pose proof (READ _ (Q second) NZQ) as READQ.
  apply wctrans_compare_zero;[repeat split;assumption|]. exists k. split;[exact K|]. split.
  - split.
    + intros i I. rewrite <- (READP i ltac:(lia)),<- (READQ i ltac:(lia)). exact (proj1 PREFIX i I).
    + exact (wctrans_prefix_back s0 second _ k P NZP).
  - rewrite <- (READP k (N.le_refl k)),<- (READQ k (N.le_refl k)). split;assumption.
Qed.

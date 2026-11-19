(* Nested PIC-call stack for wctrans_l -> wctrans -> strcmp. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call i386_strings
  wctrans_l_i386 wctrans_support wctrans_proof wctrans_i386 pc_thunk_bx_i386 strcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wctrans_l_linked:program:=updateall2 wctrans_l_i386 wctrans_linked.
Lemma wctrans_l_linked_caller:wctrans_l_i386 ⊆2 wctrans_l_linked.
Proof.
  intros s a insn H. unfold wctrans_l_linked,wctrans_linked,updateall2,updateall,
    wctrans_l_i386,wctrans_i386,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma wctrans_l_linked_wctrans:wctrans_linked ⊆2 wctrans_l_linked.
Proof. intros s a insn H. unfold wctrans_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem wctrans_l_linked_welltyped:welltyped_prog x86typctx wctrans_l_linked.
Proof.
  intros s a. unfold wctrans_l_linked,updateall2,updateall.
  destruct (wctrans_linked s a) as [[sz q]|] eqn:M.
  - pose proof (wctrans_linked_welltyped s a) as WT. rewrite M in WT. exact WT.
  - apply wctrans_l_i386.welltyped.
Qed.

Definition wctrans_l_got:N:=0xb4f9c.
Definition wctrans_l_m1:=unary_m1.
Definition wctrans_l_m2 (s0:store):=unary_m2 s0 0x4f8e2.
Definition wctrans_l_m3 (s0:store):=unary_m3 s0 0x4f8e2.
Definition wctrans_l_m4 (s0:store):=unary_memory s0 0x4f8e2 0x4f8f4.
Definition wctrans_l_frame:=unary_frame.
(* A canonical entry store describes the exact nested memory without
   flattening or discarding either comparison's overwritten stack slots. *)
Definition wctrans_l_child (s0:store):=
  s0[V_MEM32:=wctrans_l_m4 s0][R_ESP:=msub 32 (s0 R_ESP) 32][R_EBX:=wctrans_l_got].
Definition wctrans_l_memory (s0:store):=wctrans_memory (wctrans_l_child s0).
Definition wctrans_l_reference (s0:store):=s0[V_MEM32:=wctrans_l_memory s0].
Definition wctrans_l_avoids (s0:store) (p:N):=forall k,nonzero_prefix (s0 V_MEM32) p k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 72) 72 (p+k) 1.
Definition wctrans_l_pre (s0:store):=models x86typctx s0 /\
  wctrans_l_avoids s0 (cdecl_arg s0) /\
  (forall second,wctrans_l_avoids s0 (wctrans_target second)) /\
  (forall second i,i<=7 ->getmem 32 LittleE 1 (s0 V_MEM32) (wctrans_target second+i)=wctrans_letter second i).
Lemma wctrans_l_child_frame:forall s0,wctrans_l_frame s0 (wctrans_l_m4 s0) 32 (wctrans_l_child s0).
Proof. intros. unfold wctrans_l_frame,unary_frame,wctrans_l_child. psimpl. repeat split;reflexivity. Qed.
Lemma wctrans_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wctrans_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma wctrans_l_entry_read:forall s0 p k,wctrans_l_avoids s0 p ->nonzero_prefix (s0 V_MEM32) p k ->
  getmem 32 LittleE 1 (wctrans_l_m4 s0) (p+k)=getmem 32 LittleE 1 (s0 V_MEM32) (p+k).
Proof.
  intros s0 p k AVOID PREFIX. pose proof (AVOID k PREFIX) as NO.
  assert (CELL:forall depth,4<=depth ->depth<=72 ->
    ~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (p+k) 1).
  { intros depth LO HI. eapply descending_stack_subregion;[exact HI|exact LO|exact NO]. }
  unfold wctrans_l_m4,unary_memory,unary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite !getmem_noverlap by (apply noverlap_symmetry;apply CELL;lia). reflexivity.
Qed.
Lemma wctrans_l_prefix_back:forall s0 p k,wctrans_l_avoids s0 p ->
  nonzero_prefix (wctrans_l_m4 s0) p k ->nonzero_prefix (s0 V_MEM32) p k.
Proof.
  intros s0 p k AVOID PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (p+i))
    (fun i=>getmem 32 LittleE 1 (wctrans_l_m4 s0) (p+i)) _ k PREFIX).
  intros j P. apply wctrans_l_entry_read;assumption.
Qed.
Lemma wctrans_l_match:forall s0 sc second,wctrans_l_pre s0 ->
  wctrans_l_frame s0 (wctrans_l_m4 s0) 32 sc ->wctrans_matchb sc second=wctrans_matchb s0 second.
Proof.
  intros s0 sc second (_ & AVOID & Q & DATA) F.
  pose proof (unary_callee_arg s0 0x4f8e2 0x4f8f4 sc F) as ARG.
  assert (IFF:wctrans_matchb sc second=true <->wctrans_matchb s0 second=true).
  { rewrite !wctrans_matchb_spec. unfold wctrans_matches. rewrite ARG,(proj1 F). split;intro H.
    - assert (NZ:nonzero_prefix (wctrans_l_m4 s0) (cdecl_arg s0) 7).
      { intros i I. rewrite H by lia. apply wctrans_letter_nonzero;exact I. }
      pose proof (wctrans_l_prefix_back s0 _ 7 AVOID NZ) as ORIGINAL.
      intros i I. rewrite <- (wctrans_l_entry_read s0 _ i AVOID ltac:(intros j J;apply ORIGINAL;lia)). exact (H i I).
    - assert (NZ:nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) 7).
      { intros i I. rewrite H by lia. apply wctrans_letter_nonzero;exact I. }
      intros i I. rewrite (wctrans_l_entry_read s0 _ i AVOID ltac:(intros j J;apply NZ;lia)). exact (H i I). }
  destruct (wctrans_matchb sc second),(wctrans_matchb s0 second);intuition congruence.
Qed.
Lemma wctrans_l_spec_transport:forall s0 sc,wctrans_l_pre s0 ->
  wctrans_l_frame s0 (wctrans_l_m4 s0) 32 sc ->wctrans_spec sc=wctrans_spec s0.
Proof. intros. unfold wctrans_spec. rewrite !(wctrans_l_match s0 sc _ H H0). reflexivity. Qed.
Lemma wctrans_l_callee_pre:forall s0 sc,wctrans_l_pre s0 ->models x86typctx sc ->
  wctrans_l_frame s0 (wctrans_l_m4 s0) 32 sc ->wctrans_pre sc.
Proof.
  intros s0 sc (_ & P & Q & DATA) MDL F.
  pose proof (unary_callee_arg s0 0x4f8e2 0x4f8f4 sc F) as ARG.
  assert (AVOID:forall p,wctrans_l_avoids s0 p ->binary_string_avoids sc 1 p).
  { intros p A k PREFIX. apply call_prefix_byte in PREFIX. rewrite (proj1 F) in PREFIX.
    pose proof (wctrans_l_prefix_back s0 p k A PREFIX) as ORIGINAL.
    pose proof (A k ORIGINAL) as NO. rewrite N.mul_1_l,(proj1 (proj2 F)). psimpl.
    eapply descending_stack_subregion;[| |exact NO];lia. }
  split;[exact MDL|]. rewrite ARG. split;[apply AVOID;exact P|]. split.
  - intros second. apply AVOID;exact (Q second).
  - intros second i I. rewrite (proj1 F).
    rewrite wctrans_l_entry_read;[exact (DATA second i I)|exact (Q second)|].
    intros j J. rewrite DATA by lia. apply wctrans_letter_nonzero;lia.
Qed.
Lemma wctrans_l_callee_memory:forall s0 sc,wctrans_l_frame s0 (wctrans_l_m4 s0) 32 sc ->
  sc R_EBX=wctrans_l_got ->wctrans_memory sc=wctrans_l_memory s0.
Proof.
  intros s0 sc F BX.
  pose proof (unary_callee_arg s0 0x4f8e2 0x4f8f4 sc F) as ARG.
  pose proof (unary_callee_arg s0 0x4f8e2 0x4f8f4 (wctrans_l_child s0) (wctrans_l_child_frame s0)) as CARG.
  assert (MATCH:forall second,wctrans_matchb sc second=wctrans_matchb (wctrans_l_child s0) second).
  { intro second. unfold wctrans_matchb. rewrite ARG,CARG,(proj1 F). unfold wctrans_l_child. psimpl. reflexivity. }
  unfold wctrans_l_memory,wctrans_memory. rewrite MATCH. destruct (wctrans_matchb (wctrans_l_child s0) false);
    unfold wctrans_after,wctrans_before,wctrans_after_on,wctrans_entry_on,wctrans_args_on,wctrans_m2,
      unary_m2,unary_m1,save_ebx_memory;
    rewrite ARG,CARG;destruct F as (MEM & SP & SI & DI & BP & RD & WR);
    unfold wctrans_l_child;psimpl;rewrite MEM,SP,SI,BX;psimpl;reflexivity.
Qed.
Lemma wctrans_l_after_stack:forall sc second off,off<=64 ->
  getmem 32 LittleE 4 (wctrans_after sc second) (off+sc R_ESP)=getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof.
  intros sc second off OFF. destruct second;
    unfold wctrans_after,wctrans_entry,wctrans_args,wctrans_before,wctrans_after_on,wctrans_entry_on,wctrans_args_on,
      wctrans_m2,unary_m2,unary_m1,save_ebx_memory;
    rewrite (N.add_comm off (sc R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma wctrans_l_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (wctrans_l_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold wctrans_l_memory,wctrans_memory.
  destruct (wctrans_matchb (wctrans_l_child s0) false).
  - pose proof (wctrans_l_after_stack (wctrans_l_child s0) false 28 ltac:(lia)) as READ.
    unfold wctrans_l_child in READ. psimpl in READ. unfold wctrans_l_child. rewrite READ. apply unary_saved_bx;exact BOUND.
  - pose proof (wctrans_l_after_stack (wctrans_l_child s0) true 28 ltac:(lia)) as READ.
    unfold wctrans_l_child in READ. psimpl in READ. unfold wctrans_l_child. rewrite READ. apply unary_saved_bx;exact BOUND.
Qed.
Lemma wctrans_l_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wctrans_l_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold wctrans_l_memory,wctrans_memory.
  destruct (wctrans_matchb (wctrans_l_child s0) false).
  - pose proof (wctrans_l_after_stack (wctrans_l_child s0) false (32+off) ltac:(lia)) as READ.
    unfold wctrans_l_child in READ. psimpl in READ. unfold wctrans_l_child.
    rewrite READ. apply unary_outer_stack;exact OFF.
  - pose proof (wctrans_l_after_stack (wctrans_l_child s0) true (32+off) ltac:(lia)) as READ.
    unfold wctrans_l_child in READ. psimpl in READ. unfold wctrans_l_child.
    rewrite READ. apply unary_outer_stack;exact OFF.
Qed.
Lemma wctrans_l_call_return:forall s0 sc x se,wctrans_l_pre s0 ->
  wctrans_l_frame s0 (wctrans_l_m4 s0) 32 sc ->sc R_EBX=wctrans_l_got ->
  cdecl_returned (wctrans_reference sc) (wctrans_spec sc) x se ->
  x=Addr 0x4f8f4 /\ wctrans_l_frame s0 (wctrans_l_memory s0) 28 se /\
  se R_EBX=wctrans_l_got /\ se R_EAX=wctrans_spec s0.
Proof.
  intros s0 sc x se PRE F BX RETURN.
  pose proof (wctrans_l_callee_memory s0 sc F BX) as MM.
  pose proof (wctrans_l_spec_transport s0 sc PRE F) as SPEC.
  assert (RA:getmem 32 LittleE 4 (wctrans_memory sc) (sc R_ESP)=getmem 32 LittleE 4 (sc V_MEM32) (sc R_ESP)).
  { unfold wctrans_memory. destruct (wctrans_matchb sc false).
    - exact (wctrans_l_after_stack sc false 0 ltac:(lia)).
    - exact (wctrans_l_after_stack sc true 0 ltac:(lia)). }
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,wctrans_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,SPEC,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold wctrans_l_m4 in PC. rewrite unary_call_address in PC. split;[exact PC|]. split.
  - unfold wctrans_l_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.

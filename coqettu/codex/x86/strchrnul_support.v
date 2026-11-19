(* Linked code and shared unary stack interface for strchrnul. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_stack4 i386_unary_call
  i386_binary_call i386_strings i386_byte_search i386_search_arith strlen_proof strchrnul_i386 pc_thunk_bx_i386 strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition strchrnul_linked : program := updateall2 strchrnul_i386 (updateall2 pc_thunk_bx_i386 strlen_i386).
Lemma strchrnul_linked_caller : strchrnul_i386 ⊆2 strchrnul_linked.
Proof.
  intros s a insn H. unfold strchrnul_linked,updateall2,updateall,strchrnul_i386,pc_thunk_bx_i386,strlen_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma strchrnul_linked_strlen : strlen_i386 ⊆2 strchrnul_linked.
Proof. intros s a insn H. unfold strchrnul_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma strchrnul_linked_thunk : pc_thunk_bx_i386 ⊆2 strchrnul_linked.
Proof.
  intros s a insn H. unfold strchrnul_linked,updateall2,updateall,pc_thunk_bx_i386,strlen_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem strchrnul_linked_welltyped : welltyped_prog x86typctx strchrnul_linked.
Proof.
  intros s a. unfold strchrnul_linked,updateall2,updateall.
  destruct (strlen_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (strlen_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply strchrnul_i386.welltyped.
Qed.



Definition strchrnul_got:N:=0xb4f9c.
Definition strchrnul_char (s0:store):=getmem 32 LittleE 1 (s0 V_MEM32) (8+s0 R_ESP).
Definition strchrnul_m1:=save4_registers.
Definition strchrnul_m2 (s0:store):=
  setmem 32 LittleE 4 (strchrnul_m1 s0) (msub 32 (s0 R_ESP) 20) 0x31409.
Definition strchrnul_m3 (s0:store):=
  setmem 32 LittleE 4 (strchrnul_m2 s0) (msub 32 (s0 R_ESP) 44) (cdecl_arg s0).
Definition strchrnul_m4 (s0:store):=
  setmem 32 LittleE 4 (strchrnul_m3 s0) (msub 32 (s0 R_ESP) 48) 0x31441.
Definition strchrnul_snapshot (s0:store) (called:bool):=if called then strchrnul_m4 s0 else strchrnul_m2 s0.
Definition strchrnul_memory (s0:store):=strchrnul_snapshot s0 (strchrnul_char s0=?0).
Definition strchrnul_reference (s0:store):=s0[V_MEM32:=strchrnul_memory s0].
Definition strchrnul_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\ s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition strchrnul_pre (s0:store):=models x86typctx s0 /\ forall k,
  nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 48) 48 (cdecl_arg s0+k) 4.
Definition strchrnul_prefix (s0:store) (k:N):=
  nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k /\
  nonmatching_prefix (s0 V_MEM32) (cdecl_arg s0) (strchrnul_char s0) k.
Definition strchrnul_result (s0:store) (result:N):=exists k,strchrnul_prefix s0 k /\
  (getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)=0 \/
   getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)=strchrnul_char s0) /\ result=(cdecl_arg s0+k) mod 2^32.
Lemma strchrnul_char_bound:forall s0,strchrnul_char s0<256.
Proof. intro. unfold strchrnul_char;apply getmem_bound. Qed.
Lemma strchrnul_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (strchrnul_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strchrnul_m2,strchrnul_m1,save4_registers.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma strchrnul_m2_char:forall s0,
  getmem 32 LittleE 1 (strchrnul_m2 s0) (8+s0 R_ESP)=strchrnul_char s0.
Proof.
  intro s0. pose proof (strchrnul_m2_stack s0 8 ltac:(lia)) as WORD.
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. rewrite !getmem_mod in WORD. exact WORD.
Qed.
Lemma strchrnul_snapshot_stack:forall s0 called off,off<=8 ->
  getmem 32 LittleE 4 (strchrnul_snapshot s0 called) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 [|] off OFF;unfold strchrnul_snapshot,strchrnul_m4,strchrnul_m3,strchrnul_m2,strchrnul_m1,save4_registers;
    rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strchrnul_resave_arg:forall s0,
  setmem 32 LittleE 4 (strchrnul_m3 s0) (4+s0 R_ESP) (cdecl_arg s0)=strchrnul_m3 s0.
Proof.
  intro s0. assert (READ:getmem 32 LittleE 4 (strchrnul_m3 s0) (4+s0 R_ESP)=cdecl_arg s0).
  { unfold strchrnul_m3. rewrite (N.add_comm 4 (s0 R_ESP)),deep_stack_word_frame by lia.
    rewrite (N.add_comm (s0 R_ESP) 4),strchrnul_m2_stack by lia. reflexivity. }
  rewrite <- READ. apply setmem_getmem.
Qed.
Lemma strchrnul_read_word:forall s0 called k,strchrnul_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 4 (strchrnul_snapshot s0 called) (cdecl_arg s0+k)=
  getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros s0 called k (_ & AVOID) PREFIX. pose proof (AVOID k PREFIX) as NO.
  assert (CELL:forall depth,4<=depth ->depth<=48 ->
    ~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (cdecl_arg s0+k) 4).
  { intros depth LO HI. eapply descending_stack_subregion;[exact HI|exact LO|exact NO]. }
  destruct called;unfold strchrnul_snapshot,strchrnul_m4,strchrnul_m3,strchrnul_m2,strchrnul_m1,save4_registers;
    rewrite !getmem_noverlap by (apply noverlap_symmetry;apply CELL;lia);reflexivity.
Qed.
Lemma strchrnul_read_byte:forall s0 called k,strchrnul_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 1 (strchrnul_snapshot s0 called) (cdecl_arg s0+k)=
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros. pose proof (strchrnul_read_word s0 called k H H0) as WORD.
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. rewrite !getmem_mod in WORD. exact WORD.
Qed.
Lemma strchrnul_callee_arg:forall s0 sc,strchrnul_frame s0 (strchrnul_m4 s0) 48 sc ->cdecl_arg sc=cdecl_arg s0.
Proof.
  intros s0 sc (MEM & SP & RD & WR). unfold cdecl_arg at 1. rewrite MEM,SP. psimpl.
  unfold strchrnul_m4,strchrnul_m3. rewrite deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. apply N.mod_small. unfold cdecl_arg;apply getmem_bound.
Qed.
Lemma strchrnul_first_transport:forall s0 sc n,strchrnul_pre s0 ->strchrnul_frame s0 (strchrnul_m4 s0) 48 sc ->
  first_nul (sc V_MEM32) (cdecl_arg sc) n ->first_nul (s0 V_MEM32) (cdecl_arg s0) n.
Proof.
  intros s0 sc n PRE FRAME FIRST. rewrite (strchrnul_callee_arg s0 sc FRAME),(proj1 FRAME) in FIRST.
  destruct FIRST as (BOUND & PREFIX & ZERO).
  assert (ORIGINAL:nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) n).
  { refine (conditional_prefix_transfer
      (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i))
      (fun i=>getmem 32 LittleE 1 (strchrnul_m4 s0) (cdecl_arg s0+i)) _ n PREFIX).
    intros j P. exact (strchrnul_read_byte s0 true j PRE P). }
  pose proof (strchrnul_read_byte s0 true n PRE ORIGINAL) as READ.
  change (getmem 32 LittleE 1 (strchrnul_m4 s0) (cdecl_arg s0+n)=
    getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+n)) in READ.
  rewrite READ in ZERO. repeat split;assumption.
Qed.
Lemma strchrnul_call_return:forall s0 sc value x se,strchrnul_frame s0 (strchrnul_m4 s0) 48 sc ->
  cdecl_returned sc value x se ->x=Addr 0x31441 /\ strchrnul_frame s0 (strchrnul_m4 s0) 44 se /\ se R_EAX=value.
Proof.
  intros s0 sc value x se (MEM & SP & RD & WR) RETURN. unfold cdecl_returned in RETURN.
  rewrite MEM,SP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & BX & SI & DI & BP & READ & WRITE).
  unfold strchrnul_m4 in PC. rewrite getmem_setmem in PC by lia. cbn in PC.
  split;[exact PC|]. split;[|exact AX]. unfold strchrnul_frame.
  rewrite MM,ESP,READ,WRITE. psimpl. repeat split;reflexivity.
Qed.
Lemma strchrnul_prefix_step1:forall s0 k,strchrnul_prefix s0 k ->
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)<>0 ->
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)<>strchrnul_char s0 ->strchrnul_prefix s0 (k+1).
Proof.
  intros s0 k [PREFIX MATCH] NZ NE. split.
  - apply prefix_advance1;[exact PREFIX|]. rewrite getmem_mod_l. exact NZ.
  - apply nonmatching_prefix_advance1;[exact MATCH|]. rewrite getmem_mod_l. exact NE.
Qed.
Lemma strchrnul_prefix_step4:forall s0 k,strchrnul_prefix s0 k ->
  zero_mask32 (getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+k))=0 ->
  zero_mask32 (N.lxor (getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+k))
    (repeated_byte32 (strchrnul_char s0)))=0 ->strchrnul_prefix s0 (k+4).
Proof.
  intros s0 k [PREFIX MATCH] NZ NE. split.
  - apply prefix_advance4;[exact PREFIX|]. rewrite getmem_mod_l. exact NZ.
  - apply nonmatching_prefix_advance4;[apply strchrnul_char_bound|exact MATCH|]. rewrite getmem_mod_l. exact NE.
Qed.
Lemma strchrnul_zero_result:forall s0 n,strchrnul_char s0=0 ->first_nul (s0 V_MEM32) (cdecl_arg s0) n ->
  strchrnul_result s0 ((cdecl_arg s0+n) mod 2^32).
Proof.
  intros s0 n CHAR (BOUND & PREFIX & ZERO). exists n. split.
  - split;[exact PREFIX|]. rewrite CHAR. exact PREFIX.
  - split;[left;exact ZERO|reflexivity].
Qed.
Lemma strchrnul_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (strchrnul_memory s0) (msub 32 (s0 R_ESP) 16)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold strchrnul_memory,strchrnul_snapshot. destruct (strchrnul_char s0=?0);
    unfold strchrnul_m4,strchrnul_m3,strchrnul_m2,strchrnul_m1;
    rewrite !deep_saved_word_frame by lia;apply (save4_load_bx s0 None BOUND).
Qed.
Lemma strchrnul_saved_si:forall s0,s0 R_ESI<2^32 ->
  getmem 32 LittleE 4 (strchrnul_memory s0) (msub 32 (s0 R_ESP) 12)=s0 R_ESI.
Proof.
  intros s0 BOUND. unfold strchrnul_memory,strchrnul_snapshot. destruct (strchrnul_char s0=?0);
    unfold strchrnul_m4,strchrnul_m3,strchrnul_m2,strchrnul_m1;
    rewrite !deep_saved_word_frame by lia;apply (save4_load_si s0 None BOUND).
Qed.
Lemma strchrnul_saved_di:forall s0,s0 R_EDI<2^32 ->
  getmem 32 LittleE 4 (strchrnul_memory s0) (msub 32 (s0 R_ESP) 8)=s0 R_EDI.
Proof.
  intros s0 BOUND. unfold strchrnul_memory,strchrnul_snapshot. destruct (strchrnul_char s0=?0);
    unfold strchrnul_m4,strchrnul_m3,strchrnul_m2,strchrnul_m1;
    rewrite !deep_saved_word_frame by lia;apply (save4_load_di s0 None BOUND).
Qed.
Lemma strchrnul_saved_bp:forall s0,s0 R_EBP<2^32 ->
  getmem 32 LittleE 4 (strchrnul_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBP.
Proof.
  intros s0 BOUND. unfold strchrnul_memory,strchrnul_snapshot. destruct (strchrnul_char s0=?0);
    unfold strchrnul_m4,strchrnul_m3,strchrnul_m2,strchrnul_m1;
    rewrite !deep_saved_word_frame by lia;apply (save4_load_bp s0 None BOUND).
Qed.
Definition strchrnul_mask (x y:N):=
  N.land (N.lor (N.land (msub 32 y 16843009) (N.lnot y 32))
    (N.land (msub 32 x 16843009) (N.lnot x 32))) 2155905152.
Lemma strchrnul_mask_parts:forall x y,strchrnul_mask x y=0 ->zero_mask32 x=0 /\ zero_mask32 y=0.
Proof.
  intros x y MASK. unfold strchrnul_mask in MASK.
  rewrite N.land_lor_distr_l,!zero_mask32_machine in MASK.
  apply N.lor_eq_0_iff in MASK. destruct MASK as [Y X]. exact (conj X Y).
Qed.
Lemma strchrnul_found:forall s0 k,strchrnul_prefix s0 k ->
  (getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)=0 \/
   getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)=strchrnul_char s0) ->
  strchrnul_result s0 ((cdecl_arg s0+k) mod 2^32).
Proof. intros. exists k. split;[exact H|]. split;[exact H0|reflexivity]. Qed.

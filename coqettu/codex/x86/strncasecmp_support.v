(* Linked code and shared unary stack interface for strncasecmp. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_stack2 i386_deep_stack i386_unary_call i386_binary_call
  i386_strings i386_casecmp i386_casecmp_bounded i386_call_pair tolower_proof strncasecmp_i386 pc_thunk_ax_i386 tolower_i386.
From Stdlib Require Import NArith Lia List Bool.
Import X86Notations.
Open Scope N.

Definition strncasecmp_linked : program := updateall2 strncasecmp_i386 (updateall2 pc_thunk_ax_i386 tolower_i386).
Lemma strncasecmp_linked_caller : strncasecmp_i386 ⊆2 strncasecmp_linked.
Proof.
  intros s a insn H. unfold strncasecmp_linked,updateall2,updateall,strncasecmp_i386,pc_thunk_ax_i386,tolower_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma strncasecmp_linked_tolower : tolower_i386 ⊆2 strncasecmp_linked.
Proof. intros s a insn H. unfold strncasecmp_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma strncasecmp_linked_thunk : pc_thunk_ax_i386 ⊆2 strncasecmp_linked.
Proof.
  intros s a insn H. unfold strncasecmp_linked,updateall2,updateall,pc_thunk_ax_i386,tolower_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem strncasecmp_linked_welltyped : welltyped_prog x86typctx strncasecmp_linked.
Proof.
  intros s a. unfold strncasecmp_linked,updateall2,updateall.
  destruct (tolower_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (tolower_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_ax_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_ax_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply strncasecmp_i386.welltyped.
Qed.



Definition strncasecmp_got:N:=0xb4f9c.
Definition strncasecmp_count (s0:store):=getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).
Definition strncasecmp_p (s0:store) (k:N):=getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Definition strncasecmp_q (s0:store) (k:N):=getmem 32 LittleE 1 (s0 V_MEM32) (binary_arg2 s0+k).
Definition strncasecmp_prefix (s0:store) (k:N):=case_equal_prefix (s0 V_MEM32) (cdecl_arg s0) (binary_arg2 s0) k.
Definition strncasecmp_diff (s0:store) (k:N):=msub 32 (tolower_spec (strncasecmp_p s0 k)) (tolower_spec (strncasecmp_q s0 k)).
Definition strncasecmp_stop (s0:store) (k:N):=k+1=strncasecmp_count s0 \/strncasecmp_p s0 k=0 \/
  strncasecmp_q s0 k=0 \/tolower_spec (strncasecmp_p s0 k)<>tolower_spec (strncasecmp_q s0 k).
Definition strncasecmp_pic (s0:store):=setmem 32 LittleE 4 (s0 V_MEM32) (msub 32 (s0 R_ESP) 4) 0x761b9.
Definition strncasecmp_base (s0:store):=setmem 32 LittleE 4 (save4_registers s0) (msub 32 (s0 R_ESP) 32) strncasecmp_got.
Definition strncasecmp_countbase (s0:store) (called:bool):=if called then
  setmem 32 LittleE 4 (strncasecmp_base s0) (msub 32 (s0 R_ESP) 36) (strncasecmp_count s0-1) else strncasecmp_base s0.
Definition strncasecmp_pair (s0:store) (m:memory) (arg ra:N):=
  setmem 32 LittleE 4 (setmem 32 LittleE 4 m (msub 32 (s0 R_ESP) 60) arg) (msub 32 (s0 R_ESP) 64) ra.
Definition strncasecmp_memory (s0:store) (called:bool) (last:option (N*N)):=match last with
  | None=>strncasecmp_countbase s0 called
  | Some (arg,ra)=>strncasecmp_pair s0 (strncasecmp_countbase s0 called) arg ra end.
Definition strncasecmp_argmem (s0:store) (called:bool) (last:option (N*N)) (arg:N):=
  setmem 32 LittleE 4 (strncasecmp_memory s0 called last) (msub 32 (s0 R_ESP) 60) arg.
Definition strncasecmp_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\ s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition strncasecmp_avoids (s0:store) (p:N):=forall k,k<strncasecmp_count s0 ->nonzero_prefix (s0 V_MEM32) p k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 64) 64 (p+k) 1.
Definition strncasecmp_pre (s0:store):=models x86typctx s0 /\ strncasecmp_avoids s0 (cdecl_arg s0) /\
  strncasecmp_avoids s0 (binary_arg2 s0).
Definition strncasecmp_result (s0:store) (value:N):=
  bounded_case_compare_result (s0 V_MEM32) (cdecl_arg s0) (binary_arg2 s0) (strncasecmp_count s0) value.
Definition strncasecmp_outcome (s0:store) (called:bool) (stop:option N) (value:N):=match stop with
  | None=>strncasecmp_count s0=0 /\ called=false /\ value=0
  | Some k=>k<strncasecmp_count s0 /\ strncasecmp_prefix s0 k /\ strncasecmp_stop s0 k /\ value=strncasecmp_diff s0 k end.
Definition strncasecmp_endmem (s0:store) (called:bool) (stop:option N):=
  strncasecmp_memory s0 called (match stop with None=>None|Some k=>Some (strncasecmp_q s0 k,0x7624f) end).
Definition strncasecmp_reference (s0:store) (called:bool) (stop:option N):=s0[V_MEM32:=strncasecmp_endmem s0 called stop].
Lemma strncasecmp_count_bound:forall s0,strncasecmp_count s0<2^32.
Proof. intros. unfold strncasecmp_count;apply getmem_bound. Qed.
Lemma strncasecmp_pair_as_case:forall s0 m arg ra,
  strncasecmp_pair s0 m arg ra=case_call_pair m (msub 32 (s0 R_ESP) 16) arg ra.
Proof. intros. unfold strncasecmp_pair,case_call_pair. psimpl. reflexivity. Qed.
Lemma strncasecmp_pair_shadow:forall s0 m arg1 ra1 arg2 ra2,
  strncasecmp_pair s0 (strncasecmp_pair s0 m arg1 ra1) arg2 ra2=strncasecmp_pair s0 m arg2 ra2.
Proof. intros. rewrite !strncasecmp_pair_as_case. apply case_call_pair_shadow. Qed.
Lemma strncasecmp_entry_memory:forall s0 called last arg ra,
  setmem 32 LittleE 4 (strncasecmp_argmem s0 called last arg) (msub 32 (s0 R_ESP) 64) ra=
  strncasecmp_memory s0 called (Some (arg,ra)).
Proof.
  intros s0 called last arg ra.
  change (strncasecmp_pair s0 (strncasecmp_memory s0 called last) arg ra=strncasecmp_memory s0 called (Some (arg,ra))).
  destruct last as [[oldarg oldra]|];cbn [strncasecmp_memory];[apply strncasecmp_pair_shadow|reflexivity].
Qed.
Lemma strncasecmp_slots_disjoint:forall sp i j,i<=64 ->j<=64 ->(i+4<=j \/j+4<=i) ->
  ~overlap 32 (msub 32 sp i) 4 (msub 32 sp j) 4.
Proof.
  intros sp i j I J SEP. apply sep_noverlap;left;rewrite stack_depth_difference;
    apply small_separated_difference;try assumption;tauto.
Qed.
Lemma strncasecmp_setcount_pair:forall s0 m arg ra,
  setmem 32 LittleE 4 (strncasecmp_pair s0 m arg ra) (msub 32 (s0 R_ESP) 36) (strncasecmp_count s0-1)=
  strncasecmp_pair s0 (setmem 32 LittleE 4 m (msub 32 (s0 R_ESP) 36) (strncasecmp_count s0-1)) arg ra.
Proof.
  intros. unfold strncasecmp_pair.
  rewrite (setmem_swap 32 LittleE 4 4 _ (msub 32 (s0 R_ESP) 64) (msub 32 (s0 R_ESP) 36)
    ra (strncasecmp_count s0-1)) by (apply strncasecmp_slots_disjoint;lia).
  rewrite (setmem_swap 32 LittleE 4 4 _ (msub 32 (s0 R_ESP) 60) (msub 32 (s0 R_ESP) 36)
    arg (strncasecmp_count s0-1)) by (apply strncasecmp_slots_disjoint;lia). reflexivity.
Qed.
Lemma strncasecmp_setcount:forall s0 called last,
  setmem 32 LittleE 4 (strncasecmp_memory s0 called last) (msub 32 (s0 R_ESP) 36) (strncasecmp_count s0-1)=
  strncasecmp_memory s0 true last.
Proof.
  intros s0 called [[arg ra]|];cbn [strncasecmp_memory];rewrite ?strncasecmp_setcount_pair;
    unfold strncasecmp_countbase;destruct called;rewrite ?call_setmem_shadow;reflexivity.
Qed.
Lemma strncasecmp_outer_stack:forall s0 called last off,off<=12 ->
  getmem 32 LittleE 4 (strncasecmp_memory s0 called last) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 called [[arg ra]|] off OFF;unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;
    destruct called;unfold strncasecmp_base,save4_registers;
    rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strncasecmp_resave_arg:forall s0 called last,
  setmem 32 LittleE 4 (strncasecmp_memory s0 called last) (4+s0 R_ESP) (cdecl_arg s0)=strncasecmp_memory s0 called last.
Proof.
  intros s0 called last. pose proof (strncasecmp_outer_stack s0 called last 4 ltac:(lia)) as READ.
  fold (cdecl_arg s0) in READ. rewrite <- READ. apply setmem_getmem.
Qed.
Lemma strncasecmp_read:forall s0 called last p k,strncasecmp_avoids s0 p ->k<strncasecmp_count s0 ->
  nonzero_prefix (s0 V_MEM32) p k ->
  getmem 32 LittleE 1 (strncasecmp_memory s0 called last) (p+k)=getmem 32 LittleE 1 (s0 V_MEM32) (p+k).
Proof.
  intros s0 called [[arg ra]|] p k AVOID K PREFIX. all: pose proof (AVOID k K PREFIX) as NO.
  all: unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;destruct called;
    unfold strncasecmp_base,save4_registers.
  all: replace (p+k) with ((p+k)+0) by lia.
  all: rewrite !descending_stack_read with (total:=64) (n:=1) by (try exact NO;lia);reflexivity.
Qed.
Lemma strncasecmp_read_p:forall s0 called last k,strncasecmp_pre s0 ->k<strncasecmp_count s0 ->strncasecmp_prefix s0 k ->
  getmem 32 LittleE 1 (strncasecmp_memory s0 called last) (cdecl_arg s0+k)=strncasecmp_p s0 k.
Proof. intros s0 called last k (_ & P & Q) K (NP & NQ & EQ). apply strncasecmp_read;assumption. Qed.
Lemma strncasecmp_read_q:forall s0 called last k,strncasecmp_pre s0 ->k<strncasecmp_count s0 ->strncasecmp_prefix s0 k ->
  getmem 32 LittleE 1 (strncasecmp_memory s0 called last) (binary_arg2 s0+k)=strncasecmp_q s0 k.
Proof. intros s0 called last k (_ & P & Q) K (NP & NQ & EQ). apply strncasecmp_read;assumption. Qed.
Lemma strncasecmp_got_load:forall s0 called last,
  getmem 32 LittleE 4 (strncasecmp_memory s0 called last) (msub 32 (s0 R_ESP) 32)=strncasecmp_got.
Proof.
  intros s0 called [[arg ra]|];unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;destruct called;
    unfold strncasecmp_base;repeat (rewrite deep_saved_word_frame by lia);rewrite getmem_setmem by lia;reflexivity.
Qed.
Lemma strncasecmp_count_load:forall s0 last,
  getmem 32 LittleE 4 (strncasecmp_memory s0 true last) (msub 32 (s0 R_ESP) 36)=strncasecmp_count s0-1.
Proof.
  intros s0 [[arg ra]|];unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;
    repeat (rewrite deep_saved_word_frame by lia);rewrite getmem_setmem by lia;apply N.mod_small;
    pose proof (strncasecmp_count_bound s0);lia.
Qed.
Lemma strncasecmp_callee_arg:forall s0 sc called arg ra,
  strncasecmp_frame s0 (strncasecmp_memory s0 called (Some (arg,ra))) 64 sc ->arg<256 ->cdecl_arg sc=arg.
Proof.
  intros s0 sc called arg ra (MEM & SP & RD & WR) ARG. unfold cdecl_arg. rewrite MEM,SP. psimpl.
  unfold strncasecmp_memory,strncasecmp_pair. rewrite deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. apply N.mod_small;lia.
Qed.
Lemma strncasecmp_call_return:forall s0 sc called arg ra x se,
  strncasecmp_frame s0 (strncasecmp_memory s0 called (Some (arg,ra))) 64 sc ->arg<256 ->ra<2^32 ->
  cdecl_returned sc (tolower_spec (cdecl_arg sc)) x se ->
  x=Addr ra /\ strncasecmp_frame s0 (strncasecmp_memory s0 called (Some (arg,ra))) 60 se /\
  se R_EBX=sc R_EBX /\ se R_EBP=sc R_EBP /\ se R_ESI=sc R_ESI /\ se R_EDI=sc R_EDI /\ se R_EAX=tolower_spec arg.
Proof.
  intros s0 sc called arg ra x se F ARG RA RETURN.
  pose proof (strncasecmp_callee_arg s0 sc called arg ra F ARG) as VALUE.
  destruct F as (MEM & SP & RD & WR). unfold cdecl_returned in RETURN. rewrite VALUE,MEM,SP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & BX & SI & DI & BP & READ & WRITE).
  unfold strncasecmp_memory,strncasecmp_pair in PC. rewrite getmem_setmem in PC by lia.
  rewrite N.mod_small in PC by exact RA. split;[exact PC|]. split.
  - unfold strncasecmp_frame. rewrite MEMORY,ESP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj BX (conj BP (conj SI (conj DI AX)))).
Qed.
Lemma strncasecmp_outcome_result:forall s0 called stop value,strncasecmp_outcome s0 called stop value ->strncasecmp_result s0 value.
Proof.
  intros s0 called [k|] value OUT.
  - right. exists k. exact OUT.
  - destruct OUT as (COUNT & CALLED & VALUE). left. exact (conj COUNT VALUE).
Qed.
Lemma strncasecmp_saved_bx:forall s0 called last,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (strncasecmp_memory s0 called last) (msub 32 (s0 R_ESP) 16)=s0 R_EBX.
Proof.
  intros s0 called [[arg ra]|] BOUND;unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;destruct called;
    unfold strncasecmp_base;rewrite !deep_saved_word_frame by lia;exact (save4_load_bx s0 None BOUND).
Qed.
Lemma strncasecmp_saved_si:forall s0 called last,s0 R_ESI<2^32 ->
  getmem 32 LittleE 4 (strncasecmp_memory s0 called last) (msub 32 (s0 R_ESP) 12)=s0 R_ESI.
Proof.
  intros s0 called [[arg ra]|] BOUND;unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;destruct called;
    unfold strncasecmp_base;rewrite !deep_saved_word_frame by lia;exact (save4_load_si s0 None BOUND).
Qed.
Lemma strncasecmp_saved_di:forall s0 called last,s0 R_EDI<2^32 ->
  getmem 32 LittleE 4 (strncasecmp_memory s0 called last) (msub 32 (s0 R_ESP) 8)=s0 R_EDI.
Proof.
  intros s0 called [[arg ra]|] BOUND;unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;destruct called;
    unfold strncasecmp_base;rewrite !deep_saved_word_frame by lia;exact (save4_load_di s0 None BOUND).
Qed.
Lemma strncasecmp_saved_bp:forall s0 called last,s0 R_EBP<2^32 ->
  getmem 32 LittleE 4 (strncasecmp_memory s0 called last) (msub 32 (s0 R_ESP) 4)=s0 R_EBP.
Proof.
  intros s0 called [[arg ra]|] BOUND;unfold strncasecmp_memory,strncasecmp_pair,strncasecmp_countbase;destruct called;
    unfold strncasecmp_base;rewrite !deep_saved_word_frame by lia;exact (save4_load_bp s0 None BOUND).
Qed.

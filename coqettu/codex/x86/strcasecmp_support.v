(* Linked code and shared unary stack interface for strcasecmp. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_stack2 i386_deep_stack i386_unary_call i386_binary_call
  i386_strings i386_casecmp i386_call_pair tolower_proof strcasecmp_i386 pc_thunk_bx_i386 tolower_i386.
From Stdlib Require Import NArith Lia List Bool.
Import X86Notations.
Open Scope N.

Definition strcasecmp_linked : program := updateall2 strcasecmp_i386 (updateall2 pc_thunk_bx_i386 tolower_i386).
Lemma strcasecmp_linked_caller : strcasecmp_i386 ⊆2 strcasecmp_linked.
Proof.
  intros s a insn H. unfold strcasecmp_linked,updateall2,updateall,strcasecmp_i386,pc_thunk_bx_i386,tolower_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma strcasecmp_linked_tolower : tolower_i386 ⊆2 strcasecmp_linked.
Proof. intros s a insn H. unfold strcasecmp_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma strcasecmp_linked_thunk : pc_thunk_bx_i386 ⊆2 strcasecmp_linked.
Proof.
  intros s a insn H. unfold strcasecmp_linked,updateall2,updateall,pc_thunk_bx_i386,tolower_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem strcasecmp_linked_welltyped : welltyped_prog x86typctx strcasecmp_linked.
Proof.
  intros s a. unfold strcasecmp_linked,updateall2,updateall.
  destruct (tolower_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (tolower_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply strcasecmp_i386.welltyped.
Qed.



Definition strcasecmp_got:N:=0xb4f9c.
Definition strcasecmp_base (s0:store):=
  setmem 32 LittleE 4 (save4_registers s0) (msub 32 (s0 R_ESP) 20) 0x75f49.
Definition strcasecmp_memory (s0:store) (last:option (N*N)):memory:=match last with
  | None=>strcasecmp_base s0
  | Some (arg,ra)=>case_call_pair (strcasecmp_base s0) (s0 R_ESP) arg ra end.
Definition strcasecmp_argmem (s0:store) (last:option (N*N)) (arg:N):=
  setmem 32 LittleE 4 (strcasecmp_memory s0 last) (msub 32 (s0 R_ESP) 44) arg.
Definition strcasecmp_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\ s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition strcasecmp_regs (s0:store) (k:N) (s:store):=
  s R_EBX=strcasecmp_got /\ s R_EBP=(cdecl_arg s0+k) mod 2^32 /\ s R_ESI=(binary_arg2 s0+k) mod 2^32.
Definition strcasecmp_p (s0:store) (k:N):=getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Definition strcasecmp_q (s0:store) (k:N):=getmem 32 LittleE 1 (s0 V_MEM32) (binary_arg2 s0+k).
Definition strcasecmp_prefix (s0:store) (k:N):=case_equal_prefix (s0 V_MEM32) (cdecl_arg s0) (binary_arg2 s0) k.
Definition strcasecmp_stop (s0:store) (k:N):=strcasecmp_p s0 k=0 \/strcasecmp_q s0 k=0 \/
  tolower_spec (strcasecmp_p s0 k)<>tolower_spec (strcasecmp_q s0 k).
Definition strcasecmp_nz (s0:store) (k:N):=strcasecmp_p s0 k<>0 /\ strcasecmp_q s0 k<>0.
Definition strcasecmp_diff (s0:store) (k:N):=msub 32 (tolower_spec (strcasecmp_p s0 k)) (tolower_spec (strcasecmp_q s0 k)).
Definition strcasecmp_reference (s0:store) (k:N):=
  s0[V_MEM32:=strcasecmp_memory s0 (Some (strcasecmp_q s0 k,0x75fac))].
Definition strcasecmp_avoids (s0:store) (p:N):=forall k,nonzero_prefix (s0 V_MEM32) p k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 48) 48 (p+k) 1.
Definition strcasecmp_pre (s0:store):=models x86typctx s0 /\
  strcasecmp_avoids s0 (cdecl_arg s0) /\ strcasecmp_avoids s0 (binary_arg2 s0).
Definition strcasecmp_result (s0:store) (value:N):=case_compare_result (s0 V_MEM32) (cdecl_arg s0) (binary_arg2 s0) value.
Lemma strcasecmp_entry_memory:forall s0 last arg ra,
  setmem 32 LittleE 4 (strcasecmp_argmem s0 last arg) (msub 32 (s0 R_ESP) 48) ra=
  strcasecmp_memory s0 (Some (arg,ra)).
Proof.
  intros s0 last arg ra.
  change (case_call_pair (strcasecmp_memory s0 last) (s0 R_ESP) arg ra=strcasecmp_memory s0 (Some (arg,ra))).
  destruct last as [[oldarg oldra]|];cbn [strcasecmp_memory];[apply case_call_pair_shadow|reflexivity].
Qed.
Lemma strcasecmp_outer_stack:forall s0 last off,off<=8 ->
  getmem 32 LittleE 4 (strcasecmp_memory s0 last) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 [[arg ra]|] off OFF;unfold strcasecmp_memory,case_call_pair,strcasecmp_base,save4_registers;
    rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strcasecmp_read:forall s0 last p k,strcasecmp_avoids s0 p ->nonzero_prefix (s0 V_MEM32) p k ->
  getmem 32 LittleE 1 (strcasecmp_memory s0 last) (p+k)=getmem 32 LittleE 1 (s0 V_MEM32) (p+k).
Proof.
  intros s0 [[arg ra]|] p k AVOID PREFIX. all: pose proof (AVOID k PREFIX) as NO.
  all: unfold strcasecmp_memory,case_call_pair,strcasecmp_base,save4_registers.
  all: replace (p+k) with ((p+k)+0) by lia.
  all: rewrite !descending_stack_read with (total:=48) (n:=1) by (try exact NO;lia);reflexivity.
Qed.
Lemma strcasecmp_read_p:forall s0 last k,strcasecmp_pre s0 ->strcasecmp_prefix s0 k ->
  getmem 32 LittleE 1 (strcasecmp_memory s0 last) (cdecl_arg s0+k)=strcasecmp_p s0 k.
Proof. intros s0 last k (_ & P & Q) (NP & NQ & EQ). apply strcasecmp_read;assumption. Qed.
Lemma strcasecmp_read_q:forall s0 last k,strcasecmp_pre s0 ->strcasecmp_prefix s0 k ->
  getmem 32 LittleE 1 (strcasecmp_memory s0 last) (binary_arg2 s0+k)=strcasecmp_q s0 k.
Proof. intros s0 last k (_ & P & Q) (NP & NQ & EQ). apply strcasecmp_read;assumption. Qed.
Lemma strcasecmp_callee_arg:forall s0 sc arg ra,strcasecmp_frame s0 (strcasecmp_memory s0 (Some (arg,ra))) 48 sc ->
  arg<256 ->cdecl_arg sc=arg.
Proof.
  intros s0 sc arg ra (MEM & SP & RD & WR) ARG. unfold cdecl_arg. rewrite MEM,SP. psimpl.
  unfold strcasecmp_memory,case_call_pair. rewrite deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. apply N.mod_small;lia.
Qed.
Lemma strcasecmp_call_return:forall s0 sc arg ra x se,
  strcasecmp_frame s0 (strcasecmp_memory s0 (Some (arg,ra))) 48 sc ->arg<256 ->ra<2^32 ->
  cdecl_returned sc (tolower_spec (cdecl_arg sc)) x se ->
  x=Addr ra /\ strcasecmp_frame s0 (strcasecmp_memory s0 (Some (arg,ra))) 44 se /\
  se R_EBX=sc R_EBX /\ se R_EBP=sc R_EBP /\ se R_ESI=sc R_ESI /\ se R_EDI=sc R_EDI /\
  se R_EAX=tolower_spec arg.
Proof.
  intros s0 sc arg ra x se F ARG RA RETURN.
  pose proof (strcasecmp_callee_arg s0 sc arg ra F ARG) as VALUE.
  destruct F as (MEM & SP & RD & WR). unfold cdecl_returned in RETURN.
  rewrite VALUE,MEM,SP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & BX & SI & DI & BP & READ & WRITE).
  unfold strcasecmp_memory,case_call_pair in PC. rewrite getmem_setmem in PC by lia.
  rewrite N.mod_small in PC by exact RA. split;[exact PC|]. split.
  - unfold strcasecmp_frame. rewrite MEMORY,ESP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj BX (conj BP (conj SI (conj DI AX)))).
Qed.
Lemma strcasecmp_regs_transport:forall s0 k sc se,strcasecmp_regs s0 k sc ->
  se R_EBX=sc R_EBX ->se R_EBP=sc R_EBP ->se R_ESI=sc R_ESI ->strcasecmp_regs s0 k se.
Proof. intros s0 k sc se R BX BP SI. unfold strcasecmp_regs. rewrite BX,BP,SI. exact R. Qed.
Lemma strcasecmp_result_at_stop:forall s0 k,strcasecmp_prefix s0 k ->strcasecmp_stop s0 k ->
  strcasecmp_result s0 (strcasecmp_diff s0 k).
Proof. intros. apply case_compare_stop with (k:=k);[exact H|exact H0|reflexivity]. Qed.
Lemma strcasecmp_saved_bx:forall s0 last,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (strcasecmp_memory s0 last) (msub 32 (s0 R_ESP) 16)=s0 R_EBX.
Proof.
  intros s0 [[arg ra]|] BOUND;unfold strcasecmp_memory,case_call_pair,strcasecmp_base;
    rewrite !deep_saved_word_frame by lia;exact (save4_load_bx s0 None BOUND).
Qed.
Lemma strcasecmp_saved_si:forall s0 last,s0 R_ESI<2^32 ->
  getmem 32 LittleE 4 (strcasecmp_memory s0 last) (msub 32 (s0 R_ESP) 12)=s0 R_ESI.
Proof.
  intros s0 [[arg ra]|] BOUND;unfold strcasecmp_memory,case_call_pair,strcasecmp_base;
    rewrite !deep_saved_word_frame by lia;exact (save4_load_si s0 None BOUND).
Qed.
Lemma strcasecmp_saved_di:forall s0 last,s0 R_EDI<2^32 ->
  getmem 32 LittleE 4 (strcasecmp_memory s0 last) (msub 32 (s0 R_ESP) 8)=s0 R_EDI.
Proof.
  intros s0 [[arg ra]|] BOUND;unfold strcasecmp_memory,case_call_pair,strcasecmp_base;
    rewrite !deep_saved_word_frame by lia;exact (save4_load_di s0 None BOUND).
Qed.
Lemma strcasecmp_saved_bp:forall s0 last,s0 R_EBP<2^32 ->
  getmem 32 LittleE 4 (strcasecmp_memory s0 last) (msub 32 (s0 R_ESP) 4)=s0 R_EBP.
Proof.
  intros s0 [[arg ra]|] BOUND;unfold strcasecmp_memory,case_call_pair,strcasecmp_base;
    rewrite !deep_saved_word_frame by lia;exact (save4_load_bp s0 None BOUND).
Qed.

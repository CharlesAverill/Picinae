(* Linked byte-search caller and exact nested-call stack snapshots for strchr. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_stack4 i386_unary_call
  i386_binary_call i386_strings i386_byte_search strchrnul_support strchrnul_proof
  strchr_i386 strchrnul_i386 pc_thunk_bx_i386 strlen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition strchr_linked : program:=updateall2 strchr_i386 strchrnul_linked.
Lemma strchr_linked_caller:strchr_i386 ⊆2 strchr_linked.
Proof.
  intros s a insn H. unfold strchr_linked,strchrnul_linked,updateall2,updateall,
    strchr_i386,strchrnul_i386,pc_thunk_bx_i386,strlen_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma strchr_linked_callee:strchrnul_linked ⊆2 strchr_linked.
Proof. intros s a insn H. unfold strchr_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem strchr_linked_welltyped:welltyped_prog x86typctx strchr_linked.
Proof.
  intros s a. unfold strchr_linked,updateall2,updateall.
  destruct (strchrnul_linked s a) as [[sz q]|] eqn:C.
  - pose proof (strchrnul_linked_welltyped s a) as WT. rewrite C in WT. exact WT.
  - apply strchr_i386.welltyped.
Qed.
Definition strchr_m1 (s0:store):=setmem 32 LittleE 4 (s0 V_MEM32) (msub 32 (s0 R_ESP) 24) (binary_arg2 s0).
Definition strchr_m2 (s0:store):=setmem 32 LittleE 4 (strchr_m1 s0) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition strchr_m3 (s0:store):=setmem 32 LittleE 4 (strchr_m2 s0) (msub 32 (s0 R_ESP) 32) (0x7606e).
Definition strchr_m4 (s0:store):=setmem 32 LittleE 4 (strchr_m3 s0) (msub 32 (s0 R_ESP) 36) (s0 R_EBP).
Definition strchr_m5 (s0:store):=setmem 32 LittleE 4 (strchr_m4 s0) (msub 32 (s0 R_ESP) 40) (s0 R_EDI).
Definition strchr_m6 (s0:store):=setmem 32 LittleE 4 (strchr_m5 s0) (msub 32 (s0 R_ESP) 44) (s0 R_ESI).
Definition strchr_m7 (s0:store):=setmem 32 LittleE 4 (strchr_m6 s0) (msub 32 (s0 R_ESP) 48) (s0 R_EBX).
Definition strchr_m8 (s0:store):=setmem 32 LittleE 4 (strchr_m7 s0) (msub 32 (s0 R_ESP) 52) (0x31409).
Definition strchr_m9 (s0:store):=setmem 32 LittleE 4 (strchr_m8 s0) (msub 32 (s0 R_ESP) 76) (cdecl_arg s0).
Definition strchr_m10 (s0:store):=setmem 32 LittleE 4 (strchr_m9 s0) (msub 32 (s0 R_ESP) 80) (0x31441).
Definition strchr_memory (s0:store):=if strchrnul_char s0=?0 then strchr_m10 s0 else strchr_m8 s0.
Definition strchr_reference (s0:store):=s0[V_MEM32:=strchr_memory s0].
Definition strchr_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\
  s R_EBX=s0 R_EBX /\ s R_ESI=s0 R_ESI /\ s R_EDI=s0 R_EDI /\ s R_EBP=s0 R_EBP /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition strchr_pre (s0:store):=models x86typctx s0 /\ forall k,
  nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 80) 80 (cdecl_arg s0+k) 4.
Definition strchr_result (s0:store) (value:N):=exists k,strchrnul_prefix s0 k /\
  ((getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)=strchrnul_char s0 /\ value=(cdecl_arg s0+k) mod 2^32) \/
   (getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)=0 /\ strchrnul_char s0<>0 /\ value=0)).
Lemma strchr_m1_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (strchr_m1 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strchr_m1.
  rewrite (N.add_comm off (s0 R_ESP)),deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma strchr_callee_args:forall s0 sc,strchr_frame s0 (strchr_m3 s0) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ strchrnul_char sc=strchrnul_char s0.
Proof.
  intros s0 sc (MEM & SP & BX & SI & DI & BP & RD & WR).
  assert (ARGS:cdecl_arg sc=cdecl_arg s0 /\ binary_arg2 sc=binary_arg2 s0).
  { unfold cdecl_arg at 1. unfold binary_arg2 at 1. rewrite MEM,SP. psimpl.
    unfold strchr_m3,strchr_m2,strchr_m1. split;rewrite !deep_saved_word_frame by lia;
      rewrite getmem_setmem by lia;apply N.mod_small;unfold cdecl_arg,binary_arg2;apply getmem_bound. }
  split;[exact (proj1 ARGS)|].
  pose proof (f_equal (fun x=>x mod 2^(1*8)) (proj2 ARGS)) as BYTE.
  unfold binary_arg2 in BYTE. rewrite !getmem_mod in BYTE. exact BYTE.
Qed.
Lemma strchr_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (strchr_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold strchr_memory. destruct (strchrnul_char s0=?0);
    unfold strchr_m10,strchr_m9,strchr_m8,strchr_m7,strchr_m6,strchr_m5,strchr_m4,strchr_m3,strchr_m2,strchr_m1;
    rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma strchr_outer_char:forall s0,
  getmem 32 LittleE 1 (strchr_memory s0) (8+s0 R_ESP)=strchrnul_char s0.
Proof.
  intro s0. pose proof (strchr_outer_stack s0 8 ltac:(lia)) as WORD.
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. rewrite !getmem_mod in WORD. exact WORD.
Qed.
Lemma strchr_read_word:forall s0 (full:bool) k,strchr_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 4 (if full then strchr_memory s0 else strchr_m3 s0) (cdecl_arg s0+k)=
  getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros s0 full k (_ & AVOID) PREFIX. pose proof (AVOID k PREFIX) as NO.
  assert (CELL:forall depth,4<=depth ->depth<=80 ->
    ~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (cdecl_arg s0+k) 4).
  { intros depth LO HI. eapply descending_stack_subregion;[exact HI|exact LO|exact NO]. }
  destruct full;unfold strchr_memory;destruct (strchrnul_char s0=?0);
    unfold strchr_m10,strchr_m9,strchr_m8,strchr_m7,strchr_m6,strchr_m5,strchr_m4,strchr_m3,strchr_m2,strchr_m1;
    rewrite !getmem_noverlap by (apply noverlap_symmetry;apply CELL;lia);reflexivity.
Qed.
Lemma strchr_read_byte:forall s0 (full:bool) k,strchr_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 1 (if full then strchr_memory s0 else strchr_m3 s0) (cdecl_arg s0+k)=
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros. pose proof (strchr_read_word s0 full k H H0) as WORD.
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. rewrite !getmem_mod in WORD. exact WORD.
Qed.
Lemma strchr_prefix_back:forall s0 k,strchr_pre s0 ->
  nonzero_prefix (strchr_m3 s0) (cdecl_arg s0) k ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k.
Proof.
  intros s0 k PRE PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i))
    (fun i=>getmem 32 LittleE 1 (strchr_m3 s0) (cdecl_arg s0+i)) _ k PREFIX).
  intros j P. exact (strchr_read_byte s0 false j PRE P).
Qed.
Lemma strchr_callee_pre:forall s0 sc,strchr_pre s0 ->strchr_frame s0 (strchr_m3 s0) 32 sc ->
  models x86typctx sc ->strchrnul_pre sc.
Proof.
  intros s0 sc PRE F MDL. pose proof (strchr_callee_args s0 sc F) as [ARG CHAR].
  destruct F as (MEM & SP & BX & SI & DI & BP & RD & WR).
  split;[exact MDL|]. intros k PREFIX. rewrite ARG,MEM in PREFIX.
  pose proof (strchr_prefix_back s0 k PRE PREFIX) as ORIGINAL.
  pose proof (proj2 PRE k ORIGINAL) as NO. rewrite SP,ARG. psimpl.
  eapply descending_stack_subregion;[| |exact NO];lia.
Qed.
Lemma strchr_callee_memory:forall s0 sc,strchr_frame s0 (strchr_m3 s0) 32 sc ->
  strchrnul_memory sc=strchr_memory s0.
Proof.
  intros s0 sc F. pose proof (strchr_callee_args s0 sc F) as [ARG CHAR].
  destruct F as (MEM & SP & BX & SI & DI & BP & RD & WR).
  unfold strchrnul_memory,strchrnul_snapshot,strchr_memory. rewrite CHAR.
  destruct (strchrnul_char s0=?0);unfold strchrnul_m4,strchrnul_m3,strchrnul_m2,strchrnul_m1,save4_registers;
    rewrite ?ARG,MEM,SP,BX,SI,DI,BP;psimpl;reflexivity.
Qed.
Lemma strchr_result_back:forall s0 sc value,strchr_pre s0 ->strchr_frame s0 (strchr_m3 s0) 32 sc ->
  strchrnul_result sc value ->strchrnul_result s0 value.
Proof.
  intros s0 sc value PRE F RESULT. pose proof (strchr_callee_args s0 sc F) as [ARG CHAR].
  destruct F as (MEM & SP & BX & SI & DI & BP & RD & WR).
  unfold strchrnul_result,strchrnul_prefix in *. rewrite ARG,CHAR,MEM in RESULT.
  destruct RESULT as [k [[PREFIX MATCH] [STOP VALUE]]].
  pose proof (strchr_prefix_back s0 k PRE PREFIX) as ORIGINAL.
  exists k. split.
  - split;[exact ORIGINAL|]. intros i I.
    pose proof (strchr_read_byte s0 false i PRE ltac:(intros j J;apply ORIGINAL;lia)) as READ.
    change (getmem 32 LittleE 1 (strchr_m3 s0) (cdecl_arg s0+i)=
      getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i)) in READ.
    rewrite <- READ. exact (MATCH i I).
  - split;[|exact VALUE]. pose proof (strchr_read_byte s0 false k PRE ORIGINAL) as READ.
    change (getmem 32 LittleE 1 (strchr_m3 s0) (cdecl_arg s0+k)=
      getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k)) in READ.
    rewrite READ in STOP. exact STOP.
Qed.
Lemma strchr_call_return:forall s0 sc value x se,strchr_frame s0 (strchr_m3 s0) 32 sc ->
  cdecl_returned (strchrnul_reference sc) value x se ->
  x=Addr 0x7606e /\ strchr_frame s0 (strchr_memory s0) 28 se /\ se R_EAX=value.
Proof.
  intros s0 sc value x se F RETURN.
  pose proof (strchr_callee_memory s0 sc F) as MM.
  pose proof (strchrnul_snapshot_stack sc (strchrnul_char sc=?0) 0 ltac:(lia)) as RA.
  rewrite N.add_0_l in RA. change (getmem 32 LittleE 4 (strchrnul_memory sc) (sc R_ESP)=
    getmem 32 LittleE 4 (sc V_MEM32) (sc R_ESP)) in RA.
  destruct F as (MEM & SP & BX & SI & DI & BP & RD & WR).
  unfold cdecl_returned,strchrnul_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold strchr_m3 in PC. rewrite getmem_setmem in PC by lia. cbn in PC.
  split;[exact PC|]. split;[|exact AX]. unfold strchr_frame.
  rewrite MEMORY,ESP,EBX,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
Qed.

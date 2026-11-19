(* Nested PIC-call stack for wctype_l -> wctype -> strcmp. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call i386_strings i386_named_string
  wctype_l_i386 wctype_support wctype_proof wctype_i386 pc_thunk_bx_i386 strcmp_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wctype_l_linked:program:=updateall2 wctype_l_i386 wctype_linked.
Lemma wctype_l_linked_caller:wctype_l_i386 ⊆2 wctype_l_linked.
Proof.
  intros s a insn H. unfold wctype_l_linked,wctype_linked,updateall2,updateall,
    wctype_l_i386,wctype_i386,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a];[discriminate|].
  repeat (destruct a as [a|a|];cbn in *;try reflexivity;try congruence).
Qed.
Lemma wctype_l_linked_wctype:wctype_linked ⊆2 wctype_l_linked.
Proof. intros s a insn H. unfold wctype_l_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Theorem wctype_l_linked_welltyped:welltyped_prog x86typctx wctype_l_linked.
Proof.
  intros s a. unfold wctype_l_linked,updateall2,updateall.
  destruct (wctype_linked s a) as [[sz q]|] eqn:M.
  - pose proof (wctype_linked_welltyped s a) as WT. rewrite M in WT. exact WT.
  - apply wctype_l_i386.welltyped.
Qed.

Definition wctype_l_got:N:=0xb4f9c.
Definition wctype_l_m1:=unary_m1.
Definition wctype_l_m2 (s0:store):=unary_m2 s0 0x4f33e.
Definition wctype_l_m3 (s0:store):=unary_m3 s0 0x4f33e.
Definition wctype_l_m4 (s0:store):=unary_memory s0 0x4f33e 0x4f350.
Definition wctype_l_frame:=unary_frame.
Definition wctype_l_child (s0:store):=
  s0[V_MEM32:=wctype_l_m4 s0][R_ESP:=msub 32 (s0 R_ESP) 32][R_EBX:=wctype_l_got].
Definition wctype_l_memory (s0:store) (calls:list N):=wctype_memory (wctype_l_child s0) calls.
Definition wctype_l_reference (s0:store) (calls:list N):=s0[V_MEM32:=wctype_l_memory s0 calls].
Definition wctype_l_pre (s0:store):=models x86typctx s0 /\
  (forall k,nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
    ~overlap 32 (msub 32 (s0 R_ESP) 88) 88 (cdecl_arg s0+k) 1) /\
  ~overlap 32 (msub 32 (s0 R_ESP) 88) 88 wctype_table 73 /\
  (forall i,i<73 ->getmem 32 LittleE 1 (s0 V_MEM32) (wctype_table+i)=wctype_static i).
Lemma wctype_l_child_frame:forall s0,wctype_l_frame s0 (wctype_l_m4 s0) 32 (wctype_l_child s0).
Proof. intros. unfold wctype_l_frame,unary_frame,wctype_l_child. psimpl. repeat split;reflexivity. Qed.
Lemma wctype_l_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wctype_l_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma wctype_l_entry_read_region:forall s0 p n off,
  ~overlap 32 (msub 32 (s0 R_ESP) 88) 88 p n ->off<n ->
  getmem 32 LittleE 1 (wctype_l_m4 s0) (p+off)=getmem 32 LittleE 1 (s0 V_MEM32) (p+off).
Proof.
  intros s0 p n off NO OFF. unfold wctype_l_m4,unary_memory,unary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite !descending_stack_read with (total:=88) (n:=n) by (try exact NO;lia). reflexivity.
Qed.
Lemma wctype_l_entry_read:forall s0 k,wctype_l_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 1 (wctype_l_m4 s0) (cdecl_arg s0+k)=getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros s0 k (_ & A & B & DATA) PREFIX.
  pose proof (wctype_l_entry_read_region s0 (cdecl_arg s0+k) 1 0 (A k PREFIX) ltac:(lia)) as READ.
  rewrite N.add_0_r in READ. exact READ.
Qed.
Lemma wctype_l_prefix_back:forall s0 k,wctype_l_pre s0 ->
  nonzero_prefix (wctype_l_m4 s0) (cdecl_arg s0) k ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k.
Proof.
  intros s0 k PRE PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i))
    (fun i=>getmem 32 LittleE 1 (wctype_l_m4 s0) (cdecl_arg s0+i)) _ k PREFIX).
  intros j P. apply wctype_l_entry_read;assumption.
Qed.
Lemma wctype_l_match:forall s0 sc j,wctype_l_pre s0 ->j<12 ->
  wctype_l_frame s0 (wctype_l_m4 s0) 32 sc ->wctype_matchb sc j=wctype_matchb s0 j.
Proof.
  intros s0 sc j PRE J F.
  pose proof (unary_callee_arg s0 0x4f33e 0x4f350 sc F) as ARG.
  assert (IFF:wctype_matchb sc j=true <->wctype_matchb s0 j=true).
  { unfold wctype_matchb. rewrite !fixed_name_matchb_spec,ARG,(proj1 F). split;intro H.
    - assert (NZ:nonzero_prefix (wctype_l_m4 s0) (cdecl_arg s0) (wctype_length j)).
      { intros i I. rewrite H by lia. exact (proj2 (wctype_name_shape j J) i I). }
      pose proof (wctype_l_prefix_back s0 _ PRE NZ) as ORIGINAL.
      intros i I. rewrite <- (wctype_l_entry_read s0 i PRE ltac:(intros h Hh;apply ORIGINAL;lia)). exact (H i I).
    - assert (NZ:nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) (wctype_length j)).
      { intros i I. rewrite H by lia. exact (proj2 (wctype_name_shape j J) i I). }
      intros i I. rewrite (wctype_l_entry_read s0 i PRE ltac:(intros h Hh;apply NZ;lia)). exact (H i I). }
  destruct (wctype_matchb sc j),(wctype_matchb s0 j);intuition congruence.
Qed.
Lemma wctype_l_result_back:forall s0 sc value,wctype_l_pre s0 ->
  wctype_l_frame s0 (wctype_l_m4 s0) 32 sc ->wctype_result sc value ->wctype_result s0 value.
Proof.
  intros s0 sc value PRE F RESULT. unfold wctype_result in *. destruct RESULT as [(j & J & V & MATCH & BEFORE)|[V BEFORE]].
  - left. exists j. split;[exact J|]. split;[exact V|]. split.
    + rewrite <- (wctype_l_match s0 sc j PRE J F). exact MATCH.
    + intros i I. rewrite <- (wctype_l_match s0 sc i PRE ltac:(lia) F). exact (BEFORE i I).
  - right. split;[exact V|]. intros i I. rewrite <- (wctype_l_match s0 sc i PRE I F). exact (BEFORE i I).
Qed.
Lemma wctype_l_callee_pre:forall s0 sc,wctype_l_pre s0 ->models x86typctx sc ->
  wctype_l_frame s0 (wctype_l_m4 s0) 32 sc ->wctype_pre sc.
Proof.
  intros s0 sc PRE MDL F. pose proof (unary_callee_arg s0 0x4f33e 0x4f350 sc F) as ARG.
  split;[exact MDL|]. rewrite ARG. split.
  - intros k PREFIX. rewrite (proj1 F) in PREFIX.
    pose proof (wctype_l_prefix_back s0 k PRE PREFIX) as ORIGINAL.
    pose proof (proj1 (proj2 PRE) k ORIGINAL) as NO. rewrite (proj1 (proj2 F)). psimpl.
    eapply descending_stack_subregion;[| |exact NO];lia.
  - destruct PRE as (_ & A & B & DATA). split.
    + rewrite (proj1 (proj2 F)). psimpl. eapply descending_stack_subregion;[| |exact B];lia.
    + intros i I. rewrite (proj1 F),(wctype_l_entry_read_region s0 wctype_table 73 i B I). exact (DATA i I).
Qed.
Lemma wctype_memory_entry_ext:forall s1 s2,
  s1 V_MEM32=s2 V_MEM32 ->s1 R_ESP=s2 R_ESP ->s1 R_EBX=s2 R_EBX ->s1 R_ESI=s2 R_ESI ->
  s1 R_EDI=s2 R_EDI ->s1 R_EBP=s2 R_EBP ->cdecl_arg s1=cdecl_arg s2 ->
  forall calls,wctype_memory s1 calls=wctype_memory s2 calls.
Proof.
  intros s1 s2 MEM SP BX SI DI BP ARG calls. induction calls as [|j older IH].
  - cbn [wctype_memory]. unfold wctype_base,save4_registers. rewrite MEM,SP,BX,SI,DI,BP. reflexivity.
  - cbn [wctype_memory]. unfold wctype_after_on,wctype_entry_on,wctype_args_on. rewrite IH,SP,ARG. reflexivity.
Qed.
Lemma wctype_l_callee_memory:forall s0 sc calls,wctype_l_frame s0 (wctype_l_m4 s0) 32 sc ->
  sc R_EBX=wctype_l_got ->wctype_memory sc calls=wctype_l_memory s0 calls.
Proof.
  intros s0 sc calls F BX.
  pose proof (unary_callee_arg s0 0x4f33e 0x4f350 sc F) as ARG.
  pose proof (unary_callee_arg s0 0x4f33e 0x4f350 (wctype_l_child s0) (wctype_l_child_frame s0)) as CARG.
  unfold wctype_l_memory. apply wctype_memory_entry_ext;try (rewrite ARG,CARG;reflexivity).
  all: destruct F as (MEM & SP & SI & DI & BP & RD & WR);unfold wctype_l_child;psimpl;assumption.
Qed.
Lemma wctype_l_after_stack:forall sc calls off,off<=64 ->
  getmem 32 LittleE 4 (wctype_memory sc calls) (off+sc R_ESP)=getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof.
  intros sc calls. induction calls as [|j older IH];intros off OFF.
  - cbn [wctype_memory]. unfold wctype_base,save4_registers.
    rewrite (N.add_comm off (sc R_ESP)),!deep_stack_word_frame by lia;reflexivity.
  - cbn [wctype_memory]. unfold wctype_after_on,wctype_entry_on,wctype_args_on.
    rewrite (N.add_comm off (sc R_ESP)),!deep_stack_word_frame by lia.
    rewrite (N.add_comm (sc R_ESP) off). exact (IH off OFF).
Qed.
Lemma wctype_l_saved_bx:forall s0 calls,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (wctype_l_memory s0 calls) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 calls BOUND. unfold wctype_l_memory.
  pose proof (wctype_l_after_stack (wctype_l_child s0) calls 28 ltac:(lia)) as READ.
  unfold wctype_l_child in READ. psimpl in READ. unfold wctype_l_child. rewrite READ.
  apply unary_saved_bx;exact BOUND.
Qed.
Lemma wctype_l_outer_stack:forall s0 calls off,off<=8 ->
  getmem 32 LittleE 4 (wctype_l_memory s0 calls) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 calls off OFF. unfold wctype_l_memory.
  pose proof (wctype_l_after_stack (wctype_l_child s0) calls (32+off) ltac:(lia)) as READ.
  unfold wctype_l_child in READ. psimpl in READ. unfold wctype_l_child.
  rewrite READ. apply unary_outer_stack;exact OFF.
Qed.
Lemma wctype_l_call_return:forall s0 sc calls value x se,
  wctype_l_frame s0 (wctype_l_m4 s0) 32 sc ->sc R_EBX=wctype_l_got ->
  cdecl_returned (wctype_reference sc calls) value x se ->
  x=Addr 0x4f350 /\ wctype_l_frame s0 (wctype_l_memory s0 calls) 28 se /\
  se R_EBX=wctype_l_got /\ se R_EAX=value.
Proof.
  intros s0 sc calls value x se F BX RETURN.
  pose proof (wctype_l_callee_memory s0 sc calls F BX) as MM.
  pose proof (wctype_outer_stack sc calls 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  destruct F as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,wctype_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold wctype_l_m4 in PC. rewrite unary_call_address in PC. split;[exact PC|]. split.
  - unfold wctype_l_frame,unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.

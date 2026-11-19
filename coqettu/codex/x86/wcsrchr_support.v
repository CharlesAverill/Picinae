(* Linked code and shared unary stack interface for wcsrchr. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_stack4 i386_unary_call
  i386_binary_call i386_strings i386_wstrlen i386_wsearch i386_backward wcslen_proof wcsrchr_i386 pc_thunk_bx_i386 wcslen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcsrchr_linked : program := updateall2 wcsrchr_i386 (updateall2 pc_thunk_bx_i386 wcslen_i386).
Lemma wcsrchr_linked_caller : wcsrchr_i386 ⊆2 wcsrchr_linked.
Proof.
  intros s a insn H. unfold wcsrchr_linked,updateall2,updateall,wcsrchr_i386,pc_thunk_bx_i386,wcslen_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma wcsrchr_linked_wcslen : wcslen_i386 ⊆2 wcsrchr_linked.
Proof. intros s a insn H. unfold wcsrchr_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma wcsrchr_linked_thunk : pc_thunk_bx_i386 ⊆2 wcsrchr_linked.
Proof.
  intros s a insn H. unfold wcsrchr_linked,updateall2,updateall,pc_thunk_bx_i386,wcslen_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem wcsrchr_linked_welltyped : welltyped_prog x86typctx wcsrchr_linked.
Proof.
  intros s a. unfold wcsrchr_linked,updateall2,updateall.
  destruct (wcslen_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (wcslen_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply wcsrchr_i386.welltyped.
Qed.



Definition wcsrchr_got:N:=0xb4f9c.
Definition wcsrchr_needle:=binary_arg2.
Definition wcsrchr_m1 (s0:store):=
  setmem 32 LittleE 4 (s0 V_MEM32) (msub 32 (s0 R_ESP) 4) (s0 R_EDI).
Definition wcsrchr_m2 (s0:store):=
  setmem 32 LittleE 4 (wcsrchr_m1 s0) (msub 32 (s0 R_ESP) 8) (s0 R_ESI).
Definition wcsrchr_m3 (s0:store):=
  setmem 32 LittleE 4 (wcsrchr_m2 s0) (msub 32 (s0 R_ESP) 12) (s0 R_EBX).
Definition wcsrchr_m4 (s0:store):=
  setmem 32 LittleE 4 (wcsrchr_m3 s0) (msub 32 (s0 R_ESP) 16) 0x47c3c.
Definition wcsrchr_m5 (s0:store):=
  setmem 32 LittleE 4 (wcsrchr_m4 s0) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition wcsrchr_memory (s0:store):=
  setmem 32 LittleE 4 (wcsrchr_m5 s0) (msub 32 (s0 R_ESP) 32) 0x47c4f.
Definition wcsrchr_reference (s0:store):=s0[V_MEM32:=wcsrchr_memory s0].
Definition wcsrchr_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\
  s R_EBP=s0 R_EBP /\ s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Definition wcsrchr_pre (s0:store):=models x86typctx s0 /\ 4<=cdecl_arg s0 /\
  forall k,wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k ->
  cdecl_arg s0+4*k+4<=2^32 /\
  ~overlap 32 (msub 32 (s0 R_ESP) 32) 32 (cdecl_arg s0+4*k) 4.
Definition wcsrchr_word (s0:store) (i:N):=getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*i).
Definition wcsrchr_suffix (s0:store) (i n:N):=
  forall j,i<=j ->j<=n ->wcsrchr_word s0 j<>wcsrchr_needle s0.
Definition wcsrchr_length (s0:store) (result:N):=exists n,
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ result=wide_length32 n.
Definition wcsrchr_scan (s0:store) (address:N):=exists n i,
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) n /\ i<=n+1 /\
  address=backward_address (cdecl_arg s0) 4 i /\ wcsrchr_suffix s0 i n.
Definition wcsrchr_result (s0:store) (result:N):=exists n,
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) n /\
  ((result=0 /\ wcsrchr_suffix s0 0 n) \/
   exists j,j<=n /\ wcsrchr_word s0 j=wcsrchr_needle s0 /\
     result=cdecl_arg s0+4*j /\ wcsrchr_suffix s0 (j+1) n).
Lemma wcsrchr_m3_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcsrchr_m3 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold wcsrchr_m3,wcsrchr_m2,wcsrchr_m1.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma wcsrchr_m4_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcsrchr_m4 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold wcsrchr_m4. rewrite (N.add_comm off (s0 R_ESP)),deep_stack_word_frame by lia.
  rewrite (N.add_comm (s0 R_ESP) off). apply wcsrchr_m3_stack;exact OFF.
Qed.
Lemma wcsrchr_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcsrchr_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold wcsrchr_memory,wcsrchr_m5,wcsrchr_m4,wcsrchr_m3,wcsrchr_m2,wcsrchr_m1.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.
Lemma wcsrchr_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (wcsrchr_memory s0) (msub 32 (s0 R_ESP) 12)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold wcsrchr_memory,wcsrchr_m5,wcsrchr_m4,wcsrchr_m3.
  rewrite !deep_saved_word_frame by lia. rewrite getmem_setmem by lia. apply N.mod_small;exact BOUND.
Qed.
Lemma wcsrchr_saved_si:forall s0,s0 R_ESI<2^32 ->
  getmem 32 LittleE 4 (wcsrchr_memory s0) (msub 32 (s0 R_ESP) 8)=s0 R_ESI.
Proof.
  intros s0 BOUND. unfold wcsrchr_memory,wcsrchr_m5,wcsrchr_m4,wcsrchr_m3,wcsrchr_m2.
  rewrite !deep_saved_word_frame by lia. rewrite getmem_setmem by lia. apply N.mod_small;exact BOUND.
Qed.
Lemma wcsrchr_saved_di:forall s0,s0 R_EDI<2^32 ->
  getmem 32 LittleE 4 (wcsrchr_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EDI.
Proof.
  intros s0 BOUND. unfold wcsrchr_memory,wcsrchr_m5,wcsrchr_m4,wcsrchr_m3,wcsrchr_m2,wcsrchr_m1.
  rewrite !deep_saved_word_frame by lia. rewrite getmem_setmem by lia. apply N.mod_small;exact BOUND.
Qed.
Lemma wcsrchr_callee_arg:forall s0 sc,
  wcsrchr_frame s0 (wcsrchr_memory s0) 32 sc ->cdecl_arg sc=cdecl_arg s0.
Proof.
  intros s0 sc (MEM & SP & BP & RD & WR). unfold cdecl_arg at 1. rewrite MEM,SP. psimpl.
  unfold wcsrchr_memory,wcsrchr_m5. rewrite deep_saved_word_frame by lia.
  rewrite getmem_setmem by lia. apply N.mod_small. unfold cdecl_arg;apply getmem_bound.
Qed.
Lemma wcsrchr_read_prefix:forall s0 k,wcsrchr_pre s0 ->
  wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k ->
  getmem 32 LittleE 4 (wcsrchr_memory s0) (cdecl_arg s0+4*k)=wcsrchr_word s0 k.
Proof.
  intros s0 k (_ & BASE & SAFE) PREFIX. destruct (SAFE k PREFIX) as [BOUND NO].
  assert (CELL:forall depth,4<=depth ->depth<=32 ->
    ~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (cdecl_arg s0+4*k) 4).
  { intros depth LO HI. eapply descending_stack_subregion;[exact HI|exact LO|exact NO]. }
  unfold wcsrchr_memory,wcsrchr_m5,wcsrchr_m4,wcsrchr_m3,wcsrchr_m2,wcsrchr_m1.
  rewrite !getmem_noverlap by (apply noverlap_symmetry;apply CELL;lia). reflexivity.
Qed.
Lemma wcsrchr_first_bounds:forall s0 n,wcsrchr_pre s0 ->
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) n ->forall j,j<=n ->
  cdecl_arg s0+4*j<2^32.
Proof.
  intros s0 n (_ & BASE & SAFE) (NBOUND & PREFIX & ZERO) j J.
  destruct (SAFE n PREFIX) as [BOUND NO]. set (p:=cdecl_arg s0) in *;clearbody p.
  clear - BOUND J;lia.
Qed.
Lemma wcsrchr_read_first:forall s0 n,wcsrchr_pre s0 ->
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) n ->forall j,j<=n ->
  getmem 32 LittleE 4 (wcsrchr_memory s0) (cdecl_arg s0+4*j)=wcsrchr_word s0 j.
Proof.
  intros s0 n PRE (NBOUND & PREFIX & ZERO) j J. apply wcsrchr_read_prefix;[exact PRE|].
  intros k K. apply PREFIX. clear - K J;lia.
Qed.
Lemma wcsrchr_callee_length:forall s0 sc value,wcsrchr_pre s0 ->
  wcsrchr_frame s0 (wcsrchr_memory s0) 32 sc ->wcslen_result sc value ->wcsrchr_length s0 value.
Proof.
  intros s0 sc value PRE FRAME RESULT. unfold wcslen_result in RESULT.
  rewrite (wcsrchr_callee_arg s0 sc FRAME),(proj1 FRAME) in RESULT.
  destruct RESULT as (n & FIRST & VALUE). destruct FIRST as (NBOUND & PREFIX & ZERO).
  assert (ORIGINAL:wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 n).
  { refine (conditional_prefix_transfer
      (fun i=>getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*i))
      (fun i=>getmem 32 LittleE 4 (wcsrchr_memory s0) (cdecl_arg s0+4*i)) _ n PREFIX).
    intros j P. exact (wcsrchr_read_prefix s0 j PRE P). }
  rewrite (wcsrchr_read_prefix s0 n PRE ORIGINAL) in ZERO.
  exists n. split;[repeat split;assumption|exact VALUE].
Qed.
Lemma wcsrchr_call_return:forall s0 sc value x se,
  wcsrchr_frame s0 (wcsrchr_memory s0) 32 sc ->sc R_ESI=cdecl_arg s0 ->
  sc R_EDI=wcsrchr_needle s0 ->sc R_EBX=wcsrchr_got ->cdecl_returned sc value x se ->
  x=Addr 0x47c4f /\ wcsrchr_frame s0 (wcsrchr_memory s0) 28 se /\
  se R_ESI=cdecl_arg s0 /\ se R_EDI=wcsrchr_needle s0 /\ se R_EBX=wcsrchr_got /\ se R_EAX=value.
Proof.
  intros s0 sc value x se (MEM & SP & BP & RD & WR) SI DI BX RETURN.
  unfold cdecl_returned in RETURN. rewrite MEM,SP,BP,RD,WR,SI,DI,BX in RETURN.
  destruct RETURN as (PC & AX & ESP & MM & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold wcsrchr_memory in PC. rewrite getmem_setmem in PC by lia. cbn in PC.
  split;[exact PC|]. split.
  - unfold wcsrchr_frame. rewrite MM,ESP,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj ESI (conj EDI (conj EBX AX))).
Qed.
Lemma wcsrchr_scan_start:forall s0 value,wcsrchr_pre s0 ->wcsrchr_length s0 value ->
  wcsrchr_scan s0 ((cdecl_arg s0+4*value) mod 2^32).
Proof.
  intros s0 value PRE (n & FIRST & VALUE). rewrite VALUE,wide_length32_address.
  rewrite (N.mod_small _ _ (wcsrchr_first_bounds s0 n PRE FIRST n (N.le_refl n))).
  exists n,(n+1). split;[exact FIRST|]. split;[lia|]. split.
  - unfold backward_address. set (p:=cdecl_arg s0);clearbody p;lia.
  - intros j J HI. clear - J HI;lia.
Qed.

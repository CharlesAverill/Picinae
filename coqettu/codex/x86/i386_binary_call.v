(* Two-argument PIC calls to comparison callees saving ESI and EBX. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack2 i386_deep_stack i386_stack4 i386_unary_call
  i386_strings i386_wstringcmp.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition binary_arg2 (s0:store):=getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition binary_m3 (s0:store) (tr:N):=
  setmem 32 LittleE 4 (unary_m2 s0 tr) (msub 32 (s0 R_ESP) 24) (binary_arg2 s0).
Definition binary_m4 (s0:store) (tr:N):=
  setmem 32 LittleE 4 (binary_m3 s0 tr) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition binary_entry_memory (s0:store) (tr cr:N):=
  setmem 32 LittleE 4 (binary_m4 s0 tr) (msub 32 (s0 R_ESP) 32) cr.
Definition binary_memory (s0:store) (tr cr got:N):=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (binary_entry_memory s0 tr cr) (msub 32 (s0 R_ESP) 36) (s0 R_ESI))
    (msub 32 (s0 R_ESP) 40) got.
Definition binary_reference (s0:store) (tr cr got:N):=s0[V_MEM32:=binary_memory s0 tr cr got].

Lemma binary_callee_args:forall s0 tr cr sc,
  unary_frame s0 (binary_entry_memory s0 tr cr) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ binary_arg2 sc=binary_arg2 s0.
Proof.
  intros s0 tr cr sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. unfold binary_arg2 at 1. rewrite MEM,SP. psimpl.
  unfold binary_entry_memory,binary_m4,binary_m3.
  split;rewrite !deep_saved_word_frame by lia.
  all: rewrite getmem_setmem by lia;apply N.mod_small.
  - unfold cdecl_arg;apply getmem_bound.
  - unfold binary_arg2;apply getmem_bound.
Qed.
Lemma binary_callee_memory:forall s0 tr cr got sc,
  unary_frame s0 (binary_entry_memory s0 tr cr) 32 sc ->sc R_EBX=got ->
  save_si_bx_memory sc=binary_memory s0 tr cr got.
Proof.
  intros s0 tr cr got sc (MEM & SP & SI & DI & BP & RD & WR) BX.
  unfold save_si_bx_memory. rewrite MEM,SP,SI,BX. psimpl. reflexivity.
Qed.
Lemma binary_call_address:forall s0 tr cr,
  getmem 32 LittleE 4 (binary_entry_memory s0 tr cr) (msub 32 (s0 R_ESP) 32)=cr mod 2^32.
Proof. intros. unfold binary_entry_memory. rewrite getmem_setmem by lia. reflexivity. Qed.
Lemma binary_call_return:forall s0 tr cr got sc value x se,
  unary_frame s0 (binary_entry_memory s0 tr cr) 32 sc ->sc R_EBX=got ->
  cdecl_returned (save_si_bx_reference sc) value x se ->
  x=Addr (cr mod 2^32) /\ unary_frame s0 (binary_memory s0 tr cr got) 28 se /\
  se R_EBX=got /\ se R_EAX=value.
Proof.
  intros s0 tr cr got sc value x se FRAME BX RETURN.
  pose proof (binary_callee_memory s0 tr cr got sc FRAME BX) as MM.
  destruct FRAME as (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_returned,save_si_bx_reference in RETURN. psimpl in RETURN.
  pose proof (save_si_bx_stack_word sc 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  rewrite RA,MM,MEM,SP,BX,SI,DI,BP,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  rewrite binary_call_address in PC. split;[exact PC|]. split.
  - unfold unary_frame. rewrite MEMORY,ESP,ESI,EDI,EBP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj EBX AX).
Qed.
Lemma binary_saved_bx:forall s0 tr cr got,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (binary_memory s0 tr cr got) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 tr cr got BOUND.
  unfold binary_memory,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Lemma binary_outer_stack:forall s0 tr cr got off,off<=12 ->
  getmem 32 LittleE 4 (binary_memory s0 tr cr got) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 tr cr got off OFF.
  unfold binary_memory,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
Qed.

Definition call_nonzero_prefix (width:N) (m:memory) (p k:N):=
  forall i,i<k ->getmem 32 LittleE width m (p+width*i)<>0.
Definition binary_string_avoids (s0:store) (width p:N):=
  forall k,call_nonzero_prefix width (s0 V_MEM32) p k ->
    ~overlap 32 (msub 32 (s0 R_ESP) 40) 40 (p+width*k) width.
Lemma call_prefix_byte:forall m p k,
  call_nonzero_prefix 1 m p k <-> nonzero_prefix m p k.
Proof. intros. unfold call_nonzero_prefix,nonzero_prefix. setoid_rewrite N.mul_1_l. reflexivity. Qed.
Lemma call_prefix_wide:forall m p k,
  call_nonzero_prefix 4 m p k <-> wide_nonzero_prefix m p k.
Proof. reflexivity. Qed.
Lemma binary_entry_read:forall s0 tr cr width p k,
  binary_string_avoids s0 width p ->call_nonzero_prefix width (s0 V_MEM32) p k ->
  getmem 32 LittleE width (binary_entry_memory s0 tr cr) (p+width*k)=
  getmem 32 LittleE width (s0 V_MEM32) (p+width*k).
Proof.
  intros s0 tr cr width p k AVOID PREFIX.
  pose proof (AVOID k PREFIX) as NO.
  assert (CELL:forall depth,4<=depth ->depth<=40 ->
    ~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (p+width*k) width).
  { intros depth LO HI. eapply descending_stack_subregion;[exact HI|exact LO|exact NO]. }
  unfold binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite !getmem_noverlap by (apply noverlap_symmetry;apply CELL;lia). reflexivity.
Qed.
Lemma conditional_prefix_transfer:forall (r1 r2:N->N),
  (forall k,(forall i,i<k ->r1 i<>0) ->r2 k=r1 k) ->
  forall k,(forall i,i<k ->r2 i<>0) ->forall i,i<k ->r1 i<>0.
Proof.
  intros r1 r2 READ k. induction k using N.peano_ind.
  - intros P i I. clear - I. lia.
  - intros P i I. assert (OLD:forall j,j<k ->r1 j<>0).
    { apply IHk. intros j J. apply P. clear - J. lia. }
    destruct (N.lt_ge_cases i k) as [LT|GE];[exact (OLD i LT)|].
    replace i with k by (clear - I GE;lia).
    rewrite <- (READ k OLD). apply P. lia.
Qed.
Lemma binary_prefix_back:forall s0 tr cr width p k,
  binary_string_avoids s0 width p ->
  call_nonzero_prefix width (binary_entry_memory s0 tr cr) p k ->
  call_nonzero_prefix width (s0 V_MEM32) p k.
Proof.
  intros s0 tr cr width p k AVOID PREFIX. unfold call_nonzero_prefix in *.
  eapply conditional_prefix_transfer;[|exact PREFIX].
  intros j P. apply binary_entry_read;assumption.
Qed.
Lemma binary_read_through_prefix:forall s0 tr cr width p k,
  binary_string_avoids s0 width p ->
  call_nonzero_prefix width (binary_entry_memory s0 tr cr) p k ->forall i,i<=k ->
  getmem 32 LittleE width (binary_entry_memory s0 tr cr) (p+width*i)=
  getmem 32 LittleE width (s0 V_MEM32) (p+width*i).
Proof.
  intros s0 tr cr width p k AVOID PREFIX i I. apply binary_entry_read;[exact AVOID|].
  pose proof (binary_prefix_back s0 tr cr width p k AVOID PREFIX) as ORIGINAL.
  intros j J. apply ORIGINAL. clear - I J;lia.
Qed.

Lemma binary_entry_avoids_saves:forall s0 tr cr sc width p,
  unary_frame s0 (binary_entry_memory s0 tr cr) 32 sc ->
  binary_string_avoids s0 width p ->forall k,
  call_nonzero_prefix width (sc V_MEM32) p k ->
  ~overlap 32 (msub 32 (sc R_ESP) 4) 4 (p+width*k) width /\
  ~overlap 32 (msub 32 (sc R_ESP) 8) 4 (p+width*k) width.
Proof.
  intros s0 tr cr sc width p (MEM & SP & SI & DI & BP & RD & WR) AVOID k PREFIX.
  rewrite MEM in PREFIX.
  pose proof (binary_prefix_back s0 tr cr width p k AVOID PREFIX) as ORIGINAL.
  pose proof (AVOID k ORIGINAL) as NO. rewrite SP. psimpl. split;
    eapply descending_stack_subregion;[| |exact NO| | |exact NO];lia.
Qed.
Lemma binary_byte_prefix_back:forall s0 tr cr p k,
  binary_string_avoids s0 1 p ->
  nonzero_prefix (binary_entry_memory s0 tr cr) p k ->nonzero_prefix (s0 V_MEM32) p k.
Proof.
  intros s0 tr cr p k AVOID PREFIX. apply call_prefix_byte.
  apply (binary_prefix_back s0 tr cr 1 p k AVOID). apply call_prefix_byte;exact PREFIX.
Qed.
Lemma binary_byte_read:forall s0 tr cr p k,
  binary_string_avoids s0 1 p ->nonzero_prefix (binary_entry_memory s0 tr cr) p k ->
  forall i,i<=k ->getmem 32 LittleE 1 (binary_entry_memory s0 tr cr) (p+i)=
    getmem 32 LittleE 1 (s0 V_MEM32) (p+i).
Proof.
  intros s0 tr cr p k AVOID PREFIX i I.
  apply call_prefix_byte in PREFIX.
  pose proof (binary_read_through_prefix s0 tr cr 1 p k AVOID PREFIX i I) as READ.
  rewrite N.mul_1_l in READ. exact READ.
Qed.

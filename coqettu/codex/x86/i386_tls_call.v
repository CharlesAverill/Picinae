(* Three copied arguments, one fetched through GS, in a nested PIC call. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_deep_stack i386_unary_call i386_binary_call.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.
Definition tls_root (s0:store) (tr:N):=getmem 32 LittleE 4 (unary_m2 s0 tr) (s0 R_GS_BASE).
Definition tls_locale (s0:store) (tr:N):=getmem 32 LittleE 4 (unary_m2 s0 tr) (96+tls_root s0 tr).
Definition tls_m3 (s0:store) (tr:N):=setmem 32 LittleE 4 (unary_m2 s0 tr) (msub 32 (s0 R_ESP) 20) (tls_locale s0 tr).
Definition tls_m4 (s0:store) (tr:N):=setmem 32 LittleE 4 (tls_m3 s0 tr) (msub 32 (s0 R_ESP) 24) (binary_arg2 s0).
Definition tls_m5 (s0:store) (tr:N):=setmem 32 LittleE 4 (tls_m4 s0 tr) (msub 32 (s0 R_ESP) 28) (cdecl_arg s0).
Definition tls_entry (s0:store) (tr cr:N):=setmem 32 LittleE 4 (tls_m5 s0 tr) (msub 32 (s0 R_ESP) 32) cr.
Lemma tls_callee_args:forall s0 tr cr sc,unary_frame s0 (tls_entry s0 tr cr) 32 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ binary_arg2 sc=binary_arg2 s0.
Proof.
  intros s0 tr cr sc (MEM & SP & SI & DI & BP & RD & WR).
  unfold cdecl_arg at 1. unfold binary_arg2 at 1. rewrite MEM,SP. psimpl.
  unfold tls_entry,tls_m5,tls_m4,tls_m3.
  split;rewrite !deep_saved_word_frame by lia.
  all: rewrite getmem_setmem by lia;apply N.mod_small;unfold cdecl_arg,binary_arg2;apply getmem_bound.
Qed.
Lemma tls_call_address:forall s0 tr cr,getmem 32 LittleE 4 (tls_entry s0 tr cr) (msub 32 (s0 R_ESP) 32)=cr mod 2^32.
Proof. intros. unfold tls_entry. rewrite getmem_setmem by lia. reflexivity. Qed.
Lemma tls_outer_stack:forall s0 tr cr off,off<=12 ->getmem 32 LittleE 4 (tls_entry s0 tr cr) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 tr cr off OFF. unfold tls_entry,tls_m5,tls_m4,tls_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma tls_saved_bx:forall s0 tr cr,s0 R_EBX<2^32 ->getmem 32 LittleE 4 (tls_entry s0 tr cr) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 tr cr BOUND. unfold tls_entry,tls_m5,tls_m4,tls_m3,unary_m2,unary_m1.
  rewrite !deep_saved_word_frame by lia. apply saved_ebx_load;exact BOUND.
Qed.
Definition tls_string_avoids (s0:store) (width p:N):=forall k,call_nonzero_prefix width (s0 V_MEM32) p k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 72) 72 (p+width*k) width.
Lemma tls_entry_read:forall s0 tr cr width p k,tls_string_avoids s0 width p ->call_nonzero_prefix width (s0 V_MEM32) p k ->
  getmem 32 LittleE width (tls_entry s0 tr cr) (p+width*k)=getmem 32 LittleE width (s0 V_MEM32) (p+width*k).
Proof.
  intros s0 tr cr width p k A P. pose proof (A k P) as NO.
  assert (CELL:forall depth,4<=depth ->depth<=72 ->~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (p+width*k) width).
  { intros depth LO HI. eapply descending_stack_subregion;[exact HI|exact LO|exact NO]. }
  unfold tls_entry,tls_m5,tls_m4,tls_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite !getmem_noverlap by (apply noverlap_symmetry;apply CELL;lia). reflexivity.
Qed.
Lemma tls_prefix_back:forall s0 tr cr width p k,tls_string_avoids s0 width p ->
  call_nonzero_prefix width (tls_entry s0 tr cr) p k ->call_nonzero_prefix width (s0 V_MEM32) p k.
Proof.
  intros s0 tr cr width p k A P. unfold call_nonzero_prefix in *.
  eapply conditional_prefix_transfer;[|exact P]. intros j J. apply tls_entry_read;assumption.
Qed.
Lemma tls_read_through_prefix:forall s0 tr cr width p k,tls_string_avoids s0 width p ->
  call_nonzero_prefix width (tls_entry s0 tr cr) p k ->forall i,i<=k ->
  getmem 32 LittleE width (tls_entry s0 tr cr) (p+width*i)=getmem 32 LittleE width (s0 V_MEM32) (p+width*i).
Proof.
  intros s0 tr cr width p k A P i I. pose proof (tls_prefix_back s0 tr cr width p k A P) as ORIGINAL.
  apply tls_entry_read;[exact A|]. intros j J. apply ORIGINAL;lia.
Qed.
Lemma tls_entry_avoids:forall s0 tr cr sc width p,unary_frame s0 (tls_entry s0 tr cr) 32 sc ->
  tls_string_avoids s0 width p ->binary_string_avoids sc width p.
Proof.
  intros s0 tr cr sc width p F A k P. rewrite (proj1 F) in P.
  pose proof (tls_prefix_back s0 tr cr width p k A P) as ORIGINAL.
  pose proof (A k ORIGINAL) as NO. rewrite (proj1 (proj2 F)). psimpl.
  eapply descending_stack_subregion;[| |exact NO];lia.
Qed.
Lemma binary_memory_entry_ext:forall s1 s2,
  s1 V_MEM32=s2 V_MEM32 ->s1 R_ESP=s2 R_ESP ->s1 R_EBX=s2 R_EBX ->s1 R_ESI=s2 R_ESI ->
  cdecl_arg s1=cdecl_arg s2 ->binary_arg2 s1=binary_arg2 s2 ->forall tr cr got,
  binary_memory s1 tr cr got=binary_memory s2 tr cr got.
Proof.
  intros s1 s2 MEM SP BX SI ARG ARG2 tr cr got.
  unfold binary_memory,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite MEM,SP,BX,SI,ARG,ARG2. reflexivity.
Qed.
Lemma binary_memory_above:forall sc tr cr got off,off<=64 ->getmem 32 LittleE 4 (binary_memory sc tr cr got) (off+sc R_ESP)=
  getmem 32 LittleE 4 (sc V_MEM32) (off+sc R_ESP).
Proof.
  intros sc tr cr got off OFF. unfold binary_memory,binary_entry_memory,binary_m4,binary_m3,unary_m2,unary_m1,save_ebx_memory.
  rewrite (N.add_comm off (sc R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.

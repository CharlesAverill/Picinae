(* Frozen-source string-copy semantics with two saved registers and a protected stack. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack2 i386_deep_stack i386_stack4 i386_binary_call
  i386_strings i386_memory i386_byte_copy i386_byte_copy_word.
From Stdlib Require Import NArith Lia.
Open Scope N.
Definition string_copy_pre (s0:store):=models x86typctx s0 /\ forall k,
  nonzero_prefix (s0 V_MEM32) (binary_arg2 s0) k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 8) 24 (cdecl_arg s0) (k+1) /\
  ~overlap 32 (msub 32 (s0 R_ESP) 8) 8 (binary_arg2 s0+k) 4 /\
  ~overlap 32 (cdecl_arg s0) k (binary_arg2 s0+k) 4.
Definition string_copy_memory (s0:store) (k:N):=
  copy_bytes (s0 V_MEM32) (binary_arg2 s0) (cdecl_arg s0) k (save_si_bx_memory s0).
Definition string_copy_endmem (s0:store) (k:N):=
  copy_terminated (s0 V_MEM32) (binary_arg2 s0) (cdecl_arg s0) k (save_si_bx_memory s0).
Definition string_copy_reference (s0:store) (k:N):=s0[V_MEM32:=string_copy_endmem s0 k].
Definition string_copy_contents (s0:store) (k:N) (m:memory):=
  (forall i,i<k ->getmem 32 LittleE 1 m (cdecl_arg s0+i)=getmem 32 LittleE 1 (s0 V_MEM32) (binary_arg2 s0+i)) /\
  getmem 32 LittleE 1 m (cdecl_arg s0+k)=0.
Lemma string_copy_bound:forall s0 k,string_copy_pre s0 ->nonzero_prefix (s0 V_MEM32) (binary_arg2 s0) k ->k+1<2^32.
Proof.
  intros s0 k [_ SAFE] PREFIX. destruct (SAFE k PREFIX) as [NO _].
  destruct (noverlap_sep 32 (msub 32 (s0 R_ESP) 8) 24 (cdecl_arg s0) (k+1) NO) as [LE|ZERO];[|discriminate].
  pose proof (msub_lt 32 (msub 32 (s0 R_ESP) 8) (cdecl_arg s0)). lia.
Qed.
Lemma string_copy_source_word:forall s0 k,string_copy_pre s0 ->nonzero_prefix (s0 V_MEM32) (binary_arg2 s0) k ->
  getmem 32 LittleE 4 (string_copy_memory s0 k) (binary_arg2 s0+k)=getmem 32 LittleE 4 (s0 V_MEM32) (binary_arg2 s0+k).
Proof.
  intros s0 k [_ SAFE] PREFIX. destruct (SAFE k PREFIX) as (DEST & STACK & SOURCE).
  unfold string_copy_memory. rewrite (copy_bytes_frame _ _ _ _ _ _ _ SOURCE).
  unfold save_si_bx_memory. replace (binary_arg2 s0+k) with ((binary_arg2 s0+k)+0) by lia.
  rewrite !descending_stack_read with (total:=8) (n:=4) by (try exact STACK;lia). reflexivity.
Qed.
Lemma string_copy_source_byte:forall s0 k,string_copy_pre s0 ->nonzero_prefix (s0 V_MEM32) (binary_arg2 s0) k ->
  getmem 32 LittleE 1 (string_copy_memory s0 k) (binary_arg2 s0+k)=getmem 32 LittleE 1 (s0 V_MEM32) (binary_arg2 s0+k).
Proof.
  intros. pose proof (string_copy_source_word s0 k H H0) as WORD.
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. rewrite !getmem_mod in WORD. exact WORD.
Qed.
Lemma string_copy_step1:forall s0 k,setmem 32 LittleE 1 (string_copy_memory s0 k) (cdecl_arg s0+k)
  (getmem 32 LittleE 1 (s0 V_MEM32) (binary_arg2 s0+k))=string_copy_memory s0 (k+1).
Proof. intros. unfold string_copy_memory. rewrite copy_bytes_succ. reflexivity. Qed.
Lemma string_copy_step4:forall s0 k,setmem 32 LittleE 4 (string_copy_memory s0 k) (cdecl_arg s0+k)
  (getmem 32 LittleE 4 (s0 V_MEM32) (binary_arg2 s0+k))=string_copy_memory s0 (k+4).
Proof. intros. apply copy_bytes_four. Qed.
Lemma string_copy_contents_endmem:forall s0 k,string_copy_pre s0 ->nonzero_prefix (s0 V_MEM32) (binary_arg2 s0) k ->
  string_copy_contents s0 k (string_copy_endmem s0 k).
Proof.
  intros s0 k PRE PREFIX. pose proof (string_copy_bound s0 k PRE PREFIX) as BOUND.
  unfold string_copy_contents,string_copy_endmem. split;[intros;apply copy_terminated_prefix;lia|apply copy_terminated_zero].
Qed.
Lemma string_copy_saved_slot:forall s0 k depth,string_copy_pre s0 ->nonzero_prefix (s0 V_MEM32) (binary_arg2 s0) k ->depth<=8 ->
  getmem 32 LittleE 4 (string_copy_endmem s0 k) (msub 32 (s0 R_ESP) depth)=
  getmem 32 LittleE 4 (save_si_bx_memory s0) (msub 32 (s0 R_ESP) depth).
Proof.
  intros s0 k depth [_ SAFE] PREFIX DEP. destruct (SAFE k PREFIX) as [NO _]. unfold string_copy_endmem.
  apply copy_terminated_frame. apply noverlap_symmetry. eapply noverlap_shrink;[|exact NO].
  rewrite stack_depth_difference,msub_sub by lia. rewrite N.mod_small by lia. lia.
Qed.
Lemma string_copy_return_address:forall s0 k,string_copy_pre s0 ->nonzero_prefix (s0 V_MEM32) (binary_arg2 s0) k ->
  getmem 32 LittleE 4 (string_copy_endmem s0 k) (s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP).
Proof.
  intros s0 k PRE PREFIX. pose proof (string_copy_saved_slot s0 k 0 PRE PREFIX ltac:(lia)) as RA.
  rewrite msub_0_r,!getmem_mod_l in RA.
  pose proof (save_si_bx_stack_word s0 0 ltac:(lia)) as WORD. rewrite N.add_0_l in WORD. rewrite WORD in RA. exact RA.
Qed.

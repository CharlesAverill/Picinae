(* Linked code and shared unary stack interface for wcschr. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_deep_stack i386_stack4 i386_unary_call
  i386_binary_call i386_strings i386_wstrlen i386_wsearch wcslen_proof wcschr_i386 pc_thunk_bx_i386 wcslen_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wcschr_linked : program := updateall2 wcschr_i386 (updateall2 pc_thunk_bx_i386 wcslen_i386).
Lemma wcschr_linked_caller : wcschr_i386 ⊆2 wcschr_linked.
Proof.
  intros s a insn H. unfold wcschr_linked,updateall2,updateall,wcschr_i386,pc_thunk_bx_i386,wcslen_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma wcschr_linked_wcslen : wcslen_i386 ⊆2 wcschr_linked.
Proof. intros s a insn H. unfold wcschr_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma wcschr_linked_thunk : pc_thunk_bx_i386 ⊆2 wcschr_linked.
Proof.
  intros s a insn H. unfold wcschr_linked,updateall2,updateall,pc_thunk_bx_i386,wcslen_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem wcschr_linked_welltyped : welltyped_prog x86typctx wcschr_linked.
Proof.
  intros s a. unfold wcschr_linked,updateall2,updateall.
  destruct (wcslen_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (wcslen_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply wcschr_i386.welltyped.
Qed.



Definition wcschr_got:N:=0xb4f9c.
Definition wcschr_needle:=binary_arg2.
Definition wcschr_m1:=unary_m1.
Definition wcschr_m2 (s0:store):=unary_m2 s0 0x47b86.
Definition wcschr_m3 (s0:store):=unary_m3 s0 0x47b86.
Definition wcschr_m4 (s0:store):=unary_memory s0 0x47b86 0x47ba8.
Definition wcschr_snapshot (s0:store) (called:bool):=if called then wcschr_m4 s0 else wcschr_m2 s0.
Definition wcschr_memory (s0:store):=wcschr_snapshot s0 (wcschr_needle s0=?0).
Definition wcschr_reference (s0:store):=s0[V_MEM32:=wcschr_memory s0].
Definition wcschr_frame:=unary_frame.
Definition wcschr_pre (s0:store):=models x86typctx s0 /\
  forall k,wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k ->
  ~overlap 32 (msub 32 (s0 R_ESP) 32) 32 (cdecl_arg s0+4*k) 4.
Definition wcschr_prefix (s0:store) (k:N):=
  wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k /\
  forall i,i<k ->getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*i)<>wcschr_needle s0.
Definition wcschr_result (s0:store) (result:N):=exists k,wcschr_prefix s0 k /\
  ((getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)=wcschr_needle s0 /\
    result=(cdecl_arg s0+4*k) mod 2^32) \/
   (getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)=0 /\
    wcschr_needle s0<>0 /\ result=0)).
Definition wcschr_length (s0:store) (result:N):=exists k,
  wide_first_nul (s0 V_MEM32) (cdecl_arg s0) k /\ result=wide_length32 k.
Lemma wcschr_m2_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcschr_m2 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_m2_stack;assumption. Qed.
Lemma wcschr_m4_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcschr_m4 s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof. intros. apply unary_outer_stack;assumption. Qed.
Lemma wcschr_resave_arg:forall s0,
  setmem 32 LittleE 4 (wcschr_m3 s0) (4+s0 R_ESP) (cdecl_arg s0)=wcschr_m3 s0.
Proof.
  intro s0. assert (READ:getmem 32 LittleE 4 (wcschr_m3 s0) (4+s0 R_ESP)=cdecl_arg s0).
  { unfold wcschr_m3,unary_m3. rewrite (N.add_comm 4 (s0 R_ESP)),deep_stack_word_frame by lia.
    rewrite (N.add_comm (s0 R_ESP) 4),unary_m2_stack by lia. reflexivity. }
  rewrite <- READ. apply setmem_getmem.
Qed.
Lemma wcschr_saved_bx:forall s0,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (wcschr_memory s0) (msub 32 (s0 R_ESP) 4)=s0 R_EBX.
Proof.
  intros s0 BOUND. unfold wcschr_memory,wcschr_snapshot. destruct (wcschr_needle s0=?0).
  - apply unary_saved_bx;exact BOUND.
  - unfold wcschr_m2,unary_m2,unary_m1. rewrite deep_saved_word_frame by lia.
    apply saved_ebx_load;exact BOUND.
Qed.
Lemma wcschr_outer_stack:forall s0 off,off<=8 ->
  getmem 32 LittleE 4 (wcschr_memory s0) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold wcschr_memory,wcschr_snapshot. destruct (wcschr_needle s0=?0).
  - apply unary_outer_stack;exact OFF.
  - apply unary_m2_stack;exact OFF.
Qed.
Lemma wcschr_snapshot_read:forall s0 called k,wcschr_pre s0 ->
  wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k ->
  getmem 32 LittleE 4 (wcschr_snapshot s0 called) (cdecl_arg s0+4*k)=
  getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k).
Proof.
  intros s0 called k (_ & AVOID) PREFIX. pose proof (AVOID k PREFIX) as NO.
  assert (CELL:forall depth,4<=depth ->depth<=32 ->
    ~overlap 32 (msub 32 (s0 R_ESP) depth) 4 (cdecl_arg s0+4*k) 4).
  { intros depth LO HI. eapply descending_stack_subregion;[exact HI|exact LO|exact NO]. }
  unfold wcschr_snapshot. destruct called;
    unfold wcschr_m4,wcschr_m2,unary_memory,unary_m3,unary_m2,unary_m1,save_ebx_memory;
    rewrite !getmem_noverlap by (apply noverlap_symmetry;apply CELL;lia);reflexivity.
Qed.
Lemma wcschr_callee_length:forall s0 sc value,wcschr_pre s0 ->
  wcschr_frame s0 (wcschr_m4 s0) 32 sc ->wcslen_result sc value ->wcschr_length s0 value.
Proof.
  intros s0 sc value PRE FRAME RESULT.
  pose proof (unary_callee_arg s0 0x47b86 0x47ba8 sc FRAME) as ARG.
  unfold wcslen_result in RESULT. rewrite ARG,(proj1 FRAME) in RESULT.
  destruct RESULT as (k & FIRST & VALUE). destruct FIRST as (K & PREFIX & ZERO).
  assert (ORIGINAL:wide_prefix (s0 V_MEM32) (cdecl_arg s0) 0 k).
  { refine (conditional_prefix_transfer
      (fun i=>getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*i))
      (fun i=>getmem 32 LittleE 4 (wcschr_m4 s0) (cdecl_arg s0+4*i)) _ k PREFIX).
    intros j P. exact (wcschr_snapshot_read s0 true j PRE P). }
  pose proof (wcschr_snapshot_read s0 true k PRE ORIGINAL) as READ.
  change (getmem 32 LittleE 4 (wcschr_m4 s0) (cdecl_arg s0+4*k)=
    getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)) in READ.
  rewrite READ in ZERO.
  exists k. split;[repeat split;assumption|exact VALUE].
Qed.
Lemma wcschr_prefix_advance:forall s0 k,wcschr_prefix s0 k ->
  getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)<>0 ->
  getmem 32 LittleE 4 (s0 V_MEM32) (cdecl_arg s0+4*k)<>wcschr_needle s0 ->wcschr_prefix s0 (k+1).
Proof.
  intros s0 k [PREFIX NOMATCH] NONZERO DIFFERENT. split.
  - apply wide_prefix_advance;[exact PREFIX|]. rewrite getmem_mod_l. exact NONZERO.
  - intros i I. destruct (N.lt_ge_cases i k) as [LT|GE];[exact (NOMATCH i LT)|].
    replace i with k by (clear - I GE;lia). exact DIFFERENT.
Qed.
Lemma wcschr_zero_result:forall s0 value,wcschr_needle s0=0 ->wcschr_length s0 value ->
  wcschr_result s0 ((cdecl_arg s0+4*value) mod 2^32).
Proof.
  intros s0 value NEEDLE (k & FIRST & VALUE). destruct FIRST as (K & PREFIX & ZERO). exists k. split.
  - split;[exact PREFIX|]. rewrite NEEDLE. exact PREFIX.
  - left. rewrite NEEDLE. split;[exact ZERO|]. rewrite VALUE. apply wide_length32_address.
Qed.

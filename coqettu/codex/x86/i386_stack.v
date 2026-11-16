(* A one-word i386 stack save and its disjointness/frame properties. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition save_ebx_memory (s0 : store) : memory :=
  setmem 32 LittleE 4 (s0 V_MEM32) (msub 32 (s0 R_ESP) 4) (s0 R_EBX).

Definition save_ebx_reference (s0 : store) : store :=
  s0[V_MEM32 := save_ebx_memory s0].

Lemma stack_save_frame : forall m sp value off,
  off <= 12 ->
  getmem 32 LittleE 4
    (setmem 32 LittleE 4 m (msub 32 sp 4) value) (sp+off) =
  getmem 32 LittleE 4 m (sp+off).
Proof.
  intros m sp value off OFF. apply getmem_frame.
  - left. rewrite <- msub_add_distr.
    replace (4+(sp+off)) with (sp+(4+off)) by lia.
    rewrite msub_add_distr, msub_diag, msub_0_l.
    rewrite (N.mod_small (4+off) (2^32)) by lia.
    rewrite N.mod_small by lia. lia.
  - left. rewrite msub_msub_distr, add_msub_l, mp2_add_l.
    rewrite N.mod_small by lia. lia.
Qed.

Lemma saved_ebx_load : forall s0,
  s0 R_EBX < 2^32 ->
  getmem 32 LittleE 4 (save_ebx_memory s0) (msub 32 (s0 R_ESP) 4) = s0 R_EBX.
Proof.
  intros s0 BX. unfold save_ebx_memory.
  rewrite getmem_setmem by lia. apply N.mod_small. exact BX.
Qed.

Lemma save_ebx_stack_word : forall s0 off, off <= 12 ->
  getmem 32 LittleE 4 (save_ebx_memory s0) (off+s0 R_ESP) =
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold save_ebx_memory.
  rewrite (N.add_comm off (s0 R_ESP)). apply stack_save_frame. exact OFF.
Qed.

Lemma save_ebx_byte : forall s0 p n i,
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 p n -> i < n ->
  getmem 32 LittleE 1 (save_ebx_memory s0) (p+i) =
  getmem 32 LittleE 1 (s0 V_MEM32) (p+i).
Proof.
  intros s0 p n i NO I. unfold save_ebx_memory.
  pose proof (getmem_frame_noverlap_index_l 32 LittleE LittleE (s0 V_MEM32)
    (msub 32 (s0 R_ESP) 4) 4 p n 0 i 4 1 (s0 R_EBX) NO) as FRAME.
  rewrite N.add_0_r in FRAME. apply FRAME; [reflexivity|clear - I; lia].
Qed.

Definition ebx_save_frame (s0 s : store) : Prop :=
  s V_MEM32 = save_ebx_memory s0 /\ s R_ESP = msub 32 (s0 R_ESP) 4 /\
  s R_ESI = s0 R_ESI /\ s R_EDI = s0 R_EDI /\ s R_EBP = s0 R_EBP /\
  s A_READ = s0 A_READ /\ s A_WRITE = s0 A_WRITE.


Lemma save_ebx_wide : forall s0 p n i,
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 p (4*n) -> i < n ->
  getmem 32 LittleE 4 (save_ebx_memory s0) (p+4*i) =
  getmem 32 LittleE 4 (s0 V_MEM32) (p+4*i).
Proof.
  intros s0 p n i NO I. unfold save_ebx_memory.
  pose proof (getmem_frame_noverlap_index_l 32 LittleE LittleE (s0 V_MEM32)
    (msub 32 (s0 R_ESP) 4) 4 p (4*n) 0 (4*i) 4 4 (s0 R_EBX) NO) as FRAME.
  rewrite N.add_0_r in FRAME. apply FRAME; [reflexivity|clear - I; lia].
Qed.

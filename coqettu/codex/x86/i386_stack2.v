(* Two descending i386 stack saves: ESI, then EBX. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_stack.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition save_si_bx_memory (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (s0 V_MEM32) (msub 32 (s0 R_ESP) 4) (s0 R_ESI))
    (msub 32 (s0 R_ESP) 8) (s0 R_EBX).
Definition save_si_bx_reference (s0 : store) := s0[V_MEM32 := save_si_bx_memory s0].
Definition si_bx_save_frame (s0 s : store) :=
  s V_MEM32=save_si_bx_memory s0 /\ s R_ESP=msub 32 (s0 R_ESP) 8 /\
  s R_EDI=s0 R_EDI /\ s R_EBP=s0 R_EBP /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.

Lemma stack_depth_frame : forall m sp value depth off,
  4 <= depth -> depth <= 8 -> off <= 12 ->
  getmem 32 LittleE 4 (setmem 32 LittleE 4 m (msub 32 sp depth) value) (sp+off) =
  getmem 32 LittleE 4 m (sp+off).
Proof.
  intros m sp value depth off LOWER UPPER OFF. apply getmem_frame.
  - left. rewrite <- msub_add_distr.
    replace (depth+(sp+off)) with (sp+(depth+off)) by lia.
    rewrite msub_add_distr, msub_diag, msub_0_l.
    rewrite (N.mod_small (depth+off) (2^32)) by lia.
    rewrite N.mod_small by lia. lia.
  - left. rewrite msub_msub_distr, add_msub_l, mp2_add_l.
    rewrite N.mod_small by lia. lia.
Qed.

Lemma save_si_bx_stack_word : forall s0 off, off <= 12 ->
  getmem 32 LittleE 4 (save_si_bx_memory s0) (off+s0 R_ESP) =
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 off OFF. unfold save_si_bx_memory. rewrite (N.add_comm off (s0 R_ESP)).
  rewrite !stack_depth_frame by lia. reflexivity.
Qed.

Lemma saved_si_bx_load_bx : forall s0, s0 R_EBX < 2^32 ->
  getmem 32 LittleE 4 (save_si_bx_memory s0) (msub 32 (s0 R_ESP) 8) = s0 R_EBX.
Proof.
  intros s0 BOUND. unfold save_si_bx_memory.
  rewrite getmem_setmem by lia. apply N.mod_small. exact BOUND.
Qed.

Lemma saved_si_bx_load_si : forall s0, s0 R_ESI < 2^32 ->
  getmem 32 LittleE 4 (save_si_bx_memory s0) (msub 32 (s0 R_ESP) 4) = s0 R_ESI.
Proof.
  intros s0 BOUND. unfold save_si_bx_memory. rewrite getmem_frame.
  - rewrite getmem_setmem by lia. apply N.mod_small. exact BOUND.
  - left. rewrite msub_msub_distr, msub_comm, msub_diag.
    change (4 <= 4294967292). lia.
  - left. rewrite msub_msub_distr, msub_comm, msub_diag.
    change (4 <= 4). lia.
Qed.

Lemma save_si_bx_byte : forall s0 a,
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 a 1 ->
  ~overlap 32 (msub 32 (s0 R_ESP) 8) 4 a 1 ->
  getmem 32 LittleE 1 (save_si_bx_memory s0) a = getmem 32 LittleE 1 (s0 V_MEM32) a.
Proof.
  intros s0 a NO4 NO8. unfold save_si_bx_memory.
  rewrite !getmem_noverlap by (apply noverlap_symmetry; assumption). reflexivity.
Qed.

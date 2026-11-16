(* Modular cursors and suffix invariants for a backwards byte search. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_stack2.
From Stdlib Require Import NArith Lia.
Open Scope N.

Definition nonmatching_suffix (m : memory) (p c k n : N) :=
  forall i, k<=i -> i<n -> getmem 32 LittleE 1 m (p+i)<>c.
Definition reverse_search_result (m : memory) (p c n result : N) :=
  (result=0 /\ nonmatching_suffix m p c 0 n) \/
  exists k, k<n /\ nonmatching_suffix m p c (k+1) n /\
    getmem 32 LittleE 1 m (p+k)=c /\ result=(p+k) mod 2^32.

Lemma reverse_cursor_zero : forall p k, k<2^32 ->
  (msub 32 (p+k) 1 = msub 32 p 1 <-> k=0).
Proof.
  intros p k K. split.
  - intro EQ. apply msub_cancel_r in EQ.
    pose proof (f_equal (fun v => msub 32 v p) EQ) as DELTA.
    cbn beta in DELTA. rewrite !msub_mod_l, add_msub_l, msub_diag in DELTA by reflexivity.
    rewrite (N.mod_small _ _ K) in DELTA. exact DELTA.
  - intro EQ. subst k. rewrite N.add_0_r. reflexivity.
Qed.

Lemma reverse_cursor_byte : forall p k, 0<k ->
  msub 32 (p+k) 1 = (p+(k-1)) mod 2^32.
Proof.
  intros p k POS. replace (p+k) with ((p+(k-1))+1) by lia.
  apply add_msub_r.
Qed.

Lemma reverse_cursor_previous : forall p k, 0<k ->
  msub 32 (msub 32 (p+k) 1) 1 = msub 32 (p+(k-1)) 1.
Proof.
  intros p k POS. rewrite (reverse_cursor_byte p k POS).
  apply msub_mod_l. reflexivity.
Qed.

Lemma reverse_initial_cursor : forall p n,
  (4294967295+p+n) mod 2^32 = msub 32 (p+n) 1.
Proof.
  intros p n. replace 4294967295 with (msub 32 0 1) by reflexivity.
  rewrite <- N.add_assoc, N.add_comm, add_msub_assoc, N.add_0_r. reflexivity.
Qed.

Lemma nonmatching_suffix_previous : forall m p c k n,
  0<k -> nonmatching_suffix m p c k n ->
  getmem 32 LittleE 1 m (p+(k-1))<>c ->
  nonmatching_suffix m p c (k-1) n.
Proof.
  intros m p c k n POS SUFFIX BYTE i LOWER UPPER.
  destruct (N.lt_ge_cases i k) as [LT|GE].
  - replace i with (k-1) by (clear - POS LOWER LT; lia). exact BYTE.
  - exact (SUFFIX i GE UPPER).
Qed.

Lemma stack_region_byte : forall m sp depth value p n i,
  ~overlap 32 (msub 32 sp depth) 4 p n -> i<n ->
  getmem 32 LittleE 1 (setmem 32 LittleE 4 m (msub 32 sp depth) value) (p+i)=
  getmem 32 LittleE 1 m (p+i).
Proof.
  intros m sp depth value p n i NO I.
  pose proof (getmem_frame_noverlap_index_l 32 LittleE LittleE m
    (msub 32 sp depth) 4 p n 0 i 4 1 value NO) as FRAME.
  rewrite N.add_0_r in FRAME. apply FRAME; [reflexivity|clear - I; lia].
Qed.

Lemma save_si_bx_region_byte : forall s0 p n i,
  ~overlap 32 (msub 32 (s0 R_ESP) 4) 4 p n ->
  ~overlap 32 (msub 32 (s0 R_ESP) 8) 4 p n -> i<n ->
  getmem 32 LittleE 1 (save_si_bx_memory s0) (p+i)=
  getmem 32 LittleE 1 (s0 V_MEM32) (p+i).
Proof.
  intros s0 p n i NO4 NO8 I. unfold save_si_bx_memory.
  rewrite !stack_region_byte with (n:=n) by assumption. reflexivity.
Qed.

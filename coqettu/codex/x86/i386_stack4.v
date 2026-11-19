(* Four descending register saves and an optional local word. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_deep_stack.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Lemma descending_stack_subregion:forall sp total depth len p n,
  depth<=total ->len<=depth ->~overlap 32 (msub 32 sp total) total p n ->
  ~overlap 32 (msub 32 sp depth) len p n.
Proof.
  intros sp total depth len p n DEP LEN NO. eapply noverlap_shrink;[|exact NO].
  rewrite stack_depth_difference,msub_sub by lia.
  pose proof (mp2_mod_le (total-depth) 32). lia.
Qed.
Lemma descending_stack_read:forall m sp total depth value p n off len,
  4<=depth ->depth<=total ->~overlap 32 (msub 32 sp total) total p n ->off+len<=n ->
  getmem 32 LittleE len (setmem 32 LittleE 4 m (msub 32 sp depth) value) (p+off)=
  getmem 32 LittleE len m (p+off).
Proof.
  intros m sp total depth value p n off len LO HI NO FIT.
  pose proof (descending_stack_subregion sp total depth 4 p n HI LO NO) as CELL.
  pose proof (getmem_frame_noverlap_index_l 32 LittleE LittleE m
    (msub 32 sp depth) 4 p n 0 off 4 len value CELL) as FRAME.
  rewrite N.add_0_r in FRAME. apply FRAME;[reflexivity|exact FIT].
Qed.
Definition save4_registers (s0:store):=
  setmem 32 LittleE 4
  (setmem 32 LittleE 4
  (setmem 32 LittleE 4
  (setmem 32 LittleE 4 (s0 V_MEM32) (msub 32 (s0 R_ESP) 4) (s0 R_EBP))
    (msub 32 (s0 R_ESP) 8) (s0 R_EDI))
    (msub 32 (s0 R_ESP) 12) (s0 R_ESI))
    (msub 32 (s0 R_ESP) 16) (s0 R_EBX).
Definition save4_memory (s0:store) (local:option N):=
  match local with None=>save4_registers s0 |Some v=>
  setmem 32 LittleE 4 (save4_registers s0) (msub 32 (s0 R_ESP) 20) v end.
Definition save4_reference (s0:store) (local:option N):=s0[V_MEM32:=save4_memory s0 local].
Definition save4_frame (s0:store) (local:option N) (s:store):=
  s V_MEM32=save4_memory s0 local /\ s R_ESP=msub 32 (s0 R_ESP) 20 /\
  s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Lemma save4_stack_word:forall s0 local off,off<=12 ->
  getmem 32 LittleE 4 (save4_memory s0 local) (off+s0 R_ESP)=
  getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 [v|] off OFF;unfold save4_memory,save4_registers;
  rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia;reflexivity.
Qed.
Lemma save4_stack_byte:forall s0 local off,off<=12 ->
  getmem 32 LittleE 1 (save4_memory s0 local) (off+s0 R_ESP)=
  getmem 32 LittleE 1 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 local off OFF.
  pose proof (save4_stack_word s0 local off OFF) as WORD.
  apply (f_equal (fun x=>x mod 2^(1*8))) in WORD. rewrite !getmem_mod in WORD. exact WORD.
Qed.
Lemma save4_region_read:forall s0 local p n off len,
  ~overlap 32 (msub 32 (s0 R_ESP) 20) 20 p n ->off+len<=n ->
  getmem 32 LittleE len (save4_memory s0 local) (p+off)=
  getmem 32 LittleE len (s0 V_MEM32) (p+off).
Proof.
  intros s0 [v|] p n off len NO FIT;unfold save4_memory,save4_registers;
  rewrite !descending_stack_read with (total:=20) (n:=n) by (first[exact NO|exact FIT|lia]);reflexivity.
Qed.
Lemma save4_load_bx:forall s0 local,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (save4_memory s0 local) (msub 32 (s0 R_ESP) 16)=s0 R_EBX.
Proof.
  intros s0 [v|] BOUND;unfold save4_memory,save4_registers;
  rewrite ?deep_saved_word_frame by lia;rewrite getmem_setmem by lia;apply N.mod_small;exact BOUND.
Qed.
Lemma save4_load_si:forall s0 local,s0 R_ESI<2^32 ->
  getmem 32 LittleE 4 (save4_memory s0 local) (msub 32 (s0 R_ESP) 12)=s0 R_ESI.
Proof.
  intros s0 [v|] BOUND;unfold save4_memory,save4_registers;
  rewrite !deep_saved_word_frame by lia;rewrite getmem_setmem by lia;apply N.mod_small;exact BOUND.
Qed.
Lemma save4_load_di:forall s0 local,s0 R_EDI<2^32 ->
  getmem 32 LittleE 4 (save4_memory s0 local) (msub 32 (s0 R_ESP) 8)=s0 R_EDI.
Proof.
  intros s0 [v|] BOUND;unfold save4_memory,save4_registers;
  rewrite !deep_saved_word_frame by lia;rewrite getmem_setmem by lia;apply N.mod_small;exact BOUND.
Qed.
Lemma save4_load_bp:forall s0 local,s0 R_EBP<2^32 ->
  getmem 32 LittleE 4 (save4_memory s0 local) (msub 32 (s0 R_ESP) 4)=s0 R_EBP.
Proof.
  intros s0 [v|] BOUND;unfold save4_memory,save4_registers;
  rewrite !deep_saved_word_frame by lia;rewrite getmem_setmem by lia;apply N.mod_small;exact BOUND.
Qed.
Lemma save4_local_load:forall s0 v,
  getmem 32 LittleE 4 (save4_memory s0 (Some v)) (msub 32 (s0 R_ESP) 20)=v mod 2^32.
Proof. intros s0 v. unfold save4_memory. rewrite getmem_setmem by lia. reflexivity. Qed.

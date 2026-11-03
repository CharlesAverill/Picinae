(* PARTIAL vListInitialise: proposed finite ARMv6-M IL functional correctness.
   The first full build failed; main and unchecked proofs below are Aborted.
   No complete function-correctness result is exported by this checkpoint.

   PROVENANCE / AUTHOR
   Official FreeRTOS V11.1.0 dbf70559b27d39c1fdb68dfb9a32140b6a6777a0.
   Cortex-M0 ELF SHA256:
   5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Accepted e05 finite map vListInitialise_armv6m_prog, unchanged; accepted
   r00 model at 4ff26413448da4d8f064b0273ac5472cc9de7e5a.
   Initial author: OpenAI gpt-6-astra, xhigh/priority, one-shot attempt.
   Validation status and final producer: notes/r02-list-init/README.md.

   ENGLISH SPEC / ABI / PATH
   At 0x40, R0=p is a nonnull, four-byte-aligned, nonwrapping 20-byte List_t.
   The initial store is welltyped and every byte of that object is writable.
   Original memory is arbitrary subject only to its architectural width.
   No other object/disjointness premise, input list validity, callee, scheduler,
   IRQ, CPU feature, or tunable contract is required by this sequential IL.
   No loads, stack accesses, literal pools, calls, or branches precede BX LR.
   Stores: 0x44 index at p+4; 0x4a sentinel value at p+8; 0x4c/0x4e links
   at p+12/p+16; 0x52 count at p. At BX (0x54), count=0, index=p+8,
   sentinel value=0xffffffff, next=previous=p+8. Exact memory equals r00's
   empty_image of ORIGINAL memory. ALL original bytes outside the 20 bytes
   persist. The embedded 12-byte sentinel has no owner/container fields.
   R0 stays p, R2=0xffffffff, R3=0, N=0, Z=1, C=0, V=0.
   R1, R4-R12, SP, LR, permissions and temporary variables are preserved.
   The separate return step requires LR mod 2=1 and LR<0xfffffff0, explicitly
   excluding the exception-return range; destination is LR & 0xfffffffe.
   No stack-alignment premise is needed because SP is never dereferenced.

   BOUNDARY
   These are partial-correctness and ordinary modeled-return claims about the
   actual finite IL map. No termination, hardware exception-return, asynchronous
   execution, or binary/lifter refinement theorem is asserted. The immutable
   generated map and inherited ISA/lifter provenance remain trusted. Permission
   witnesses use symbolic ones_bound/ones_spec_low, never bitmap evaluation.
 *)

Require Import Picinae_armv6m.
Require Import vListInitialise_armv6m armv6m_list_model.
From Stdlib Require Import NArith Lia List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Theorem list_init_nwc:
  forall s2 s1, vListInitialise_armv6m_prog s1 = vListInitialise_armv6m_prog s2.
Proof. reflexivity. Qed.

Theorem list_init_welltyped:
  welltyped_prog armv6mtypctx vListInitialise_armv6m_prog.
Proof. exact vListInitialise_armv6m_welltyped. Qed.

Definition list_init_preserved (v:armv6mvar) : Prop :=
  match v with V_MEM32 | R_R2 | R_R3 | F_N | F_Z | F_C | F_V => False
             | _ => True end.

Theorem list_init_register_frame:
  forall v, list_init_preserved v ->
  forall_endstates vListInitialise_armv6m_prog (fun _ s _ s' => s v = s' v).
Proof.
  intros v KEEP. destruct v; cbn in KEEP; try contradiction;
    apply noassign_prog_same; prove_noassign.
Qed.

Definition list_init_pre (p:N) (s:store) :=
  object32 p list_size /\ s R_R0 = p /\ MemAcc mem_writable s p 32 20.

Definition list_init_post (s0:store) (p:N) (s:store) :=
  s V_MEM32 = empty_image (s0 V_MEM32) p /\
  s R_R0 = p /\ s R_R2 = list_max_value /\ s R_R3 = 0 /\
  s F_N = 0 /\ s F_Z = 1 /\ s F_C = 0 /\ s F_V = 0.

Definition list_init_exit (t:trace) :=
  match t with (Addr 0x54,_)::_ => true | _ => false end.

Definition list_init_invs (s0:store) (p:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    match a with
    | 0x40 => Some (s = s0)
    | 0x54 => Some (list_init_post s0 p s)
    | _ => None
    end
  | _ => None end.

(* This is a memory expression in the observed store order, not a program. *)
Definition list_init_stores (m p:N) :=
  write_field32
    (write_field32
      (write_field32
        (write_field32 (write_field32 m p 4 (p+8)) p 8 list_max_value)
        p 12 (p+8))
      p 16 (p+8))
    p 0 0.

Lemma list_init_swap_zero:
  forall m p off v, p+20 <= 2^32 -> In off [4;8;12;16] ->
  write_field32 (write_field32 m p off v) p 0 0 =
  write_field32 (write_field32 m p 0 0) p off v.
Proof.
  intros m p off v B IN. unfold write_field32. apply setmem_swap.
  apply (fields20_separate p off 0 B).
  - cbn in IN |- *. tauto.
  - cbn. tauto.
  - cbn in IN. destruct IN as [<-|[<-|[<-|[<-|[]]]]]; discriminate.
Qed.

Theorem list_init_stores_image:
  forall m p, object32 p list_size -> list_init_stores m p = empty_image m p.
Proof.
  intros m p OBJ.
  assert (B: p+20 <= 2^32) by exact (proj2 (proj2 (proj2 OBJ))).
  unfold list_init_stores, empty_image, image20.
  repeat rewrite list_init_swap_zero by (assumption || (cbn; tauto)).
  reflexivity.
Qed.

Theorem list_init_post_layout_frame:
  forall s0 p s, object32 p list_size -> list_init_post s0 p s ->
  empty_list (s V_MEM32) p /\
  outside_frame32 (s0 V_MEM32) (s V_MEM32) p list_size.
Proof.
  intros s0 p s OBJ [MEM REST]. rewrite MEM. split.
  - apply empty_image_spec. exact OBJ.
  - apply empty_image_frame.
Qed.

(* Entry witnesses for EVERY bounded original memory and supported pointer.
   Granting all modeled addresses write permission is a satisfiability witness,
   not an additional precondition of the functional theorem. *)
Definition list_init_entry_store (m p lr:N) : store :=
  update (update (update (memory_store32 m) R_R0 p) R_LR lr)
    A_WRITE (N.ones (2^32)).

Theorem list_init_entry_witness:
  forall m p lr, m < memsize 32 -> object32 p list_size -> lr < 2^32 ->
  exists s:store, models armv6mtypctx s /\ list_init_pre p s /\
    s V_MEM32 = m /\ s R_LR = lr.
Proof.
  intros m p lr MB OBJ LB. exists (list_init_entry_store m p lr).
  assert (PB: p < 2^32) by exact (proj1 (proj2 (proj2 OBJ))).
  split.
  - unfold list_init_entry_store.
    apply models_update; [apply ones_bound|].
    apply models_update; [exact LB|].
    apply models_update; [exact PB|].
    apply memory_store32_welltyped. exact MB.
  - split.
    + split; [exact OBJ|]. split.
      * unfold list_init_entry_store. rewrite !update_frame by discriminate.
        apply update_updated.
      * intros n BN. unfold mem_writable, list_init_entry_store.
        rewrite update_updated. apply N.ones_spec_low. apply mp2_mod_lt.
    + unfold list_init_entry_store, memory_store32.
      rewrite !update_frame by discriminate. rewrite !update_updated.
      split; reflexivity.
Qed.

Theorem list_init_concrete_entry_witness:
  forall m, m < memsize 32 ->
  exists s:store, models armv6mtypctx s /\ list_init_pre 4096 s /\
    s V_MEM32 = m /\ s R_LR = 257.
Proof.
  intros m MB. apply list_init_entry_witness; try assumption.
  - exact (proj1 list_regions_witness).
  - reflexivity.
Qed.

Theorem list_init_correct:
  forall s0 t s' x' p
    (ENTRY: startof t (x',s') = (Addr 0x40,s0))
    (MDL: models armv6mtypctx s0) (INPUT: list_init_pre p s0),
  satisfies_all vListInitialise_armv6m_prog (list_init_invs s0 p)
    list_init_exit ((x',s')::t).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are archived in notes/r02-list-init/. *)
Abort.

(* Specialize the actual execution invariant at BX; the post contains the
   exact image, while this theorem exposes its fields and original-byte frame. *)
Theorem list_init_at_bx:
  forall s0 t s p,
  startof t (Addr 0x54,s) = (Addr 0x40,s0) ->
  models armv6mtypctx s0 -> list_init_pre p s0 ->
  exec_prog vListInitialise_armv6m_prog ((Addr 0x54,s)::t) ->
  unterminated list_init_exit t ->
  list_init_post s0 p s /\ empty_list (s V_MEM32) p /\
  outside_frame32 (s0 V_MEM32) (s V_MEM32) p list_size /\
  (forall v, list_init_preserved v -> s v = s0 v).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are archived in notes/r02-list-init/. *)
Abort.

Definition list_init_ordinary_lr (lr:N) := lr mod 2 = 1 /\ lr < 0xfffffff0.

Theorem list_init_return_step:
  forall s, models armv6mtypctx s -> list_init_ordinary_lr (s R_LR) ->
  can_step vListInitialise_armv6m_prog
    ((Addr (N.land (s R_LR) 0xfffffffe),s),(Addr 0x54,s)).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are archived in notes/r02-list-init/. *)
Abort.

Theorem list_init_return_witness:
  forall m, m < memsize 32 ->
  exists s:store, models armv6mtypctx s /\ list_init_pre 4096 s /\
    s V_MEM32 = m /\ list_init_ordinary_lr (s R_LR).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are archived in notes/r02-list-init/. *)
Abort.

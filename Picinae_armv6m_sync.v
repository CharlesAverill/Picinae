(* Explicit ARMv6-M SY-barrier sequential projection, NOT hardware semantics.
   DDI 0419E A3.7.3, A6.7.21/22/24, B2.5 distinguish ordering,
   completion and instruction-context synchronization. Picinae's store has
   no external observers, pending accesses, pipeline or exception delivery.
   The view retains barrier kind/length; the named projection erases that
   observation to Nop. No refinement, weak-memory or IRQ claim follows.
   See notes/e20-armv6m-critical/README.md for the exact observation boundary.
   Existing e03/e19 decoders, lifts and acceptance sets remain unchanged. *)
Require Export Picinae_armv6m.
From Stdlib Require Import NArith Bool List.
Open Scope N.

Inductive armv6m_sync_kind := SyncDMB_SY | SyncDSB_SY | SyncISB_SY.

(* Tighten only the NEW profile: all fixed bits and option=SY are required.
   The f3bf first halfword can also belong to BL; preserve that disjoint
   second-halfword class. Reserved options architecturally execute as SY but software must not rely
   on them (A6.7.21/22/24); this frontend deliberately rejects them. *)
Definition armv6m_sync_decode32 (hw1 hw2 : N) : thumb_instr :=
  if (hw1 =? 0xf3bf) && negb (N.land hw2 0xd000 =? 0xd000) then
    if hw2 =? 0x8f4f then T_DSB else
    if hw2 =? 0x8f5f then T_DMB else
    if hw2 =? 0x8f6f then T_ISB else T_Invalid
  else thumb32_decode hw1 hw2.

Definition armv6m_sync_instruction_supported (i : thumb_instr) : bool :=
  match i with
  | T_DMB | T_DSB | T_ISB => true
  | _ => armv6m_mask_instruction_supported i
  end.

Definition armv6m_sync_view := (option armv6m_sync_kind * (N * stmt))%type.
Definition armv6m_sync_program := store -> addr -> option armv6m_sync_view.
Definition armv6m_sync_project (p : armv6m_sync_program) : program :=
  fun s a => match p s a with Some (_, q) => Some q | None => None end.

(* A barrier observation denotes its occurrence at this instruction address,
   never fulfillment of an architectural ordering/completion obligation.
   Non-barrier entries delegate to e19 including dynamic EXC_RETURN guards.
   Actual nesting remains ordinary loads/stores; no abstract counter is added. *)
Definition lift_armv6m_sync_view (binary : addr -> N) : armv6m_sync_program :=
  fun s a =>
  if is_32bit_insn (binary a) then
    match armv6m_sync_decode32 (binary a) (binary ((a+2) mod 2^32)) with
    | T_DMB => Some (Some SyncDMB_SY, (4, Nop))
    | T_DSB => Some (Some SyncDSB_SY, (4, Nop))
    | T_ISB => Some (Some SyncISB_SY, (4, Nop))
    | T_Invalid => None
    | _ => match lift_armv6m_mask binary s a with
           | Some q => Some (None, q) | None => None end
    end
  else match lift_armv6m_mask binary s a with
       | Some q => Some (None, q) | None => None end.

Theorem welltyped_lift_armv6m_sync_projection : forall binary,
  welltyped_prog armv6mtypctx
    (armv6m_sync_project (lift_armv6m_sync_view binary)).
Proof.
  intros binary s a. unfold armv6m_sync_project, lift_armv6m_sync_view.
  pose proof (welltyped_lift_armv6m_mask binary s a) as WT.
  destruct is_32bit_insn.
  - destruct armv6m_sync_decode32;
      try (destruct (lift_armv6m_mask binary s a) as [[n q]|]; exact WT);
      try exact I; eexists; apply TNop; reflexivity.
  - destruct (lift_armv6m_mask binary s a) as [[n q]|]; exact WT.
Qed.

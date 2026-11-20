(* Finite executable instruction regressions, not callee correctness proofs. *)
From Stdlib Require Import Bool.
From Stdlib Require Import NArith List.
Require Import Picinae_armv6m.
Require Import Picinae.tests.armv6m_primask.fixture.
Require Import Picinae.Examples.FreeRTOSMask.ulSetInterruptMask_armv6m.
Require Import Picinae.Examples.FreeRTOSMask.vClearInterruptMask_armv6m.
Open Scope N.

Fixpoint finish (fuel : nat) (base : store) (state : finterp_state) : option (store * option exit) :=
  match state with
  | FIS l (FIExit x) _ => Some (updstr base l vupdate, x)
  | FIS l (FIStmt q) _ =>
      match fuel with
      | O => None
      | S n => finish n base (fexec_stmt noe_setop noe_typop armv6mtypctx q base (fun _ => 0) l)
      end
  end.
Definition run q s := finish 8 s (fexec_stmt noe_setop noe_typop armv6mtypctx q s (fun _ => 0) nil).
Definition observed := V_MEM32 :: R_R0 :: R_R1 :: R_R2 :: R_R3 :: R_R4 :: R_R5 ::
  R_R6 :: R_R7 :: R_R8 :: R_R9 :: R_R10 :: R_R11 :: R_R12 :: R_SP :: R_LR ::
  F_N :: F_Z :: F_C :: F_V :: S_PRIMASK :: S_HANDLER :: S_CONTROL_NPRIV ::
  A_READ :: A_WRITE :: A_EXEC :: V_TEMP 0 :: V_TEMP 1 :: nil.
Definition sample h n p : store := fun v => match v with
  | S_HANDLER => h | S_CONTROL_NPRIV => n | S_PRIMASK => p
  | F_N | F_C => p | F_Z | F_V => 1-p
  | V_MEM32 => 0x12345678 | R_SP => 0x20001000 | R_LR => 0x1001
  | A_READ => 3 | A_WRITE => 5 | A_EXEC => 7
  | _ => 0x87654321 end.
Definition check q s dst expected := match run q s with
  | Some (s', None) => (s' dst =? expected) &&
      forallb (fun v => if Var.eq_dec v dst then true else s' v =? s v) observed
  | _ => false end.
Definition bits := 0 :: 1 :: nil.
Definition gprs := 0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: 11 :: 12 :: 14 :: nil.
Definition values := 0 :: 1 :: 2 :: 3 :: 0xfffffffe :: 0xffffffff :: 0x80000000 :: 0x80000001 :: nil.
Definition privileged h n := (h =? 1) || (n =? 0).
Definition matrix (test : N -> N -> N -> bool) :=
  forallb (fun h => forallb (fun n => forallb (test h n) bits) bits) bits.
Definition is_invalid i := match i with T_Invalid => true | _ => false end.

Example primask_state_widths : map armv6mtypctx
  (S_PRIMASK :: S_HANDLER :: S_CONTROL_NPRIV :: nil) =
  (Some 1 :: Some 1 :: Some 1 :: nil).
Proof. reflexivity. Qed.

Example cps_all_modes_and_frames : matrix (fun h n p =>
  check (arm2il 0 (thumb16_decode 0xb672)) (sample h n p) S_PRIMASK
    (if privileged h n then 1 else p) &&
  check (arm2il 0 (thumb16_decode 0xb662)) (sample h n p) S_PRIMASK
    (if privileged h n then 0 else p)) = true.
Proof. vm_compute. reflexivity. Qed.

Example mrs_all_gprs_modes_and_frames : matrix (fun h n p => forallb (fun r =>
  check (arm2il 0 (thumb32_decode 0xf3ef (0x8010 + 256*r)))
    (sample h n p) (armv6m_varid r) (if privileged h n then p else 0)) gprs) = true.
Proof. vm_compute. reflexivity. Qed.

Example msr_all_gprs_bits_modes_and_frames : matrix (fun h n p => forallb (fun r =>
  forallb (fun x => check (arm2il 0 (thumb32_decode (0xf380+r) 0x8810))
    (update (sample h n p) (armv6m_varid r) x) S_PRIMASK
    (if privileged h n then x mod 2 else p)) values) gprs) = true.
Proof. vm_compute. reflexivity. Qed.

Example assembled_mask_shapes :
  map (fun a => if is_32bit_insn (mask_fixture a)
       then thumb32_decode (mask_fixture a) (mask_fixture (a+2))
       else thumb16_decode (mask_fixture a)) mask_fixture_entries =
  (T_MRS 0 16 :: T_CPSID :: T_MSR 16 0 :: T_CPSIE :: T_MRS 14 16 :: T_MSR 16 14 :: T_BX 14 :: nil).
Proof. vm_compute. reflexivity. Qed.

(* All 256 CPS-region halfwords: only the two exact v6-M encodings decode. *)
Example cps_reserved_bits : forallb (fun k =>
  match thumb16_decode (0xb600 + N.of_nat k) with
  | T_CPSIE => N.of_nat k =? 0x62
  | T_CPSID => N.of_nat k =? 0x72
  | T_Invalid => negb ((N.of_nat k =? 0x62) || (N.of_nat k =? 0x72))
  | _ => false end) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Example mrs_msr_invalid_registers : forallb (fun r =>
  is_invalid (thumb32_decode 0xf3ef (0x8010+256*r)) &&
  is_invalid (thumb32_decode (0xf380+r) 0x8810)) (13 :: 15 :: nil) = true.
Proof. vm_compute. reflexivity. Qed.

Example reserved_sysm : forallb (fun k => let n := N.of_nat k in
  if (n <=? 3) || ((5 <=? n) && (n <=? 9)) || (n =? 16) || (n =? 20) then true else
  is_invalid (thumb32_decode 0xf3ef (0x8000+n)) &&
  is_invalid (thumb32_decode 0xf380 (0x8800+n))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.

Example wrong_fixed_bits : forallb (fun pair => is_invalid (thumb32_decode (fst pair) (snd pair)))
  ((0xf3ff,0x8010) :: (0xf3ee,0x8010) :: (0xf3ef,0xa010) ::
   (0xf390,0x8810) :: (0xf380,0x8910) :: (0xf380,0xa810) :: nil) = true.
Proof. vm_compute. reflexivity. Qed.

Example real_mask_finite_maps :
  ulSetInterruptMask_entries = (0x4090 :: 0x4094 :: 0x4096 :: nil) /\
  vClearInterruptMask_entries = (0x4098 :: 0x409c :: nil) /\
  ulSetInterruptMask_prog (sample 0 1 0) 0x4090 = None /\
  vClearInterruptMask_prog (sample 1 1 0) 0x4098 = None /\
  ulSetInterruptMask_prog (sample 0 0 0) 0x4092 = None /\
  vClearInterruptMask_prog (sample 0 0 0) 0x40a0 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example real_mask_lowering :
  ulSetInterruptMask_prog (sample 0 0 0) 0x4090 = Some (4, arm2il 0x4090 (T_MRS 0 16)) /\
  ulSetInterruptMask_prog (sample 0 0 0) 0x4094 = Some (2, armv6m_write_primask (Word 1 1)) /\
  vClearInterruptMask_prog (sample 0 0 0) 0x4098 = Some (4, arm2il 0x4098 (T_MSR 16 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example exception_return_excluded :
  ulSetInterruptMask_prog (update (sample 1 0 0) R_LR 0xfffffff9) 0x4096 = None /\
  vClearInterruptMask_prog (update (sample 1 0 0) R_LR 0xfffffff1) 0x409c = None /\
  armv6m_mask_target_supported (T_POP 0 true)
    (update (update (sample 1 0 0) R_SP 0) V_MEM32
      (setmem 32 LittleE 4 0 0 0xfffffffd)) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example unsupported_system_boundary :
  forallb armv6m_mask_instruction_supported
    (T_MRS 0 9 :: T_MSR 9 0 :: T_DSB :: T_DMB :: T_ISB :: T_WFI :: nil) = false /\
  map armv6m_mask_instruction_supported
    (T_MRS 0 9 :: T_MSR 9 0 :: T_DSB :: T_DMB :: T_ISB :: T_WFI :: nil) =
    (false :: false :: false :: false :: false :: false :: nil).
Proof. vm_compute. repeat split; reflexivity. Qed.

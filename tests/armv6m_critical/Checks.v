(* Finite decoder/IL fixtures only; r43 owns real function contracts. *)
From Stdlib Require Import NArith Bool List.
Require Import Picinae_armv6m_sync.
Require Import Picinae.tests.armv6m_primask.Checks.
Require Import Picinae.tests.armv6m_critical.fixture.
Require Import Picinae.Examples.FreeRTOSCritical.vPortEnterCritical_armv6m.
Require Import Picinae.Examples.FreeRTOSCritical.vPortExitCritical_armv6m.
Open Scope N.

Example assembled_sync_shapes :
  map (fun a => if is_32bit_insn (sync_fixture a)
    then armv6m_sync_decode32 (sync_fixture a) (sync_fixture (a+2))
    else thumb16_decode (sync_fixture a)) sync_fixture_entries =
  (T_DMB :: T_DSB :: T_ISB :: T_CPSID :: T_CPSIE :: T_BX 14 :: nil).
Proof. vm_compute. reflexivity. Qed.

Example all_barrier_options : forallb (fun k => let n := N.of_nat k in
  if n =? 15 then
    match armv6m_sync_decode32 0xf3bf (0x8f40+n),
          armv6m_sync_decode32 0xf3bf (0x8f50+n),
          armv6m_sync_decode32 0xf3bf (0x8f60+n) with
    | T_DSB, T_DMB, T_ISB => true | _,_,_ => false end
  else is_invalid (armv6m_sync_decode32 0xf3bf (0x8f40+n)) &&
       is_invalid (armv6m_sync_decode32 0xf3bf (0x8f50+n)) &&
       is_invalid (armv6m_sync_decode32 0xf3bf (0x8f60+n))) (seq 0 16) = true.
Proof. vm_compute. reflexivity. Qed.

(* Exhaust every second halfword with this first halfword. *)
Example barrier_fixed_bits : forallb (fun k => let n := N.of_nat k in
  match armv6m_sync_decode32 0xf3bf n with
  | T_DSB => n =? 0x8f4f | T_DMB => n =? 0x8f5f | T_ISB => n =? 0x8f6f
  | T_BL _ => N.land n 0xd000 =? 0xd000
  | T_Invalid => negb ((n =? 0x8f4f) || (n =? 0x8f5f) || (n =? 0x8f6f))
  | _ => false end) (seq 0 65536) = true.
Proof. vm_compute. reflexivity. Qed.

Example separate_barrier_observations :
  sync_fixture_sync_view (sample 0 0 1) 0x1000 = Some (Some SyncDMB_SY, (4,Nop)) /\
  sync_fixture_sync_view (sample 0 0 1) 0x1004 = Some (Some SyncDSB_SY, (4,Nop)) /\
  sync_fixture_sync_view (sample 0 0 1) 0x1008 = Some (Some SyncISB_SY, (4,Nop)) /\
  sync_fixture_sync_view (sample 0 0 1) 0x100c =
    Some (None, (2, armv6m_write_primask (Word 1 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example projected_barriers_preserve_sample_state : matrix (fun h n p =>
  forallb (fun a => match armv6m_sync_project (lift_armv6m_sync_view sync_fixture) (sample h n p) a with
  | Some (4,q) => match run q (sample h n p) with
    | Some (s',None) => forallb (fun v => s' v =? sample h n p v) observed
    | _ => false end
  | _ => false end) (0x1000 :: 0x1004 :: 0x1008 :: nil)) = true.
Proof. vm_compute. reflexivity. Qed.

Example exact_critical_literals_and_views :
  vPortEnterCritical_prog (sample 0 0 0) 0x3e6a =
    Some (2,armv6m_mov 2 (armv6m_word 0x20000000)) /\
  vPortExitCritical_prog (sample 0 0 1) 0x3e82 =
    Some (2,armv6m_mov 3 (armv6m_word 0x20000000)) /\
  vPortEnterCritical_sync_view (sample 0 0 1) 0x3e72 = Some (Some SyncDSB_SY,(4,Nop)) /\
  vPortEnterCritical_sync_view (sample 0 0 1) 0x3e76 = Some (Some SyncISB_SY,(4,Nop)).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example critical_finite_and_profile_guards :
  vPortEnterCritical_prog (sample 0 0 0) 0x3e74 = None /\
  vPortEnterCritical_prog (sample 0 0 0) 0x3e7c = None /\
  vPortExitCritical_prog (sample 0 0 0) 0x3ea4 = None /\
  vPortEnterCritical_prog (sample 0 1 0) 0x3e72 = None /\
  vPortExitCritical_prog (sample 1 1 0) 0x3e98 = None /\
  vPortEnterCritical_prog (update (sample 1 0 1) R_LR 0xfffffff9) 0x3e7a = None /\
  vPortExitCritical_prog
    (update (update (sample 1 0 1) R_SP 0) V_MEM32
      (setmem 32 LittleE 4 0 4 0xfffffffd)) 0x3e9a = None /\
  vPortExitCritical_prog (sample 0 0 1) 0x419c = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Observe the actual branch/CPS instructions in isolation, with explicit flags.
   There is NO inferred relationship between flags and nesting here. *)
Example conditional_cpsie_and_assert_edges :
  (match vPortExitCritical_prog (sample 0 0 0) 0x3e96 with
   | Some (_,q) => match run q (update (sample 0 0 0) F_Z 0) with
     | Some (_,Some (Addr 0x3e9a)) => true | _ => false end | _ => false end) = true /\
  (match vPortExitCritical_prog (sample 0 0 0) 0x3e96 with
   | Some (_,q) => match run q (update (sample 0 0 0) F_Z 1) with
     | Some (_,None) => true | _ => false end | _ => false end) = true /\
  matrix (fun h n p => check (arm2il 0x3e98 (thumb16_decode (vPortExitCritical 0x3e98)))
    (sample h n p) S_PRIMASK (if privileged h n then 0 else p)) = true /\
  (match vPortExitCritical_prog (sample 0 0 0) 0x3ea0 with
   | Some (_,q) => match run q (sample 0 0 0) with
     | Some (s',Some (Addr 0x419c)) => s' R_LR =? 0x3ea5
     | _ => false end | _ => false end) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Real load/store opcode shapes, executed at a small test address to keep the
   dense N memory finite under 2M KiB. This is NOT an execution of the function
   with ulCriticalNesting relocated, nor a general counter/frame theorem. *)
Example memory_opcode_fixtures : forallb (fun x =>
  check (arm2il 0x3e6c (thumb16_decode (vPortEnterCritical 0x3e6c)))
    (update (update (sample 0 0 1) R_R2 0) V_MEM32 x) R_R3 x &&
  check (arm2il 0x3e70 (thumb16_decode (vPortEnterCritical 0x3e70)))
    (update (update (sample 0 0 1) R_R2 0) R_R3 x) V_MEM32 x &&
  check (arm2il 0x3e90 (thumb16_decode (vPortExitCritical 0x3e90)))
    (update (update (sample 0 0 1) R_R3 0) R_R2 x) V_MEM32 x)
  (0 :: 1 :: 2 :: 0xffffffff :: nil) = true.
Proof. vm_compute. reflexivity. Qed.

(* Modular arithmetic observations of the actual opcodes, not bounds claims. *)
Example actual_nesting_arithmetic_samples : forallb (fun x =>
  match run (arm2il 0x3e6e (thumb16_decode (vPortEnterCritical 0x3e6e)))
          (update (sample 0 0 1) R_R3 x),
        run (arm2il 0x3e8e (thumb16_decode (vPortExitCritical 0x3e8e)))
          (update (sample 0 0 1) R_R2 x) with
  | Some (s1,None), Some (s2,None) =>
      (s1 R_R3 =? (x+1) mod 2^32) && (s2 R_R2 =? msub 32 x 1) &&
      (s1 V_MEM32 =? sample 0 0 1 V_MEM32) && (s2 V_MEM32 =? sample 0 0 1 V_MEM32) &&
      (s1 S_PRIMASK =? 1) && (s2 S_PRIMASK =? 1)
  | _,_ => false end) (0 :: 1 :: 2 :: 0xffffffff :: nil) = true.
Proof. vm_compute. reflexivity. Qed.

Example remaining_systems_rejected :
  map armv6m_sync_instruction_supported
   (T_WFI :: T_MRS 0 9 :: T_MSR 9 0 :: T_SVC 0 :: T_DSB :: T_ISB :: T_DMB :: nil) =
   (false :: false :: false :: false :: true :: true :: true :: nil).
Proof. vm_compute. reflexivity. Qed.

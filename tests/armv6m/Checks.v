(* Executable decoder/IL regression cases, not function correctness theorems.
   Bytes independently assembled by GNU as for cortex-m0; check.sh regenerates. *)
From Stdlib Require Import NArith ZArith List.
Require Import Picinae_armv6m.
Require Import Picinae.tests.armv6m.generated.fixture.
Require Import Picinae.tests.armv6m.generated.all_bytes.
Open Scope N.

Example literal_after_function : armv6m_literal fixture_bytes 0x1002 3 = 0x1234abcd.
Proof. vm_compute. reflexivity. Qed.
Example literal_lift : lift_armv6m fixture_bytes (fun _ => 0) 0x1002 =
  Some (2, armv6m_mov 4 (Word 0x1234abcd 32)).
Proof. vm_compute. reflexivity. Qed.
Example finite_program_boundary : fixture_bytes_prog (fun _ => 0) 0x1010 = None /\
  fixture_bytes_prog (fun _ => 0) 0x100c = None /\
  fixture_bytes_prog (fun _ => 0) 0x2000 = None.
Proof. vm_compute. auto. Qed.
Example decode_push : thumb16_decode (fixture_bytes 0x1000) = T_PUSH 16 true.
Proof. vm_compute. reflexivity. Qed.
Example decode_pop : thumb16_decode (fixture_bytes 0x100e) = T_POP 16 true.
Proof. vm_compute. reflexivity. Qed.
Example decode_bl : thumb32_decode (fixture_bytes 0x100a) (fixture_bytes 0x100c) = T_BL 6%Z.
Proof. vm_compute. reflexivity. Qed.
Example decode_bx : thumb16_decode (all_bytes 0x1016) = T_BX 14.
Proof. vm_compute. reflexivity. Qed.
Example invalid_decode : thumb16_decode 0xde00 = T_Invalid /\
  thumb32_decode 0xffff 0xffff = T_Invalid.
Proof. vm_compute. auto. Qed.

(* Evaluate through the existing functional IL interpreter, using its actual
   arithmetic/loads/stores. The runner is test-only and has bounded fuel. Memory
   accessibility predicates are not discharged: these are IL value regressions. *)
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
Definition get_result q s v := match run q s with Some (s', _) => Some (s' v) | _ => None end.
Definition get_exit q s := match run q s with Some (_, x) => x | _ => None end.
Definition regs (r0 r1 c : N) : store := fun v =>
  match v with R_R0 => r0 | R_R1 => r1 | F_C => c | _ => 0 end.
Definition instruction a := snd (armv6m_decode_at all_bytes a).

Example addition_wrap_flags :
  map (get_result (instruction 0x1018) (regs 0xffffffff 1 0))
      (R_R0 :: F_N :: F_Z :: F_C :: F_V :: nil) =
  (Some 0 :: Some 0 :: Some 1 :: Some 1 :: Some 0 :: nil).
Proof. vm_compute. reflexivity. Qed.
Example addition_signed_overflow :
  map (get_result (instruction 0x1018) (regs 0x7fffffff 1 0))
      (R_R0 :: F_N :: F_Z :: F_C :: F_V :: nil) =
  (Some 0x80000000 :: Some 1 :: Some 0 :: Some 0 :: Some 1 :: nil).
Proof. vm_compute. reflexivity. Qed.
Example subtraction_borrow_flags :
  map (get_result (instruction 0x101a) (regs 0 1 0))
      (R_R0 :: F_N :: F_Z :: F_C :: F_V :: nil) =
  (Some 0xffffffff :: Some 1 :: Some 0 :: Some 0 :: Some 0 :: nil).
Proof. vm_compute. reflexivity. Qed.
Example adc_carry_in : get_result (instruction 0x101c) (regs 0xffffffff 0 1) R_R0 = Some 0 /\
  get_result (instruction 0x101c) (regs 0xffffffff 0 1) F_C = Some 1.
Proof. vm_compute. auto. Qed.
Example sbc_borrow_in : get_result (instruction 0x101e) (regs 0 0 0) R_R0 = Some 0xffffffff /\
  get_result (instruction 0x101e) (regs 0 0 0) F_C = Some 0.
Proof. vm_compute. auto. Qed.
Example shift_zero_preserves_carry :
  get_result (instruction 0x1020) (regs 0x80000001 0 1) F_C = Some 1.
Proof. vm_compute. reflexivity. Qed.
Example shift_32_carry :
  get_result (instruction 0x1020) (regs 0x80000001 32 0) F_C = Some 1 /\
  get_result (instruction 0x1022) (regs 0x80000001 32 0) F_C = Some 1 /\
  get_result (instruction 0x1024) (regs 0x80000001 255 0) R_R0 = Some 0xffffffff /\
  get_result (instruction 0x1026) (regs 0x80000001 32 0) R_R0 = Some 0x80000001.
Proof. vm_compute. auto. Qed.
Example forward_bl_link : get_result (instruction 0x100a) (regs 0 0 0) R_LR = Some 0x100f /\
  get_exit (instruction 0x100a) (regs 0 0 0) = Some (Addr 0x1014).
Proof. vm_compute. auto. Qed.
Example backward_bl_link : get_result (instruction 0x1028) (regs 0 0 0) R_LR = Some 0x102d /\
  get_exit (instruction 0x1028) (regs 0 0 0) = Some (Addr 0x1014).
Proof. vm_compute. auto. Qed.
Example bx_thumb_and_fault :
  get_exit (instruction 0x1016) (fun v => match v with R_LR => 0x100f | _ => 0 end) = Some (Addr 0x100e) /\
  get_exit (instruction 0x1016) (fun v => match v with R_LR => 0x100e | _ => 0 end) = Some (Raise 3).
Proof. vm_compute. auto. Qed.
Definition stack_state : store := fun v =>
  match v with R_SP => 32 | R_R4 => 0x12345678 | R_LR => 0x100f | _ => 0 end.
Example push_order : match run (instruction 0x1000) stack_state with
  | Some (s, x) => (s R_SP, getmem 32 LittleE 4 (s V_MEM32) 24,
                   getmem 32 LittleE 4 (s V_MEM32) 28, x)
  | None => (0, 0, 0, Some (Raise 0)) end = (24, 0x12345678, 0x100f, None).
Proof. vm_compute. reflexivity. Qed.
Definition after_push : store := match run (instruction 0x1000) stack_state with Some (s, _) => s | _ => stack_state end.
Example pop_order_return : match run (instruction 0x100e) after_push with
  | Some (s, x) => (s R_SP, s R_R4, x)
  | None => (0, 0, None) end = (32, 0x12345678, Some (Addr 0x100e)).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions welltyped_lift_armv6m.
Print Assumptions welltyped_armv6mprog.
Print Assumptions welltyped_arm2il.
